// ==UserScript==
// @name         贴吧存档助手（TiebaArchiver 浏览器版）
// @namespace    tieba-archiver-browser
// @version      1.5.0
// @description  在贴吧帖子页抓取主题帖、全部楼层与楼中楼，导出为完整 JSON 或用于 AI 分析的 Lite 文本
// @author       tieba-ex
// @match        https://tieba.baidu.com/p/*
// @match        http://tieba.baidu.com/p/*
// @grant        GM_xmlhttpRequest
// @grant        GM_cookie
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        GM_registerMenuCommand
// @grant        GM_addStyle
// @connect      tiebac.baidu.com
// @noframes
// @run-at       document-idle
// ==/UserScript==

/*
 * 用法：
 * 1. 登录 tieba.baidu.com 后打开任意帖子页（/p/<tid>）。
 * 2. 点击顶部导航栏的「导出」按钮（找不到导航栏时会出现在右下角），选择导出格式后点击「开始抓取」，
 *    完成后自动下载所选格式（JSON / Lite 文本）。
 * 3. 大帖可随时「取消」，已抓到的部分仍可下载；「设置」可调整并发与页数上限。
 * 4. 抓取过程中可以关闭面板，导航栏按钮会以进度条形式显示当前进度。
 * 5. Lite 为少 Token 的纯文本，适合 AI 分析。
 *
 * 说明：
 * - 使用与 TiebaArchiver 相同的 protobuf 客户端接口，抓取全部楼层与楼中楼。
 * - 不下载图片/视频/语音/头像，仅在 JSON 中保留原始链接与元数据。
 * - 输出为单个 JSON，结构对应原工具的 threads/<tid>/ 目录（thread.json、forum.json、post 表、user 表）。
 *
 * 1.5.0 更新：
 * - 楼中楼在 JSON 与 Lite 中统一按时间正序（修复：首页内联的楼中楼原为按赞排序，未经重排）。
 * - Lite 1.1：楼中楼增加序号与点赞数；楼主标 [OP]；
 *   表头 floors=存活楼层数(max:最大楼号)，并用 missing= 列出缺失（被删/被吞）的楼号；
 *   抓取失败的页码记入 failed_pages，避免把网络失败误判为被删楼层。
 */

(() => {
    "use strict";

    const APP_VERSION = "browser-1.5.0";
    const APP_HOST = "https://tiebac.baidu.com";
    const BOUNDARY = "-*_r1999";
    const PAGE_CMD = 302001;
    const FLOOR_CMD = 302002;
    const PAGE_CLIENT_VERSION = "12.64.1.1";
    const FLOOR_CLIENT_VERSION = "22.12.1.0";
    const PAGE_SIZE = 30;
    const INLINE_COMMENT_SIZE = 4;

    const FRAGMENT_TYPE = {
        TEXT: 1,
        EMOJI: 2,
        IMAGE: 3,
        AT: 4,
        LINK: 5,
        TIEBAPLUS: 6,
        VIDEO: 7,
        VOICE: 8,
        SCRAPE_ERROR: -1,
    };

    const THREAD_TYPE_HELP = 71;

    class CancelledError extends Error {
        constructor() {
            super("已取消");
            this.name = "CancelledError";
        }
    }

    const sleep = (ms) => new Promise((resolve) => setTimeout(resolve, ms));

    function isCancelled(error) {
        return error instanceof CancelledError;
    }

    // ---------------------------------------------------------------------------
    // 字节工具 / Protobuf 编解码
    // ---------------------------------------------------------------------------

    const textEncoder = new TextEncoder();
    const textDecoder = new TextDecoder("utf-8");

    function utf8Encode(text) {
        return textEncoder.encode(text);
    }

    function utf8Decode(bytes) {
        return textDecoder.decode(bytes);
    }

    function readVarint(bytes, offset) {
        let value = 0n;
        let shift = 0n;
        for (; ;) {
            if (offset >= bytes.length) {
                throw new Error("protobuf: varint 被截断");
            }
            const byte = bytes[offset++];
            value |= BigInt(byte & 0x7f) << shift;
            if ((byte & 0x80) === 0) {
                return [value, offset];
            }
            shift += 7n;
            if (shift > 63n) {
                throw new Error("protobuf: varint 过长");
            }
        }
    }

    function varintBytes(value) {
        let current = BigInt(value);
        const out = [];
        if (current < 0n) {
            throw new Error("protobuf: 不支持负数");
        }
        while (current > 0x7fn) {
            out.push(Number(current & 0x7fn) | 0x80);
            current >>= 7n;
        }
        out.push(Number(current));
        return out;
    }

    function concatBytes(parts) {
        let length = 0;
        for (const part of parts) {
            length += part.length;
        }
        const out = new Uint8Array(length);
        let offset = 0;
        for (const part of parts) {
            out.set(part, offset);
            offset += part.length;
        }
        return out;
    }

    class ProtoWriter {
        constructor() {
            this.parts = [];
        }

        tag(field, wire) {
            this.parts.push(new Uint8Array(varintBytes(BigInt(field) * 8n + BigInt(wire))));
        }

        int(field, value, keepZero = false) {
            const number = Number(value) || 0;
            if (!number && !keepZero) {
                return this;
            }
            this.tag(field, 0);
            this.parts.push(new Uint8Array(varintBytes(number)));
            return this;
        }

        string(field, value) {
            if (!value) {
                return this;
            }
            const bytes = utf8Encode(String(value));
            this.tag(field, 2);
            this.parts.push(new Uint8Array(varintBytes(bytes.length)));
            this.parts.push(bytes);
            return this;
        }

        message(field, writer) {
            const bytes = writer.bytes();
            this.tag(field, 2);
            this.parts.push(new Uint8Array(varintBytes(bytes.length)));
            this.parts.push(bytes);
            return this;
        }

        bytes() {
            return concatBytes(this.parts);
        }
    }

    function decodeFields(bytes) {
        const fields = Object.create(null);
        let offset = 0;
        while (offset < bytes.length) {
            const [key, nextOffset] = readVarint(bytes, offset);
            offset = nextOffset;
            const fieldNo = Number(key >> 3n);
            const wireType = Number(key & 7n);

            let value;
            if (wireType === 0) {
                const [varint, after] = readVarint(bytes, offset);
                offset = after;
                value = Number(varint);
            } else if (wireType === 2) {
                const [length, after] = readVarint(bytes, offset);
                offset = after;
                const size = Number(length);
                value = bytes.subarray(offset, offset + size);
                offset += size;
            } else if (wireType === 1) {
                value = bytes.subarray(offset, offset + 8);
                offset += 8;
            } else if (wireType === 5) {
                value = bytes.subarray(offset, offset + 4);
                offset += 4;
            } else {
                throw new Error(`protobuf: 不支持的 wire type ${wireType}`);
            }

            (fields[fieldNo] || (fields[fieldNo] = [])).push(value);
        }
        return fields;
    }

    function first(fields, fieldNo) {
        if (!fields) {
            return undefined;
        }
        const values = fields[fieldNo];
        return values && values.length ? values[0] : undefined;
    }

    function getInt(fields, fieldNo, fallback = 0) {
        const value = first(fields, fieldNo);
        return value === undefined ? fallback : Number(value);
    }

    function getString(fields, fieldNo, fallback = "") {
        const value = first(fields, fieldNo);
        return value === undefined ? fallback : utf8Decode(value);
    }

    function getMessage(fields, fieldNo) {
        const value = first(fields, fieldNo);
        return value === undefined ? null : decodeFields(value);
    }

    function getMessages(fields, fieldNo) {
        if (!fields || !fields[fieldNo]) {
            return [];
        }
        return fields[fieldNo].map((bytes) => decodeFields(bytes));
    }

    function makeCommon(clientVersion, bduss) {
        const common = new ProtoWriter();
        common.int(1, 2, true); // _client_type
        common.string(2, clientVersion); // _client_version
        if (bduss) {
            common.string(10, bduss); // BDUSS
        }
        return common;
    }

    function encodePageRequest(tid, pn, bduss) {
        const data = new ProtoWriter();
        data.message(25, makeCommon(PAGE_CLIENT_VERSION, bduss));
        data.int(4, tid); // kz
        data.int(5, 0); // lz 只看楼主
        data.int(6, 0); // r 排序: 时间正序
        data.int(13, PAGE_SIZE); // rn
        data.int(18, pn); // pn
        data.int(8, 1); // with_floor
        data.int(9, INLINE_COMMENT_SIZE); // floor_rn
        data.int(74, 1); // floor_sort_type: 按赞排序

        const root = new ProtoWriter();
        root.message(1, data);
        return root.bytes();
    }

    function encodeFloorRequest(tid, pid, pn) {
        const data = new ProtoWriter();
        data.message(9, makeCommon(FLOOR_CLIENT_VERSION, null));
        data.int(1, tid); // kz
        data.int(2, pid); // pid
        data.int(4, pn); // pn
        data.int(19, 0); // sort: 时间正序

        const root = new ProtoWriter();
        root.message(1, data);
        return root.bytes();
    }

    function decodeError(fields) {
        if (!fields) {
            return { errorno: 0, errmsg: "" };
        }
        return {
            errorno: getInt(fields, 1),
            errmsg: getString(fields, 2),
        };
    }

    function decodePage(fields) {
        if (!fields) {
            return null;
        }
        return {
            pageSize: getInt(fields, 1),
            currentPage: getInt(fields, 3),
            totalCount: getInt(fields, 4),
            totalPage: getInt(fields, 5),
            hasMore: getInt(fields, 6) !== 0,
            hasPrev: getInt(fields, 7) !== 0,
        };
    }

    function decodeForum(fields) {
        if (!fields) {
            return null;
        }
        return {
            id: getInt(fields, 1),
            name: getString(fields, 2),
            firstClass: getString(fields, 7),
            secondClass: getString(fields, 8),
            memberNum: getInt(fields, 12),
            postNum: getInt(fields, 13),
        };
    }

    function decodeAgree(fields) {
        if (!fields) {
            return { agreeNum: 0, disagreeNum: 0 };
        }
        return {
            agreeNum: getInt(fields, 1),
            disagreeNum: getInt(fields, 4),
        };
    }

    function decodePoll(fields) {
        const empty = {
            title: "",
            isMulti: false,
            totalVote: 0,
            totalUser: 0,
            options: [],
        };
        if (!fields) {
            return empty;
        }
        return {
            title: getString(fields, 12),
            isMulti: getInt(fields, 2) !== 0,
            totalVote: getInt(fields, 11),
            totalUser: getInt(fields, 3),
            options: getMessages(fields, 9).map((option) => ({
                voteNum: getInt(option, 2),
                text: getString(option, 3),
            })),
        };
    }

    function decodeIcon(fields) {
        return getString(fields, 1);
    }

    function decodeUserGrowth(fields) {
        return fields ? getInt(fields, 1) : 0;
    }

    function decodeUser(fields) {
        if (!fields) {
            return null;
        }
        let portrait = getString(fields, 5);
        if (portrait.includes("?")) {
            portrait = portrait.split("?")[0];
        }
        return {
            id: getInt(fields, 2),
            name: getString(fields, 3),
            nameShow: getString(fields, 4),
            portrait,
            icons: getMessages(fields, 17).map(decodeIcon).filter(Boolean),
            isCoreUser: getInt(fields, 20) !== 0,
            level: getInt(fields, 23),
            isBawu: getInt(fields, 25) !== 0,
            fansNum: getInt(fields, 30),
            concernNum: getInt(fields, 31),
            sex: getInt(fields, 32),
            postNum: getInt(fields, 37),
            isMem: getInt(fields, 39) !== 0,
            gender: getInt(fields, 42),
            tyUid: Number(getString(fields, 120)) || 0,
            ip: getString(fields, 127),
            growthLevel: decodeUserGrowth(getMessage(fields, 137)),
        };
    }

    function decodeContent(fields) {
        return {
            type: getInt(fields, 1),
            text: getString(fields, 2),
            link: getString(fields, 3),
            src: getString(fields, 4),
            bsize: getString(fields, 5),
            cdnSrc: getString(fields, 8),
            bigCdnSrc: getString(fields, 9),
            c: getString(fields, 11),
            voiceMd5: getString(fields, 12),
            duringTime: getInt(fields, 13),
            uid: getInt(fields, 15),
            width: getInt(fields, 18),
            height: getInt(fields, 19),
            originSrc: getString(fields, 25),
            originSize: getInt(fields, 27),
            count: getInt(fields, 28),
            portrait: getString(fields, 49),
            tiebaplus: decodeTiebaPlus(getMessage(fields, 40)),
        };
    }

    function decodeTiebaPlus(fields) {
        if (!fields) {
            return null;
        }
        return {
            title: getString(fields, 1),
            desc: getString(fields, 2),
            jumpUrl: getString(fields, 3),
        };
    }

    function decodeSignature(fields) {
        if (!fields) {
            return "";
        }
        return getMessages(fields, 4)
            .filter((item) => getInt(item, 1) === 0)
            .map((item) => getString(item, 2))
            .join("");
    }

    function decodeSubPost(fields) {
        return {
            id: getInt(fields, 1),
            contents: getMessages(fields, 2).map(decodeContent),
            time: getInt(fields, 3),
            authorId: getInt(fields, 4),
            title: getString(fields, 5),
            floor: getInt(fields, 6),
            author: decodeUser(getMessage(fields, 7)),
            agree: decodeAgree(getMessage(fields, 9)),
        };
    }

    function decodePost(fields) {
        const chat = getMessage(fields, 78);
        const botUk = chat ? getString(chat, 1) : "";
        return {
            id: getInt(fields, 1),
            floor: getInt(fields, 3),
            time: getInt(fields, 4),
            contents: getMessages(fields, 5).map(decodeContent),
            subPostNumber: getInt(fields, 13),
            authorId: getInt(fields, 19),
            inlineComments: getMessages(getMessage(fields, 15) || Object.create(null), 2).map(decodeSubPost),
            signature: decodeSignature(getMessage(fields, 21)),
            author: decodeUser(getMessage(fields, 23)),
            agree: decodeAgree(getMessage(fields, 37)),
            tid: getInt(fields, 46),
            isBotChat: botUk !== "",
        };
    }

    function decodeOriginThread(fields) {
        if (!fields) {
            return null;
        }
        return {
            title: getString(fields, 1),
            fname: getString(fields, 4),
            tid: Number(getString(fields, 5)) || 0,
            fid: getInt(fields, 7),
            isDeleted: getInt(fields, 9) !== 0,
            author: decodeUser(getMessage(fields, 18)),
        };
    }

    function decodeThread(fields) {
        if (!fields) {
            return null;
        }
        const author = decodeUser(getMessage(fields, 18));
        return {
            id: getInt(fields, 1),
            title: getString(fields, 3),
            replyNum: getInt(fields, 4),
            viewNum: getInt(fields, 5),
            author,
            authorId: author ? author.id : getInt(fields, 56),
            threadType: getInt(fields, 26),
            fid: getInt(fields, 27),
            fname: getString(fields, 28),
            firstPostId: getInt(fields, 40),
            createTime: getInt(fields, 45),
            postId: getInt(fields, 52),
            validPostNum: getInt(fields, 57),
            poll: decodePoll(getMessage(fields, 74)),
            agree: decodeAgree(getMessage(fields, 126)),
            shareNum: getInt(fields, 135),
            originThread: decodeOriginThread(getMessage(fields, 141)),
            isShare: getInt(fields, 143) !== 0,
            collectNum: getInt(fields, 190),
            isDeleted: getInt(fields, 181) !== 0,
        };
    }

    function decodePageResponse(bytes) {
        const root = decodeFields(bytes);
        const error = decodeError(getMessage(root, 1));
        if (error.errorno) {
            return { error, page: null, forum: null, thread: null, users: [], posts: [], threadFreqNum: 0 };
        }

        const data = getMessage(root, 2);
        if (!data) {
            return { error: null, page: null, forum: null, thread: null, users: [], posts: [], threadFreqNum: 0 };
        }

        const threadFreqNum = getInt(data, 37);
        const thread = decodeThread(getMessage(data, 8));
        if (thread) {
            thread.viewNum = threadFreqNum;
        }

        return {
            error: null,
            page: decodePage(getMessage(data, 3)),
            forum: decodeForum(getMessage(data, 2)),
            thread,
            users: getMessages(data, 13).map(decodeUser).filter(Boolean),
            posts: getMessages(data, 6).map(decodePost),
            threadFreqNum,
        };
    }

    function decodeFloorResponse(bytes) {
        const root = decodeFields(bytes);
        const error = decodeError(getMessage(root, 1));
        if (error.errorno) {
            return { error, page: null, thread: null, forum: null, post: null, comments: [] };
        }

        const data = getMessage(root, 2);
        if (!data) {
            return { error: null, page: null, thread: null, forum: null, post: null, comments: [] };
        }

        return {
            error: null,
            page: decodePage(getMessage(data, 1)),
            post: decodePost(getMessage(data, 3)),
            thread: decodeThread(getMessage(data, 5)),
            forum: decodeForum(getMessage(data, 6)),
            comments: getMessages(data, 4).map(decodeSubPost),
        };
    }

    // ---------------------------------------------------------------------------
    // 内容碎片 / 数据转换
    // ---------------------------------------------------------------------------

    function percentEncode(value) {
        return encodeURIComponent(value).replace(/[!'()*]/g, (char) =>
            "%" + char.charCodeAt(0).toString(16).toUpperCase(),
        );
    }

    function imageHash(url) {
        const matched = /\/[a-z0-9]{32,}\./.exec(url || "");
        return matched ? matched[0].slice(1, -1) : "";
    }

    function bsizeSize(bsize) {
        if (!bsize || !bsize.includes(",")) {
            return null;
        }
        const [width, height] = bsize.split(",");
        return { width: Number(width) || 0, height: Number(height) || 0 };
    }

    function extractExternalUrl(rawUrl) {
        try {
            const url = new URL(rawUrl, "https://tieba.baidu.com");
            if (url.hostname === "tieba.baidu.com" && url.pathname === "/mo/q/checkurl") {
                return url.searchParams.get("url");
            }
            return rawUrl;
        } catch (error) {
            return null;
        }
    }

    function extractCustomEmoticonUrl(rawUrl) {
        try {
            const url = new URL(rawUrl, "https://tieba.baidu.com");
            if (url.hostname === "c.tieba.baidu.com" && url.pathname === "/c/p/img") {
                return url.searchParams.get("src") || rawUrl;
            }
        } catch (error) {
            // ignore
        }
        return rawUrl;
    }

    function voiceUrl(md5) {
        return `https://tiebac.baidu.com/c/p/voice?voice_md5=${md5}&play_from=pb_voice_play`;
    }

    function contentToFragment(content) {
        const type = content.type;
        switch (type) {
            case 0:
            case 9:
            case 18:
            case 27:
            case 40:
                return { type: FRAGMENT_TYPE.TEXT, text: content.text };

            case 2:
            case 11:
                return { type: FRAGMENT_TYPE.EMOJI, id: content.text, desc: content.c };

            case 3:
            case 20: {
                const size = bsizeSize(content.bsize) || {
                    width: content.width,
                    height: content.height,
                };
                return {
                    type: FRAGMENT_TYPE.IMAGE,
                    filename: "",
                    tb_origin_src: content.originSrc || extractCustomEmoticonUrl(content.cdnSrc),
                    origin_size: content.originSize,
                    show_width: size.width,
                    show_height: size.height,
                    hash: imageHash(content.cdnSrc),
                };
            }

            case 4:
                return { type: FRAGMENT_TYPE.AT, text: content.text, user_id: content.uid };

            case 1: {
                const rawUrl = extractExternalUrl(content.link);
                if (!rawUrl) {
                    return {
                        type: FRAGMENT_TYPE.SCRAPE_ERROR,
                        error_frag_type: FRAGMENT_TYPE.LINK,
                        error_frag_name: "link",
                    };
                }
                return {
                    type: FRAGMENT_TYPE.LINK,
                    text: percentEncode(rawUrl),
                    title: content.text,
                    raw_url: rawUrl,
                };
            }

            case 10:
                return {
                    type: FRAGMENT_TYPE.VOICE,
                    filename: "",
                    md5: content.voiceMd5,
                    duration: (content.duringTime || 0) / 1000,
                    tb_origin_src: voiceUrl(content.voiceMd5),
                };

            case 5:
                return {
                    type: FRAGMENT_TYPE.VIDEO,
                    filename: "",
                    cover_filename: "",
                    duration: content.duringTime,
                    width: content.width,
                    height: content.height,
                    view_num: content.count,
                    tb_origin_src: content.link,
                    tb_origin_cover_src: content.src,
                };

            case 35:
            case 36:
            case 37:
                return {
                    type: FRAGMENT_TYPE.TIEBAPLUS,
                    text: content.tiebaplus ? content.tiebaplus.desc : "",
                    url: content.tiebaplus ? content.tiebaplus.jumpUrl : "",
                };

            case 34:
            case 52:
                return null;

            default:
                return content.text ? { type: FRAGMENT_TYPE.TEXT, text: content.text } : null;
        }
    }

    function convertContents(contents) {
        const fragments = [];
        for (const content of contents) {
            const fragment = contentToFragment(content);
            if (fragment) {
                fragments.push(fragment);
            }
        }
        return fragments;
    }

    function convertCommentContents(comment) {
        const fragments = convertContents(comment.contents);
        let replyToId = 0;

        if (fragments.length > 0) {
            const firstFragment = fragments[0];
            if (
                firstFragment.type === FRAGMENT_TYPE.TEXT &&
                firstFragment.text === "回复 " &&
                comment.contents[1]
            ) {
                replyToId = comment.contents[1].uid || 0;
                if (replyToId) {
                    fragments.splice(0, 2);
                    if (fragments.length && fragments[0].type === FRAGMENT_TYPE.TEXT) {
                        fragments[0].text = fragments[0].text.replace(/^ :/, "");
                    }
                }
            }
        }

        return { fragments, replyToId };
    }

    function makeUserRow(user, scrapeTime) {
        if (!user || !user.id) {
            return null;
        }
        return {
            id: user.id,
            portrait: user.portrait || null,
            username: user.name || null,
            nickname: user.nameShow || "",
            tieba_uid: user.tyUid || null,
            avatar: null,
            glevel: user.growthLevel || 0,
            gender: user.gender || 0,
            ip: user.ip || "",
            is_vip: !!user.isMem,
            is_god: false,
            age: 0,
            sign: "",
            post_num: user.postNum || 0,
            agree_num: 0,
            fan_num: user.fansNum || 0,
            follow_num: user.concernNum || 0,
            forum_num: 0,
            level: user.level || 0,
            is_bawu: !!user.isBawu,
            status: 0,
            completed: 0,
            scrape_time: scrapeTime,
        };
    }

    function mergeUserRow(target, incoming) {
        if (!target) {
            return incoming;
        }
        for (const key of ["portrait", "username", "nickname", "tieba_uid"]) {
            if ((target[key] === null || target[key] === "" || target[key] === 0) && incoming[key]) {
                target[key] = incoming[key];
            }
        }
        for (const key of [
            "glevel",
            "gender",
            "ip",
            "post_num",
            "fan_num",
            "follow_num",
            "level",
            "is_vip",
            "is_bawu",
        ]) {
            if (!target[key] && incoming[key]) {
                target[key] = incoming[key];
            }
        }
        return target;
    }

    function normalizeForum(forum) {
        return {
            id: forum ? forum.id : 0,
            name: forum ? forum.name : "",
            category: forum ? forum.firstClass : "",
            subcategory: forum ? forum.secondClass : "",
            member_num: forum ? forum.memberNum : 0,
            post_num: forum ? forum.postNum : 0,
            thread_num: 0,
            slogan: "",
            small_avatar: "",
            origin_avatar: "",
        };
    }

    function normalizeThread(thread, forum, defaultTid) {
        const poll = thread.poll || {
            title: "",
            isMulti: false,
            totalVote: 0,
            totalUser: 0,
            options: [],
        };
        return {
            id: thread.id || defaultTid,
            title: thread.title,
            forum_id: forum ? forum.id : thread.fid,
            forum_name: forum ? forum.name : thread.fname,
            post_id: thread.postId || thread.firstPostId,
            user_id: thread.authorId,
            type: thread.threadType,
            is_share: !!thread.isShare,
            is_help: thread.threadType === THREAD_TYPE_HELP,
            vote_info: {
                title: poll.title,
                is_multi: poll.isMulti,
                total_vote: poll.totalVote,
                total_user: poll.totalUser,
                options: poll.options.map((option) => ({
                    text: option.text,
                    vote_num: option.voteNum,
                })),
            },
            share_origin: thread.isShare && thread.originThread ? thread.originThread.tid : 0,
            view_num: thread.viewNum || 0,
            reply_num: thread.replyNum,
            share_num: thread.shareNum,
            agree: thread.agree.agreeNum,
            disagree: thread.agree.disagreeNum,
            create_time: thread.createTime,
            status: 0,
        };
    }

    function normalizePost(post, threadAuthorId, userMap) {
        return {
            id: post.id,
            contents: convertContents(post.contents),
            floor: post.floor,
            user_id: post.authorId,
            agree: post.agree.agreeNum,
            disagree: post.agree.disagreeNum,
            create_time: post.time,
            is_thread_author: post.authorId === threadAuthorId,
            sign: post.signature,
            reply_num: post.subPostNumber,
            parent_id: 0,
            reply_to_id: 0,
            user: userMap.get(post.authorId) || null,
            comments: [],
            _inline: post.inlineComments || [],
        };
    }

    function normalizeComment(comment, parentPost, threadAuthorId, userMap) {
        const converted = convertCommentContents(comment);
        const authorId = comment.author ? comment.author.id : comment.authorId;
        return {
            id: comment.id,
            contents: converted.fragments,
            floor: parentPost.floor,
            user_id: authorId,
            agree: comment.agree.agreeNum,
            disagree: comment.agree.disagreeNum,
            create_time: comment.time,
            is_thread_author: authorId === threadAuthorId,
            sign: "",
            reply_num: 0,
            parent_id: parentPost.id,
            reply_to_id: converted.replyToId,
            user: userMap.get(authorId) || null,
        };
    }

    // 楼中楼统一按时间正序（时间相同则按 id），避免按赞/热度排序造成时间线错乱
    function compareByTime(a, b) {
        return (a.create_time || 0) - (b.create_time || 0) || (a.id || 0) - (b.id || 0);
    }

    function sortCommentsAsc(list) {
        return list.sort(compareByTime);
    }

    // 首页内联的楼中楼是按赞排序的：转换后必须重新按时间排序
    function inlineToComments(post) {
        return sortCommentsAsc(
            (post._inline || []).map((comment) =>
                normalizeComment(comment, post, scraper.thread.authorId, scraper.users),
            ),
        );
    }

    // ---------------------------------------------------------------------------
    // 网络
    // ---------------------------------------------------------------------------

    function buildMultipartBytes(bodyBytes) {
        const head = utf8Encode(
            `--${BOUNDARY}\r\nContent-Disposition: form-data; name="data"; filename="file"\r\n\r\n`,
        );
        const tail = utf8Encode(`\r\n--${BOUNDARY}--\r\n`);
        return concatBytes([head, bodyBytes, tail]);
    }

    function buildMultipartBlob(bodyBytes) {
        return new Blob([buildMultipartBytes(bodyBytes)], {
            type: `multipart/form-data; boundary=${BOUNDARY}`,
        });
    }

    const activeRequests = new Set();

    function abortActiveRequests() {
        for (const handle of activeRequests) {
            try {
                handle.abort();
            } catch (error) {
                // ignore
            }
        }
        activeRequests.clear();
    }

    function gmPostProto(url, bodyBytes) {
        return new Promise((resolve, reject) => {
            if (typeof GM_xmlhttpRequest !== "function") {
                reject(new Error("GM_xmlhttpRequest 不可用，请检查脚本权限"));
                return;
            }

            const handle = GM_xmlhttpRequest({
                method: "POST",
                url,
                headers: {
                    "Content-Type": `multipart/form-data; boundary=${BOUNDARY}`,
                    "x_bd_data_type": "protobuf",
                },
                data: buildMultipartBlob(bodyBytes),
                responseType: "arraybuffer",
                timeout: 30000,
                onload(response) {
                    activeRequests.delete(handle);
                    if (response.status !== 200) {
                        reject(new Error(`HTTP ${response.status}`));
                        return;
                    }
                    const body = response.response;
                    if (!body) {
                        reject(new Error("响应为空"));
                        return;
                    }
                    if (typeof Blob !== "undefined" && body instanceof Blob) {
                        body.arrayBuffer().then((buffer) => resolve(new Uint8Array(buffer))).catch(reject);
                        return;
                    }
                    resolve(
                        body instanceof ArrayBuffer
                            ? new Uint8Array(body)
                            : new Uint8Array(body.buffer || body),
                    );
                },
                onerror() {
                    activeRequests.delete(handle);
                    reject(new Error("网络错误"));
                },
                ontimeout() {
                    activeRequests.delete(handle);
                    reject(new Error("请求超时"));
                },
                onabort() {
                    activeRequests.delete(handle);
                    reject(new CancelledError());
                },
            });

            activeRequests.add(handle);
        });
    }

    function safeDecode(value) {
        try {
            return decodeURIComponent(value);
        } catch (error) {
            return value;
        }
    }

    async function getBduss() {
        const matched = document.cookie.match(/(?:^|; )BDUSS=([^;]+)/);
        if (matched) {
            return safeDecode(matched[1]);
        }

        if (typeof GM_cookie === "undefined" || typeof GM_cookie.list !== "function") {
            return null;
        }

        const cookies = await Promise.race([
            new Promise((resolve) => {
                try {
                    GM_cookie.list({ domain: ".baidu.com", name: "BDUSS" }, (list) => resolve(list || []));
                } catch (error) {
                    resolve([]);
                }
            }),
            sleep(2000).then(() => []),
        ]);

        if (!cookies.length) {
            return null;
        }
        return safeDecode(cookies[0].value);
    }

    function assertProtobuf(bytes) {
        if (!bytes || bytes.length === 0) {
            throw new Error("响应为空");
        }
        if (bytes[0] === 0x7b) {
            let detail = "";
            try {
                const payload = JSON.parse(utf8Decode(bytes));
                detail = [payload.error_code, payload.error_msg].filter(Boolean).join(": ");
            } catch (error) {
                // ignore
            }
            throw new Error(`接口返回错误${detail ? `（${detail}）` : ""}`);
        }
    }

    async function requestWithRetry(factory, label, attempts = 3) {
        let lastError = null;
        for (let attempt = 1; attempt <= attempts; attempt += 1) {
            if (scraper.cancelled) {
                throw new CancelledError();
            }
            try {
                return await factory();
            } catch (error) {
                if (isCancelled(error)) {
                    throw error;
                }
                lastError = error;
                if (attempt < attempts) {
                    log(`${label} 失败（第 ${attempt} 次）：${error.message}，重试中`, "warn");
                    await sleep(500 * 2 ** (attempt - 1));
                }
            }
        }
        throw lastError;
    }

    async function fetchPostsPage(tid, pn) {
        const body = encodePageRequest(tid, pn, scraper.bduss);
        const bytes = await requestWithRetry(
            () => gmPostProto(`${APP_HOST}/c/f/pb/page?cmd=${PAGE_CMD}`, body),
            `第 ${pn} 页`,
        );
        assertProtobuf(bytes);
        const result = decodePageResponse(bytes);
        if (result.error) {
            throw new Error(`接口错误 ${result.error.errorno}: ${result.error.errmsg}`);
        }
        if (!result.thread || result.thread.id === 0) {
            throw new Error("响应中没有主题帖信息");
        }
        return result;
    }

    async function fetchCommentsPage(tid, pid, pn) {
        const body = encodeFloorRequest(tid, pid, pn);
        const bytes = await requestWithRetry(
            () => gmPostProto(`${APP_HOST}/c/f/pb/floor?cmd=${FLOOR_CMD}`, body),
            `楼中楼 ${pid} 第 ${pn} 页`,
        );
        assertProtobuf(bytes);
        const result = decodeFloorResponse(bytes);
        if (result.error) {
            throw new Error(`接口错误 ${result.error.errorno}: ${result.error.errmsg}`);
        }
        return result;
    }

    // ---------------------------------------------------------------------------
    // 抓取流程
    // ---------------------------------------------------------------------------

    const scraper = {
        running: false,
        cancelled: false,
        phase: "idle",
        stage: 0, // 0 未开始 / 1 楼层 / 2 楼中楼
        tid: 0,
        bduss: null,
        scrapeTime: 0,
        startedAt: 0,
        finishedAt: 0,
        concurrency: 3,
        pageLimit: 0,
        exportFormat: "full",
        page: { done: 0, total: 0 },
        comment: { done: 0, total: 0 },
        posts: new Map(),
        users: new Map(),
        forum: null,
        thread: null,
        errors: [],
        failedPages: [],
        fatal: "",
        result: null,
        lastExport: null,
        logs: [],
    };

    function log(message, level = "info") {
        scraper.logs.push({ message, level, at: Date.now() });
        if (scraper.logs.length > 30) {
            scraper.logs.shift();
        }
        renderPanel();
    }

    function recordError(message) {
        scraper.errors.push(message);
        if (scraper.errors.length > 200) {
            scraper.errors.shift();
        }
    }

    function isThreadVisible(thread) {
        return thread && thread.id > 0;
    }

    function absorbPageResponse(response, isPrimary) {
        if (response.forum && isPrimary) {
            scraper.forum = response.forum;
        }
        if (response.thread && isPrimary) {
            scraper.thread = response.thread;
            scraper.tid = response.thread.id;
        }

        for (const user of response.users) {
            if (!user || !user.id) {
                continue;
            }
            const row = makeUserRow(user, scraper.scrapeTime);
            scraper.users.set(user.id, mergeUserRow(scraper.users.get(user.id), row));
        }

        const threadAuthorId = scraper.thread ? scraper.thread.authorId : 0;
        if (scraper.thread && scraper.thread.author) {
            const row = makeUserRow(scraper.thread.author, scraper.scrapeTime);
            if (row) {
                scraper.users.set(row.id, mergeUserRow(scraper.users.get(row.id), row));
            }
        }
        for (const post of response.posts) {
            if (!post.id || post.id <= 0 || post.isBotChat) {
                continue;
            }
            const record = normalizePost(post, threadAuthorId, scraper.users);
            const authorRow = makeUserRow(post.author, scraper.scrapeTime);
            if (authorRow) {
                record.user = mergeUserRow(scraper.users.get(authorRow.id), authorRow);
                scraper.users.set(authorRow.id, record.user);
            }
            for (const comment of post.inlineComments) {
                const row = makeUserRow(comment.author, scraper.scrapeTime);
                if (row) {
                    scraper.users.set(row.id, mergeUserRow(scraper.users.get(row.id), row));
                }
            }
            for (const fragment of record.contents) {
                if (fragment.type === FRAGMENT_TYPE.AT && fragment.user_id) {
                    const row = makeUserRow(
                        { id: fragment.user_id, nameShow: fragment.text },
                        scraper.scrapeTime,
                    );
                    if (row) {
                        scraper.users.set(row.id, mergeUserRow(scraper.users.get(row.id), row));
                    }
                }
            }
            scraper.posts.set(post.id, record);
        }
    }

    async function mapLimit(items, limit, worker) {
        let index = 0;
        const runners = [];
        const size = Math.min(Math.max(limit, 1), items.length);
        for (let i = 0; i < size; i += 1) {
            runners.push((async () => {
                for (; ;) {
                    if (scraper.cancelled) {
                        return;
                    }
                    const current = index;
                    index += 1;
                    if (current >= items.length) {
                        return;
                    }
                    await worker(items[current], current);
                }
            })());
        }
        await Promise.all(runners);
    }

    async function scrapeFloors(pages) {
        await mapLimit(pages, scraper.concurrency, async (pn) => {
            try {
                const response = await fetchPostsPage(scraper.tid, pn);
                absorbPageResponse(response);
            } catch (error) {
                if (isCancelled(error)) {
                    throw error;
                }
                scraper.failedPages.push(pn);
                recordError(`第 ${pn} 页：${error.message}`);
                log(`第 ${pn} 页抓取失败：${error.message}`, "error");
            } finally {
                if (!scraper.cancelled) {
                    scraper.page.done += 1;
                }
                renderPanel();
            }
        });
    }

    async function fetchAllComments(post) {
        let pn = 1;
        let totalPage = 1;
        const collected = [];
        const seen = new Set();

        while (pn <= totalPage && pn <= 500) {
            if (scraper.cancelled) {
                throw new CancelledError();
            }
            const response = await fetchCommentsPage(scraper.tid, post.id, pn);
            if (response.page) {
                totalPage = Math.max(totalPage, response.page.totalPage || 1);
            }
            for (const comment of response.comments) {
                if (!comment.id || seen.has(comment.id)) {
                    continue;
                }
                seen.add(comment.id);
                const row = makeUserRow(comment.author, scraper.scrapeTime);
                if (row) {
                    scraper.users.set(row.id, mergeUserRow(scraper.users.get(row.id), row));
                }
                const record = normalizeComment(
                    comment,
                    post,
                    scraper.thread.authorId,
                    scraper.users,
                );
                collected.push(record);
            }
            pn += 1;
        }

        return sortCommentsAsc(collected);
    }

    async function scrapeComments() {
        const floors = [...scraper.posts.values()].filter((post) => post.id > 0);
        const tasks = floors.filter(
            (post) => post.reply_num > (post._inline ? post._inline.length : 0),
        );
        scraper.comment.total = tasks.length;
        scraper.comment.done = 0;
        scraper.phase = "comments";
        scraper.stage = 2;
        log(`开始抓取楼中楼，共 ${tasks.length} 层需要补全`, "info");
        renderPanel();

        await mapLimit(tasks, scraper.concurrency, async (post) => {
            try {
                const comments = await fetchAllComments(post);
                post.comments = comments;
            } catch (error) {
                if (isCancelled(error)) {
                    throw error;
                }
                recordError(`楼层 ${post.floor}(${post.id}) 楼中楼：${error.message}`);
                log(`楼层 ${post.floor} 楼中楼抓取失败：${error.message}`, "error");
                post.comments = inlineToComments(post);
            } finally {
                if (!scraper.cancelled) {
                    scraper.comment.done += 1;
                }
                renderPanel();
            }
        });

        if (scraper.cancelled) {
            throw new CancelledError();
        }

        for (const post of floors) {
            if (!post.comments || post.comments.length === 0) {
                post.comments = inlineToComments(post);
            } else {
                sortCommentsAsc(post.comments);
            }
            delete post._inline;
            for (const comment of post.comments) {
                if (!comment.user) {
                    const row = scraper.users.get(comment.user_id);
                    if (row) {
                        comment.user = row;
                    }
                }
            }
        }
    }

    function countComments() {
        let total = 0;
        for (const post of scraper.posts.values()) {
            total += post.comments ? post.comments.length : 0;
        }
        return total;
    }

    function ensureReferencedUsers() {
        const remember = (userId) => {
            if (!userId || scraper.users.has(userId)) {
                return;
            }
            const row = makeUserRow({ id: userId }, scraper.scrapeTime);
            if (row) {
                scraper.users.set(userId, row);
            }
        };

        for (const post of scraper.posts.values()) {
            remember(post.user_id);
            for (const fragment of post.contents) {
                if (fragment.type === FRAGMENT_TYPE.AT) {
                    remember(fragment.user_id);
                }
            }
            for (const comment of post.comments || []) {
                remember(comment.user_id);
                remember(comment.reply_to_id);
            }
        }
    }

    function buildResult(partial) {
        const posts = [...scraper.posts.values()].sort(
            (a, b) => a.floor - b.floor || a.id - b.id,
        );
        posts.forEach((post) => {
            // 取消/中断时尚未补全楼中楼的楼层，保留首页内联的楼中楼，避免丢数据
            if (
                (!post.comments || post.comments.length === 0) &&
                post._inline &&
                post._inline.length &&
                scraper.thread
            ) {
                post.comments = inlineToComments(post);
            }
            if (post.comments && post.comments.length > 1) {
                sortCommentsAsc(post.comments);
            }
            delete post._inline;
        });
        ensureReferencedUsers();

        const threadInfo = scraper.thread
            ? normalizeThread(scraper.thread, scraper.forum, scraper.tid)
            : null;

        const record = {
            scrape_time: scraper.scrapeTime,
            scrape_config: {
                POST_FILTER_TYPE: "all",
                DOWNLOAD_USER_AVATAR_MODE: "none",
                SCRAPE_SHARE_ORIGIN: false,
                UPDATE_SHARE_ORIGIN: false,
                CONCURRENCY: scraper.concurrency,
                PAGE_LIMIT: scraper.pageLimit,
            },
            stats: {
                page_total: scraper.page.total,
                page_fetched: scraper.page.done,
                post_count: posts.length,
                comment_count: countComments(),
                user_count: scraper.users.size,
                error_count: scraper.errors.length,
                failed_pages: [...scraper.failedPages].sort((a, b) => a - b),
                partial: !!partial,
            },
            errors: scraper.errors.slice(0, 100),
        };

        return {
            scrape_info: {
                main_thread: scraper.tid,
                create_time: scraper.scrapeTime,
                update_time: Math.floor(Date.now() / 1000),
                scraper_version: APP_VERSION,
                scrape_records: [record],
            },
            threads: threadInfo
                ? [
                    {
                        tid: scraper.tid,
                        forum: normalizeForum(scraper.forum),
                        thread: threadInfo,
                        users: [...scraper.users.values()],
                        posts,
                    },
                ]
                : [],
        };
    }

    function sanitizeFilename(name) {
        return String(name)
            .replace(/[<>:"/\\|?*\u0000-\u001f]/g, "")
            .replace(/\s+/g, " ")
            .trim()
            .slice(0, 120);
    }

    function formatLiteTime(timestamp) {
        const value = Number(timestamp);
        if (!value) {
            return "-";
        }
        const date = new Date((value + 8 * 3600) * 1000);
        return date.toISOString().slice(0, 16).replace("T", " ");
    }

    function sanitizeLiteText(rawText) {
        let text = String(rawText || "").replace(/\r/g, "");
        // 去掉常见的小尾巴：只处理短尾，避免误删正文
        text = text.replace(/\s+[～~]{2,}\s*([\s\S]{0,120})$/, (match, tail) =>
            /群|QQ|qq|微信|vx|VX|http|www\.|\d{5,}/.test(tail) ? "" : match,
        );
        text = text.replace(/\n\s*(?:——|—|--|==)[\s\S]*$/, (match) =>
            match.length <= 120 ? "" : match,
        );
        text = text.replace(/\n\s*来自[^\n]{0,20}客户端[^\n]{0,40}$/, "");
        text = text.replace(/[ \u3000]{2,}/g, " ");
        text = text.replace(/\n{3,}/g, "\n\n");
        text = text.replace(/\|/g, "｜");
        text = text.replace(/\n/g, "\\n");
        return text.trim() || "-";
    }

    function renderLiteContent(contents) {
        let text = "";
        for (const fragment of contents || []) {
            switch (fragment.type) {
                case FRAGMENT_TYPE.TEXT:
                case FRAGMENT_TYPE.AT:
                    text += fragment.text || "";
                    break;
                case FRAGMENT_TYPE.EMOJI:
                    text += fragment.desc ? `[emoji:${fragment.desc}]` : "[emoji]";
                    break;
                case FRAGMENT_TYPE.IMAGE:
                    text += "[img]";
                    break;
                case FRAGMENT_TYPE.LINK:
                    text += fragment.title ? `[link:${fragment.title}]` : "[link]";
                    break;
                case FRAGMENT_TYPE.VIDEO:
                    text += "[vid]";
                    break;
                case FRAGMENT_TYPE.VOICE:
                    text += "[voice]";
                    break;
                default:
                    break;
            }
        }
        return sanitizeLiteText(text);
    }

    // 统计楼层号：存活数、最大楼号、缺失（被删/被吞）的楼号
    function analyzeFloors(posts) {
        const present = new Set();
        let max = 0;
        for (const post of posts) {
            if (post.floor > 0) {
                present.add(post.floor);
                if (post.floor > max) {
                    max = post.floor;
                }
            }
        }
        const missing = [];
        for (let floor = 1; floor <= max; floor += 1) {
            if (!present.has(floor)) {
                missing.push(floor);
            }
        }
        return { count: present.size, max, missing };
    }

    // [55,56,66,72,75] -> "55-56,66,72,75"；过长时截断，避免头部膨胀
    function formatFloorRanges(floors, maxParts = 60) {
        const parts = [];
        let i = 0;
        while (i < floors.length) {
            let j = i;
            while (j + 1 < floors.length && floors[j + 1] === floors[j] + 1) {
                j += 1;
            }
            parts.push(i === j ? String(floors[i]) : `${floors[i]}-${floors[j]}`);
            i = j + 1;
        }
        if (parts.length > maxParts) {
            return `${parts.slice(0, maxParts).join(",")},…`;
        }
        return parts.join(",");
    }

    function buildLiteText(result) {
        const threadBlock = result && result.threads && result.threads[0];
        if (!threadBlock) {
            return "LITE 1.1|empty";
        }

        const thread = threadBlock.thread || {};
        const forum = threadBlock.forum || {};
        const posts = threadBlock.posts || [];
        const users = threadBlock.users || [];

        const nameById = new Map();
        const nameByAccount = new Map();
        const ipById = new Map();
        const rememberUser = (user) => {
            if (!user || !user.id) {
                return;
            }
            const name = user.nickname || user.username || `用户${user.id}`;
            nameById.set(user.id, name);
            if (user.username) {
                nameByAccount.set(user.username, name);
            }
            if (user.ip) {
                ipById.set(user.id, user.ip);
            }
        };

        users.forEach(rememberUser);
        for (const post of posts) {
            rememberUser(post.user);
            for (const comment of post.comments || []) {
                rememberUser(comment.user);
            }
        }

        let author = nameById.get(thread.user_id) || "";
        if (!author) {
            const firstFloor = posts.find((post) => post.floor === 1);
            author = firstFloor && firstFloor.user
                ? firstFloor.user.nickname || firstFloor.user.username || ""
                : "";
        }

        const cleanField = (value) =>
            String(value == null ? "" : value).replace(/\|/g, "｜").replace(/\s+/g, " ").trim();

        const tid = threadBlock.tid || (result.scrape_info && result.scrape_info.main_thread) || 0;
        const forumName = cleanField(forum.name);
        const title = cleanField(thread.title);
        const created = formatLiteTime(thread.create_time);
        const totalReplies = posts.reduce(
            (sum, post) => sum + (post.comments ? post.comments.length : 0),
            0,
        );

        const record =
            result.scrape_info &&
            result.scrape_info.scrape_records &&
            result.scrape_info.scrape_records[0];
        const stats = (record && record.stats) || {};

        // floors=存活楼层数；有缺口时追加 (max:最大楼号) 与 missing=缺失楼号
        const floorInfo = analyzeFloors(posts);
        const floorsField =
            floorInfo.max > floorInfo.count ? `${floorInfo.count}(max:${floorInfo.max})` : String(posts.length);

        let header =
            `LITE 1.1|tid=${tid}|forum=${forumName}|title=${title}|author=${cleanField(author)}|` +
            `created=${created}|floors=${floorsField}|replies=${totalReplies}|tz=+08`;
        if (floorInfo.missing.length) {
            header += `|missing=${formatFloorRanges(floorInfo.missing)}`;
        }
        if (stats.partial) {
            header += "|partial=1";
        }
        if (stats.failed_pages && stats.failed_pages.length) {
            header += `|failed_pages=${stats.failed_pages.join(",")}`;
        }
        if (stats.error_count) {
            header += `|errors=${stats.error_count}`;
        }

        const lines = [
            header,
            "format: #floor|user|time|ip|likes|text ; >n|user|time|ip|likes|to|text " +
            "(n=sub-reply index, sorted by time ASC) ; [OP]=thread author ; " +
            "missing=deleted/skipped floor numbers (failed_pages=fetch failed, not deleted) ; " +
            "markers [img][vid][voice][emoji:x][link:t] ; \\n=newline",
            "",
        ];

        const likesField = (agree) => (agree > 0 ? `+${agree}` : "-");

        for (const post of posts) {
            const userName =
                nameById.get(post.user_id) ||
                (post.user && (post.user.nickname || post.user.username)) ||
                `用户${post.user_id}`;
            const ip = (post.user && post.user.ip) || ipById.get(post.user_id) || "-";
            const content = renderLiteContent(post.contents);
            const opMark = post.is_thread_author ? "[OP]" : "";
            lines.push(
                `#${post.floor}|${cleanField(userName)}${opMark}|${formatLiteTime(post.create_time)}|${cleanField(ip)}|${likesField(post.agree)}|${content}`,
            );

            // 导出前再保险排序一次，保证楼中楼严格按时间正序
            const comments = [...(post.comments || [])].sort(compareByTime);
            comments.forEach((comment, index) => {
                let commentContent = renderLiteContent(comment.contents);
                let prefixTarget = null;
                const matched = commentContent.match(/^回复\s*([^\n:：]{1,40})[:：]\s*/);
                if (matched) {
                    prefixTarget = matched[1].trim().replace(/^[@＠]/, "");
                    commentContent = commentContent.slice(matched[0].length).trim() || "-";
                }

                const replyToId = comment.reply_to_id || 0;
                const target = replyToId
                    ? nameById.get(replyToId)
                    : nameByAccount.get(prefixTarget) || prefixTarget;
                const targetField = target ? `@${cleanField(target)}` : "-";
                const commentUser =
                    nameById.get(comment.user_id) ||
                    (comment.user && (comment.user.nickname || comment.user.username)) ||
                    `用户${comment.user_id}`;
                const commentIp =
                    (comment.user && comment.user.ip) || ipById.get(comment.user_id) || "-";
                const commentOp = comment.is_thread_author ? "[OP]" : "";
                lines.push(
                    `>${index + 1}|${cleanField(commentUser)}${commentOp}|${formatLiteTime(comment.create_time)}|${cleanField(commentIp)}|${likesField(comment.agree)}|${targetField}|${commentContent}`,
                );
            });
        }

        return lines.join("\n");
    }

    function buildExportPayload(result, format) {
        if (format === "lite") {
            return {
                text: buildLiteText(result),
                extension: "txt",
                mime: "text/plain;charset=utf-8",
            };
        }
        return {
            text: JSON.stringify(result),
            extension: "json",
            mime: "application/json;charset=utf-8",
        };
    }

    function buildFilename(format) {
        const forumName = scraper.forum ? scraper.forum.name : "unknown";
        const title = scraper.thread ? scraper.thread.title : "";
        const timestamp = Date.now() * 1000;
        const extension = format === "lite" ? "txt" : "json";
        return `[${forumName}吧][${scraper.tid}]${sanitizeFilename(title)}_${timestamp}.${extension}`;
    }

    function downloadResult(result, format, filename) {
        const payload = buildExportPayload(result, format);
        const blob = new Blob([payload.text], { type: payload.mime });
        const url = URL.createObjectURL(blob);
        const anchor = document.createElement("a");
        anchor.href = url;
        anchor.download = filename;
        (document.body || document.documentElement).appendChild(anchor);
        anchor.click();
        anchor.remove();
        setTimeout(() => URL.revokeObjectURL(url), 1000);
        return blob.size;
    }

    function exportNow(result, format) {
        const filename = buildFilename(format);
        const size = downloadResult(result, format, filename);
        scraper.lastExport = { filename, size, format };
        return scraper.lastExport;
    }

    let tickTimer = 0;

    async function startScrape() {
        if (scraper.running) {
            return;
        }

        const tid = parseTid();
        if (!tid) {
            log("当前页面不是帖子页，无法获取 tid", "error");
            toast("当前页面不是帖子页", "err");
            return;
        }

        scraper.running = true;
        scraper.cancelled = false;
        scraper.phase = "posts";
        scraper.stage = 1;
        scraper.tid = tid;
        scraper.scrapeTime = Math.floor(Date.now() / 1000);
        scraper.startedAt = Date.now();
        scraper.finishedAt = 0;
        scraper.page = { done: 0, total: 0 };
        scraper.comment = { done: 0, total: 0 };
        scraper.posts = new Map();
        scraper.users = new Map();
        scraper.forum = null;
        scraper.thread = null;
        scraper.errors = [];
        scraper.failedPages = [];
        scraper.fatal = "";
        scraper.result = null;
        scraper.lastExport = null;
        scraper.logs = [];
        scraper.concurrency = readNumberInput("tbarch-concurrency", 3, 1, 6);
        scraper.pageLimit = readNumberInput("tbarch-page-limit", 0, 0, 99999);
        persistSettings();
        openPanel();
        updateButtons();
        log(`开始抓取 tid=${tid}`, "info");

        clearInterval(tickTimer);
        tickTimer = setInterval(renderPanel, 1000);

        try {
            scraper.bduss = await getBduss();
            if (!scraper.bduss) {
                log("未读取到 BDUSS，将依赖浏览器 Cookie 请求", "warn");
            }

            const firstPage = await fetchPostsPage(tid, 1);
            absorbPageResponse(firstPage, true);
            refreshMeta();
            if (!isThreadVisible(scraper.thread) || scraper.posts.size === 0) {
                throw new Error("帖子可能已被屏蔽或删除，或当前账号无权访问");
            }

            const totalPage = firstPage.page ? firstPage.page.totalPage || 1 : 1;
            const limit = scraper.pageLimit > 0 ? Math.min(totalPage, scraper.pageLimit) : totalPage;
            scraper.page.total = limit;
            scraper.page.done = 1;
            log(
                `第 1 页完成：${scraper.posts.size} 楼，共 ${totalPage} 页${limit < totalPage ? `（本次限制 ${limit} 页）` : ""
                }`,
                "success",
            );
            renderPanel();

            const restPages = [];
            for (let pn = 2; pn <= limit; pn += 1) {
                restPages.push(pn);
            }
            if (restPages.length) {
                await scrapeFloors(restPages);
            }
            if (scraper.cancelled) {
                throw new CancelledError();
            }

            await scrapeComments();

            scraper.phase = "done";
            scraper.result = buildResult(limit < totalPage);
            const format = scraper.exportFormat;
            const info = exportNow(scraper.result, format);
            log(
                `抓取完成，已导出${format === "lite" ? " Lite 文本" : " JSON"}（${formatBytes(info.size)}）`,
                "success",
            );
            toast(`抓取完成，已导出 ${formatName(format)} · ${formatBytes(info.size)}`, "ok");
        } catch (error) {
            if (isCancelled(error)) {
                scraper.phase = "cancelled";
                if (scraper.posts.size > 0) {
                    scraper.result = buildResult(true);
                }
                log("已取消，当前数据可下载", "warn");
                toast("已取消抓取", "warn");
            } else {
                scraper.phase = "error";
                scraper.fatal = error.message;
                recordError(error.message);
                log(`抓取失败：${error.message}`, "error");
                if (scraper.posts.size > 0) {
                    scraper.result = buildResult(true);
                    log("已保留部分数据，可下载", "warn");
                }
                toast(`抓取失败：${error.message}`, "err");
            }
        } finally {
            scraper.running = false;
            scraper.finishedAt = Date.now();
            clearInterval(tickTimer);
            tickTimer = 0;
            updateButtons();
            renderPanel();
        }
    }

    function cancelScrape() {
        if (!scraper.running) {
            return;
        }
        scraper.cancelled = true;
        abortActiveRequests();
        log("正在取消…", "warn");
    }

    function formatBytes(size) {
        if (size < 1024) {
            return `${size} B`;
        }
        if (size < 1024 * 1024) {
            return `${(size / 1024).toFixed(1)} KB`;
        }
        return `${(size / 1024 / 1024).toFixed(1)} MB`;
    }

    function formatDuration(ms) {
        const total = Math.max(0, Math.round(ms / 1000));
        if (total < 60) {
            return `${total} 秒`;
        }
        return `${Math.floor(total / 60)} 分 ${total % 60} 秒`;
    }

    function formatName(format) {
        return format === "lite" ? "Lite 文本" : "JSON";
    }

    // ---------------------------------------------------------------------------
    // UI
    // ---------------------------------------------------------------------------

    const VERSION = APP_VERSION.replace(/^browser-/, "");
    const $ = (id) => document.getElementById(id);

    const svg = (inner) =>
        `<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.9" ` +
        `stroke-linecap="round" stroke-linejoin="round" aria-hidden="true">${inner}</svg>`;

    const ICONS = {
        download: svg('<path d="M12 3v12"/><path d="m7 10 5 5 5-5"/><path d="M5 21h14"/>'),
        archive: svg(
            '<rect x="3" y="4" width="18" height="5" rx="1.6"/><path d="M5 9v9a2 2 0 0 0 2 2h10a2 2 0 0 0 2-2V9"/><path d="M10 13h4"/>',
        ),
        close: svg('<path d="M18 6 6 18"/><path d="m6 6 12 12"/>'),
        sliders: svg(
            '<path d="M4 7h9"/><path d="M17 7h3"/><circle cx="15" cy="7" r="2"/><path d="M4 17h3"/><path d="M11 17h9"/><circle cx="9" cy="17" r="2"/>',
        ),
        copy: svg('<rect x="9" y="9" width="11" height="11" rx="2.5"/><path d="M5 15V6.5A2.5 2.5 0 0 1 7.5 4H15"/>'),
        check: svg('<path d="m5 12.5 4.5 4.5L19 7.5"/>'),
        stop: svg('<rect x="6" y="6" width="12" height="12" rx="2.5"/>'),
        play: svg('<path d="M8 5.5v13l10.5-6.5z"/>'),
        refresh: svg('<path d="M20 12a8 8 0 1 1-2.6-5.9"/><path d="M20 4v5h-5"/>'),
        braces: svg(
            '<path d="M8 4C6 4 5 5 5 7v2c0 1.5-.7 2.5-2 3 1.3.5 2 1.5 2 3v2c0 2 1 3 3 3"/><path d="M16 4c2 0 3 1 3 3v2c0 1.5.7 2.5 2 3-1.3.5-2 1.5-2 3v2c0 2-1 3-3 3"/>',
        ),
        text: svg(
            '<path d="M14 3H7a2 2 0 0 0-2 2v14a2 2 0 0 0 2 2h10a2 2 0 0 0 2-2V8z"/><path d="M14 3v5h5"/><path d="M9 13h6"/><path d="M9 17h4"/>',
        ),
        file: svg('<path d="M14 3H7a2 2 0 0 0-2 2v14a2 2 0 0 0 2 2h10a2 2 0 0 0 2-2V8z"/><path d="M14 3v5h5"/>'),
        layers: svg('<path d="m12 3 9 5-9 5-9-5z"/><path d="m3 13 9 5 9-5"/>'),
        message: svg('<path d="M21 12a8 8 0 0 1-11.6 7.1L4 20l1-4.5A8 8 0 1 1 21 12z"/>'),
        alert: svg('<circle cx="12" cy="12" r="9"/><path d="M12 8v5"/><path d="M12 16.5h.01"/>'),
        info: svg('<circle cx="12" cy="12" r="9"/><path d="M12 11v5"/><path d="M12 7.5h.01"/>'),
        chevron: svg('<path d="m6 9 6 6 6-6"/>'),
    };

    const STYLE = `
  /* ---------- 导航栏按钮（固定浅色，贴合贴吧顶栏） ---------- */
  #tbarch-nav-btn { position: relative; isolation: isolate; overflow: hidden;
    display: inline-flex; align-items: center; justify-content: center; gap: 7px;
    height: 34px; margin: 0 0 0 8px; padding: 0 14px 0 11px;
    border: 1px solid #d3e0ff; border-radius: 999px; background: #f3f7ff; color: #2f5bea;
    font: 600 13px/1 -apple-system, BlinkMacSystemFont, "PingFang SC", "Microsoft YaHei", "Segoe UI", Arial, sans-serif;
    cursor: pointer; flex: 0 0 auto; box-sizing: border-box; white-space: nowrap; user-select: none;
    -webkit-tap-highlight-color: transparent;
    transition: background-color .16s, border-color .16s, box-shadow .16s, transform .12s; }
  #tbarch-nav-btn::before { content: ""; position: absolute; inset: 0; z-index: -1; pointer-events: none;
    width: var(--tbarch-p, 0%); opacity: 0;
    background: linear-gradient(90deg, rgba(59,109,246,.14), rgba(59,109,246,.30));
    transition: width .3s ease, opacity .2s; }
  #tbarch-nav-btn.running::before { opacity: 1; }
  #tbarch-nav-btn:hover { background: #e9f0ff; border-color: #b7ccff; box-shadow: 0 2px 10px rgba(47,91,234,.16); }
  #tbarch-nav-btn:active { transform: scale(.97); }
  #tbarch-nav-btn:focus-visible { outline: 2px solid #3b6df6; outline-offset: 2px; }
  #tbarch-nav-btn.active { background: #e4edff; border-color: #a5beff; }
  #tbarch-nav-btn .tbarch-nav-ic { display: inline-flex; width: 16px; height: 16px; }
  #tbarch-nav-btn .tbarch-nav-ic svg { width: 16px; height: 16px; display: block; }
  #tbarch-nav-btn.running .tbarch-nav-ic { animation: tbarch-bob 1s ease-in-out infinite; }
  #tbarch-nav-btn .tbarch-nav-tx { min-width: 2.8em; text-align: center; font-variant-numeric: tabular-nums; }
  #tbarch-nav-btn .tbarch-nav-dot { display: none; width: 7px; height: 7px; border-radius: 50%;
    background: #16a34a; box-shadow: 0 0 0 3px rgba(22,163,74,.18); }
  #tbarch-nav-btn.done .tbarch-nav-dot { display: inline-block; }
  #tbarch-nav-btn.tbarch-floating { position: fixed; right: 22px; bottom: 26px; margin: 0; height: 42px;
    padding: 0 18px 0 14px; z-index: 2147482999; background: #fff; border-color: #cfdcff;
    box-shadow: 0 10px 28px rgba(47,91,234,.28); }

  /* ---------- 设计令牌 ---------- */
  #tbarch-panel, #tbarch-toast {
    --tb-bg: #ffffff; --tb-soft: #f5f7fb; --tb-hover: #ebeff6;
    --tb-line: #e7ecf3; --tb-line-2: #d5dce8;
    --tb-text: #0f172a; --tb-text-2: #475569; --tb-text-3: #8793a7;
    --tb-accent: #3b6df6; --tb-accent-soft: #eef3ff; --tb-accent-ink: #2a55d6; --tb-ring: rgba(59,109,246,.16);
    --tb-primary-a: #5a86ff; --tb-primary-b: #3a64f2;
    --tb-ok: #16a34a; --tb-ok-soft: #ecfdf3;
    --tb-warn: #d97706; --tb-warn-soft: #fff6e0;
    --tb-err: #dc2626; --tb-err-soft: #fef2f2;
    --tb-shadow: 0 28px 60px -14px rgba(15,23,42,.30), 0 6px 18px rgba(15,23,42,.08);
    --tb-font: -apple-system, BlinkMacSystemFont, "PingFang SC", "Microsoft YaHei", "Segoe UI", Roboto, Arial, sans-serif;
    color-scheme: light; }
  @media (prefers-color-scheme: dark) {
    #tbarch-panel, #tbarch-toast {
      --tb-bg: #171a21; --tb-soft: #1e222b; --tb-hover: #282d38;
      --tb-line: #2a303c; --tb-line-2: #3a4150;
      --tb-text: #e9edf5; --tb-text-2: #aab4c5; --tb-text-3: #748092;
      --tb-accent: #6a93ff; --tb-accent-soft: rgba(106,147,255,.14); --tb-accent-ink: #9db9ff; --tb-ring: rgba(106,147,255,.22);
      --tb-primary-a: #5f8bff; --tb-primary-b: #4169f0;
      --tb-ok: #34d399; --tb-ok-soft: rgba(52,211,153,.12);
      --tb-warn: #fbbf24; --tb-warn-soft: rgba(251,191,36,.12);
      --tb-err: #f87171; --tb-err-soft: rgba(248,113,113,.12);
      --tb-shadow: 0 28px 60px -14px rgba(0,0,0,.7), 0 0 0 1px rgba(255,255,255,.04);
      color-scheme: dark; }
  }

  /* ---------- 面板骨架 ---------- */
  #tbarch-panel { position: fixed; z-index: 2147483000; display: flex; flex-direction: column;
    width: 384px; max-width: calc(100vw - 16px); overflow: hidden; background: var(--tb-bg); color: var(--tb-text);
    border: 1px solid var(--tb-line); border-radius: 18px; box-shadow: var(--tb-shadow);
    font: 13px/1.55 var(--tb-font); text-align: left; letter-spacing: 0; -webkit-font-smoothing: antialiased; }
  #tbarch-panel[hidden], #tbarch-panel [hidden] { display: none !important; }
  #tbarch-panel:not([hidden]) { animation: tbarch-pop .2s cubic-bezier(.2,.9,.3,1.15); }
  #tbarch-panel *, #tbarch-panel *::before, #tbarch-panel *::after { box-sizing: border-box; }
  #tbarch-panel button, #tbarch-panel input { font-family: inherit; margin: 0; }
  #tbarch-panel button { -webkit-appearance: none; appearance: none; }
  #tbarch-panel svg { display: block; flex: none; }
  #tbarch-panel p { margin: 0; }
  #tbarch-panel button:focus-visible, #tbarch-panel input:focus-visible { outline: 2px solid var(--tb-accent); outline-offset: 2px; }

  .tbarch-hd { flex: none; display: flex; align-items: center; gap: 10px; padding: 14px 14px 12px 16px;
    border-bottom: 1px solid var(--tb-line); background: var(--tb-bg); }
  .tbarch-brand { display: flex; align-items: center; gap: 10px; min-width: 0; flex: 1; }
  .tbarch-logo { width: 34px; height: 34px; flex: none; border-radius: 11px; display: flex; align-items: center;
    justify-content: center; color: #fff; background: linear-gradient(135deg, var(--tb-primary-a), var(--tb-primary-b));
    box-shadow: 0 6px 14px -4px rgba(51,97,240,.55); }
  .tbarch-logo svg { width: 18px; height: 18px; }
  .tbarch-brand-tx { display: flex; flex-direction: column; min-width: 0; line-height: 1.3; }
  .tbarch-title { font-size: 14.5px; font-weight: 700; white-space: nowrap; }
  .tbarch-sub { font-size: 11px; color: var(--tb-text-3); white-space: nowrap; }
  .tbarch-status { display: inline-flex; align-items: center; gap: 6px; height: 24px; padding: 0 10px;
    border-radius: 999px; background: var(--tb-soft); color: var(--tb-text-2);
    font-size: 11.5px; font-weight: 600; white-space: nowrap; transition: background-color .2s, color .2s; }
  .tbarch-status i { width: 6px; height: 6px; border-radius: 50%; background: currentColor; flex: none; }
  .tbarch-status em { font-style: normal; }
  .tbarch-status.running { background: var(--tb-accent-soft); color: var(--tb-accent-ink); }
  .tbarch-status.running i { animation: tbarch-pulse 1.2s ease-in-out infinite; }
  .tbarch-status.success { background: var(--tb-ok-soft); color: var(--tb-ok); }
  .tbarch-status.warn { background: var(--tb-warn-soft); color: var(--tb-warn); }
  .tbarch-status.error { background: var(--tb-err-soft); color: var(--tb-err); }
  .tbarch-icon-btn { width: 30px; height: 30px; flex: none; display: flex; align-items: center; justify-content: center;
    padding: 0; border: 0; border-radius: 9px; background: transparent; color: var(--tb-text-3); cursor: pointer;
    transition: background-color .15s, color .15s; }
  .tbarch-icon-btn:hover { background: var(--tb-hover); color: var(--tb-text); }
  .tbarch-icon-btn svg { width: 16px; height: 16px; }

  .tbarch-bd { flex: 1 1 auto; min-height: 0; overflow-y: auto; padding: 14px 16px 16px;
    display: flex; flex-direction: column; gap: 14px;
    scrollbar-width: thin; scrollbar-color: var(--tb-line-2) transparent; }

  /* ---------- 帖子信息 ---------- */
  .tbarch-meta { padding: 12px 14px; border: 1px solid var(--tb-line); border-radius: 14px; background: var(--tb-soft); }
  .tbarch-meta-title { font-size: 13.5px; font-weight: 600; line-height: 1.45; word-break: break-word;
    display: -webkit-box; -webkit-line-clamp: 2; -webkit-box-orient: vertical; overflow: hidden; }
  .tbarch-meta-sub { display: flex; align-items: center; flex-wrap: wrap; gap: 6px; margin-top: 9px; }
  .tbarch-chip { display: inline-flex; align-items: center; gap: 5px; height: 22px; padding: 0 8px;
    border: 1px solid var(--tb-line); border-radius: 7px; background: var(--tb-bg); color: var(--tb-text-2);
    font-size: 11px; font-variant-numeric: tabular-nums; }
  .tbarch-chip b { font-weight: 600; color: var(--tb-text); }
  .tbarch-chip.accent { border-color: transparent; background: var(--tb-accent-soft); color: var(--tb-accent-ink); font-weight: 600; }
  .tbarch-chip-btn { display: inline-flex; align-items: center; gap: 4px; height: 22px; padding: 0 6px; border: 0;
    border-radius: 7px; background: transparent; color: var(--tb-accent-ink); font-size: 11px; font-weight: 600; cursor: pointer;
    transition: background-color .15s; }
  .tbarch-chip-btn:hover { background: var(--tb-accent-soft); }
  .tbarch-chip-btn svg { width: 12px; height: 12px; }

  /* ---------- 导出格式 ---------- */
  .tbarch-sec-hd { margin: 0 2px 8px; font-size: 12px; font-weight: 600; color: var(--tb-text-2); }
  .tbarch-formats { display: grid; grid-template-columns: 1fr 1fr; gap: 8px; }
  .tbarch-fmt { position: relative; display: flex; flex-direction: column; align-items: flex-start; gap: 9px;
    padding: 12px; text-align: left; border: 1.5px solid var(--tb-line); border-radius: 14px; background: var(--tb-bg);
    color: var(--tb-text); cursor: pointer;
    transition: border-color .15s, background-color .15s, box-shadow .15s, transform .12s; }
  .tbarch-fmt:hover:not(:disabled) { border-color: var(--tb-line-2); background: var(--tb-soft); }
  .tbarch-fmt:active:not(:disabled) { transform: scale(.985); }
  .tbarch-fmt.active, .tbarch-fmt.active:hover:not(:disabled) { border-color: var(--tb-accent); background: var(--tb-accent-soft);
    box-shadow: 0 0 0 3px var(--tb-ring); }
  .tbarch-fmt:disabled { opacity: .55; cursor: default; }
  .tbarch-fmt-ic { width: 30px; height: 30px; border-radius: 9px; display: flex; align-items: center; justify-content: center;
    background: var(--tb-soft); color: var(--tb-text-2); transition: background-color .15s, color .15s; }
  .tbarch-fmt.active .tbarch-fmt-ic { background: var(--tb-accent); color: #fff; }
  .tbarch-fmt-ic svg { width: 16px; height: 16px; }
  .tbarch-fmt-tx { display: flex; flex-direction: column; gap: 1px; }
  .tbarch-fmt-tx b { font-size: 13px; font-weight: 600; }
  .tbarch-fmt-tx small { font-size: 11px; line-height: 1.4; color: var(--tb-text-3); }
  .tbarch-fmt-ck { position: absolute; top: 10px; right: 10px; width: 18px; height: 18px; border-radius: 50%;
    display: flex; align-items: center; justify-content: center; border: 1.5px solid var(--tb-line-2); color: transparent;
    transition: background-color .15s, border-color .15s, color .15s; }
  .tbarch-fmt-ck svg { width: 11px; height: 11px; stroke-width: 3; }
  .tbarch-fmt.active .tbarch-fmt-ck { background: var(--tb-accent); border-color: var(--tb-accent); color: #fff; }

  .tbarch-hint { display: flex; align-items: flex-start; gap: 8px; padding: 0 2px; color: var(--tb-text-3);
    font-size: 11.5px; line-height: 1.6; }
  .tbarch-hint svg { width: 14px; height: 14px; margin-top: 2px; }

  /* ---------- 抓取进度 ---------- */
  .tbarch-run { display: flex; flex-direction: column; gap: 14px; padding: 14px; border: 1px solid var(--tb-line);
    border-radius: 14px; background: var(--tb-bg); }
  .tbarch-steps { list-style: none; margin: 0; padding: 0; display: flex; align-items: center; }
  .tbarch-steps li { list-style: none; }
  .tbarch-step { display: flex; align-items: center; gap: 6px; color: var(--tb-text-3); font-size: 11.5px;
    font-weight: 500; white-space: nowrap; transition: color .2s; }
  .tbarch-step i { width: 20px; height: 20px; border-radius: 50%; display: flex; align-items: center; justify-content: center;
    font-style: normal; font-size: 11px; font-weight: 700; background: var(--tb-soft); border: 1.5px solid var(--tb-line-2);
    color: var(--tb-text-3); transition: background-color .2s, border-color .2s, color .2s, box-shadow .2s; }
  .tbarch-step i svg { width: 11px; height: 11px; stroke-width: 3; }
  .tbarch-step[data-state="active"] { color: var(--tb-text); font-weight: 600; }
  .tbarch-step[data-state="active"] i { background: var(--tb-accent-soft); border-color: var(--tb-accent);
    color: var(--tb-accent-ink); box-shadow: 0 0 0 3px var(--tb-ring); }
  .tbarch-step[data-state="done"] { color: var(--tb-text-2); }
  .tbarch-step[data-state="done"] i { background: var(--tb-ok); border-color: var(--tb-ok); color: #fff; }
  .tbarch-step[data-state="warn"] { color: var(--tb-warn); font-weight: 600; }
  .tbarch-step[data-state="warn"] i { background: var(--tb-warn-soft); border-color: var(--tb-warn); color: var(--tb-warn); }
  .tbarch-step[data-state="error"] { color: var(--tb-err); font-weight: 600; }
  .tbarch-step[data-state="error"] i { background: var(--tb-err-soft); border-color: var(--tb-err); color: var(--tb-err); }
  .tbarch-step-line { flex: 1; height: 2px; min-width: 12px; margin: 0 8px; border-radius: 2px; background: var(--tb-line);
    transition: background-color .3s; }
  .tbarch-step-line[data-state="done"] { background: var(--tb-ok); }

  .tbarch-prog-hd { display: flex; align-items: baseline; justify-content: space-between; gap: 10px; margin-bottom: 8px; }
  .tbarch-phase { font-size: 12.5px; font-weight: 600; min-width: 0; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
  .tbarch-prog-r { flex: none; color: var(--tb-text-3); font-size: 11px; font-variant-numeric: tabular-nums; white-space: nowrap; }
  .tbarch-prog-r b { margin-right: 6px; font-size: 12.5px; font-weight: 700; color: var(--tb-text); }
  .tbarch-track { height: 8px; border-radius: 999px; background: var(--tb-soft); overflow: hidden;
    box-shadow: inset 0 0 0 1px var(--tb-line); }
  .tbarch-fill { position: relative; overflow: hidden; height: 100%; width: 0; border-radius: 999px;
    background: linear-gradient(90deg, var(--tb-primary-b), var(--tb-primary-a));
    transition: width .35s cubic-bezier(.4,0,.2,1), background .3s; }
  .tbarch-fill::after { content: ""; position: absolute; inset: 0; transform: translateX(-100%);
    background: linear-gradient(90deg, transparent, rgba(255,255,255,.5), transparent); }
  .tbarch-run[data-state="running"] .tbarch-fill::after { animation: tbarch-shimmer 1.5s ease-in-out infinite; }
  .tbarch-run[data-state="success"] .tbarch-fill { background: linear-gradient(90deg, #22c55e, var(--tb-ok)); }
  .tbarch-run[data-state="warn"] .tbarch-fill { background: linear-gradient(90deg, #fbbf24, var(--tb-warn)); }
  .tbarch-run[data-state="error"] .tbarch-fill { background: linear-gradient(90deg, #f87171, var(--tb-err)); }

  .tbarch-stats { display: grid; grid-template-columns: repeat(4, 1fr); gap: 8px; }
  .tbarch-stat { display: flex; flex-direction: column; align-items: center; gap: 1px; padding: 9px 4px 8px;
    border: 1px solid transparent; border-radius: 12px; background: var(--tb-soft); transition: background-color .2s; }
  .tbarch-stat svg { width: 14px; height: 14px; margin-bottom: 2px; color: var(--tb-text-3); }
  .tbarch-stat b { font-size: 14px; font-weight: 700; line-height: 1.35; font-variant-numeric: tabular-nums; white-space: nowrap; }
  .tbarch-stat small { font-size: 10px; color: var(--tb-text-3); }
  .tbarch-stat.error { background: var(--tb-err-soft); }
  .tbarch-stat.error b, .tbarch-stat.error svg { color: var(--tb-err); }

  .tbarch-logs { display: flex; flex-direction: column; gap: 6px; }
  .tbarch-live { display: flex; align-items: center; gap: 8px; width: 100%; padding: 7px 10px; border: 0; border-radius: 10px;
    background: var(--tb-soft); color: var(--tb-text-2); font-size: 11.5px; text-align: left; cursor: pointer;
    transition: background-color .15s; }
  .tbarch-live:hover { background: var(--tb-hover); }
  .tbarch-live .dot { width: 7px; height: 7px; flex: none; border-radius: 50%; background: var(--tb-text-3); }
  .tbarch-live[data-level="success"] .dot { background: var(--tb-ok); }
  .tbarch-live[data-level="warn"] .dot { background: var(--tb-warn); }
  .tbarch-live[data-level="error"] .dot { background: var(--tb-err); }
  .tbarch-live .msg { flex: 1; min-width: 0; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
  .tbarch-live .chev { flex: none; color: var(--tb-text-3); transition: transform .2s; }
  .tbarch-live .chev svg { width: 13px; height: 13px; }
  .tbarch-live.open .chev { transform: rotate(180deg); }
  .tbarch-log { max-height: 136px; overflow-y: auto; padding: 6px 10px; border-radius: 10px; background: var(--tb-soft);
    font: 11px/1.85 ui-monospace, "SF Mono", Menlo, Consolas, "PingFang SC", "Microsoft YaHei", monospace;
    scrollbar-width: thin; scrollbar-color: var(--tb-line-2) transparent; }
  .tbarch-log div { display: flex; gap: 8px; word-break: break-word; color: var(--tb-text-2); }
  .tbarch-log time { flex: none; color: var(--tb-text-3); }
  .tbarch-log .lv-success { color: var(--tb-ok); }
  .tbarch-log .lv-warn { color: var(--tb-warn); }
  .tbarch-log .lv-error { color: var(--tb-err); }

  /* ---------- 结果卡片 ---------- */
  .tbarch-result { display: flex; align-items: flex-start; gap: 12px; padding: 12px 14px; border-radius: 14px; }
  .tbarch-result[data-kind="ok"] { background: var(--tb-ok-soft); }
  .tbarch-result[data-kind="warn"] { background: var(--tb-warn-soft); }
  .tbarch-result[data-kind="err"] { background: var(--tb-err-soft); }
  .tbarch-result .ic { width: 28px; height: 28px; flex: none; border-radius: 50%; display: flex; align-items: center;
    justify-content: center; color: #fff; }
  .tbarch-result .ic svg { width: 15px; height: 15px; stroke-width: 2.4; }
  .tbarch-result[data-kind="ok"] .ic { background: var(--tb-ok); }
  .tbarch-result[data-kind="warn"] .ic { background: var(--tb-warn); }
  .tbarch-result[data-kind="err"] .ic { background: var(--tb-err); }
  .tbarch-result .tx { min-width: 0; display: flex; flex-direction: column; gap: 2px; }
  .tbarch-result .tx b { font-size: 13px; font-weight: 700; }
  .tbarch-result .desc { font-size: 12px; color: var(--tb-text-2); word-break: break-word; }
  .tbarch-result code { display: block; margin-top: 2px; overflow: hidden; text-overflow: ellipsis; white-space: nowrap;
    font: 11px/1.5 ui-monospace, "SF Mono", Menlo, Consolas, monospace; color: var(--tb-text-3); }

  /* ---------- 底栏 / 设置 ---------- */
  .tbarch-ft { flex: none; border-top: 1px solid var(--tb-line); background: var(--tb-bg); }
  .tbarch-collapse { display: grid; grid-template-rows: 0fr; transition: grid-template-rows .26s ease; }
  .tbarch-collapse.open { grid-template-rows: 1fr; }
  .tbarch-collapse > .inner { min-height: 0; overflow: hidden; visibility: hidden; transition: visibility 0s .26s; }
  .tbarch-collapse.open > .inner { visibility: visible; transition-delay: 0s; }
  .tbarch-settings { display: flex; flex-direction: column; gap: 14px; padding: 14px 16px; background: var(--tb-soft);
    border-bottom: 1px solid var(--tb-line); }
  .tbarch-field { display: flex; flex-direction: column; gap: 8px; }
  .tbarch-field-hd { display: flex; align-items: baseline; justify-content: space-between; font-size: 12px; font-weight: 600; }
  .tbarch-field-hd label { color: var(--tb-text); }
  .tbarch-field-hd output { font-size: 12px; font-weight: 700; color: var(--tb-accent-ink); font-variant-numeric: tabular-nums; }
  .tbarch-field-hd span { font-size: 11px; font-weight: 400; color: var(--tb-text-3); }
  .tbarch-field-tip { font-size: 11px; color: var(--tb-text-3); line-height: 1.5; }
  .tbarch-range { width: 100%; height: 18px; margin: 0; accent-color: var(--tb-accent); cursor: pointer; }
  .tbarch-limit-row { display: flex; align-items: center; gap: 8px; }
  .tbarch-num { width: 84px; height: 32px; flex: none; padding: 0 10px; border: 1px solid var(--tb-line-2); border-radius: 9px;
    background: var(--tb-bg); color: var(--tb-text); font-size: 12.5px; font-variant-numeric: tabular-nums; outline: none;
    transition: border-color .15s, box-shadow .15s; }
  .tbarch-num:focus { border-color: var(--tb-accent); box-shadow: 0 0 0 3px var(--tb-ring); }
  .tbarch-chips { display: flex; flex-wrap: wrap; gap: 6px; }
  .tbarch-pill { height: 28px; padding: 0 10px; border: 1px solid var(--tb-line-2); border-radius: 999px; background: var(--tb-bg);
    color: var(--tb-text-2); font-size: 11.5px; font-weight: 500; cursor: pointer;
    transition: background-color .15s, border-color .15s, color .15s; }
  .tbarch-pill:hover:not(:disabled) { background: var(--tb-hover); }
  .tbarch-pill.active { border-color: var(--tb-accent); background: var(--tb-accent-soft); color: var(--tb-accent-ink); font-weight: 600; }
  .tbarch-pill:disabled, .tbarch-num:disabled, .tbarch-range:disabled { opacity: .55; cursor: default; }

  .tbarch-ft-row { display: flex; align-items: center; gap: 8px; padding: 12px 16px 14px; }
  .tbarch-ft-r { display: flex; align-items: center; gap: 8px; margin-left: auto; }
  .tbarch-ghost { display: inline-flex; align-items: center; gap: 6px; height: 34px; padding: 0 10px; border: 0; border-radius: 10px;
    background: transparent; color: var(--tb-text-2); font-size: 12.5px; font-weight: 500; cursor: pointer;
    transition: background-color .15s, color .15s; }
  .tbarch-ghost:hover, .tbarch-ghost.on { background: var(--tb-hover); color: var(--tb-text); }
  .tbarch-ghost svg { width: 15px; height: 15px; }
  .tbarch-btn { display: inline-flex; align-items: center; justify-content: center; gap: 6px; height: 36px; padding: 0 14px;
    border: 1px solid var(--tb-line-2); border-radius: 11px; background: var(--tb-bg); color: var(--tb-text);
    font: 600 12.5px/1 var(--tb-font); cursor: pointer; white-space: nowrap;
    transition: background-color .15s, border-color .15s, box-shadow .15s, filter .15s, transform .12s; }
  .tbarch-btn svg { width: 15px; height: 15px; }
  .tbarch-btn:hover { background: var(--tb-soft); }
  .tbarch-btn:active { transform: scale(.97); }
  .tbarch-btn.primary { border-color: transparent; color: #fff;
    background: linear-gradient(180deg, var(--tb-primary-a), var(--tb-primary-b));
    box-shadow: 0 1px 2px rgba(37,70,200,.3), inset 0 1px 0 rgba(255,255,255,.2); }
  .tbarch-btn.primary:hover { filter: brightness(1.06); box-shadow: 0 8px 18px -6px rgba(51,97,240,.6), inset 0 1px 0 rgba(255,255,255,.2); }
  .tbarch-btn.danger { border-color: rgba(220,38,38,.3); color: var(--tb-err); }
  .tbarch-btn.danger:hover { background: var(--tb-err-soft); }
  .tbarch-btn:disabled { opacity: .65; cursor: default; pointer-events: none; }
  .tbarch-spin { width: 14px; height: 14px; border-radius: 50%; border: 2px solid rgba(255,255,255,.4); border-top-color: #fff;
    animation: tbarch-rot .7s linear infinite; }

  /* ---------- Toast ---------- */
  #tbarch-toast { position: fixed; left: 50%; bottom: 32px; z-index: 2147483600; display: flex; align-items: center; gap: 8px;
    max-width: calc(100vw - 32px); padding: 10px 16px; border-radius: 999px; background: #111827; color: #f8fafc;
    border: 1px solid rgba(255,255,255,.08); font: 500 13px/1.4 var(--tb-font);
    box-shadow: 0 14px 34px rgba(0,0,0,.3); opacity: 0; transform: translate(-50%, 12px); pointer-events: none;
    transition: opacity .2s, transform .2s; }
  #tbarch-toast.show { opacity: 1; transform: translate(-50%, 0); }
  #tbarch-toast svg { width: 15px; height: 15px; flex: none; }
  #tbarch-toast[data-kind="ok"] svg { color: #4ade80; }
  #tbarch-toast[data-kind="warn"] svg { color: #fbbf24; }
  #tbarch-toast[data-kind="err"] svg { color: #f87171; }
  #tbarch-toast span { min-width: 0; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }

  @keyframes tbarch-pop { from { opacity: 0; transform: translateY(-6px) scale(.97); } to { opacity: 1; transform: none; } }
  @keyframes tbarch-pulse { 0%, 100% { opacity: .35; } 50% { opacity: 1; } }
  @keyframes tbarch-bob { 0%, 100% { transform: translateY(-1px); } 50% { transform: translateY(2px); } }
  @keyframes tbarch-rot { to { transform: rotate(360deg); } }
  @keyframes tbarch-shimmer { to { transform: translateX(100%); } }
  @media (prefers-reduced-motion: reduce) {
    #tbarch-panel, #tbarch-panel *, #tbarch-nav-btn, #tbarch-nav-btn *, #tbarch-toast {
      animation: none !important; transition: none !important; }
  }
  `;

    let styleInjected = false;

    function injectStyle() {
        if (styleInjected) {
            return;
        }
        styleInjected = true;
        if (typeof GM_addStyle === "function") {
            try {
                GM_addStyle(STYLE);
                return;
            } catch (error) {
                styleInjected = false;
            }
        }
        const style = document.createElement("style");
        style.id = "tbarch-style";
        style.textContent = STYLE;
        (document.head || document.documentElement).appendChild(style);
        styleInjected = true;
    }

    function findHeaderRoot() {
        const isVisible = (element) => {
            const rect = element.getBoundingClientRect();
            return rect.width > 0 && rect.height > 0 && rect.top >= 0 && rect.top < 160;
        };

        const knownBar = document.querySelector("#top-bar, .top-nav-bar, .top-bar-wrapper");
        if (knownBar && isVisible(knownBar)) {
            return knownBar;
        }

        const header = document.querySelector("header");
        if (header && isVisible(header)) {
            return header;
        }

        const search = document.querySelector(
            'input[placeholder*="搜索"], input[type="search"], [class*="search"] input, [class*="Search"] input',
        );
        if (search) {
            let node = search;
            for (let i = 0; i < 8 && node && node !== document.body; i += 1) {
                const rect = node.getBoundingClientRect();
                const wideEnough = rect.width >= Math.min(window.innerWidth * 0.5, 640);
                const hasPostArea =
                    (node.textContent || "").includes("发帖") ||
                    !!node.querySelector(".right-menu, .add-post, .add-btn");
                if (wideEnough && hasPostArea && rect.height > 24 && rect.height <= 96 && rect.top < 160) {
                    return node;
                }
                node = node.parentElement;
            }
        }

        const fallback = document.querySelector("nav, [class*='header'], [class*='Header']");
        if (fallback && isVisible(fallback)) {
            return fallback;
        }
        return null;
    }

    function findClickableAncestor(element) {
        let node = element;
        for (let i = 0; i < 4 && node; i += 1) {
            const tagName = node.tagName ? node.tagName.toLowerCase() : "";
            const role = node.getAttribute ? node.getAttribute("role") : "";
            const className = node.className ? String(node.className) : "";
            if (
                tagName === "button" ||
                tagName === "a" ||
                role === "button" ||
                /btn|button|publish|post/i.test(className)
            ) {
                return node;
            }
            node = node.parentElement;
        }
        return element;
    }

    function findNavInsertion() {
        const rightMenu = document.querySelector("#top-bar .right-menu, .top-nav-bar .right-menu, .right-menu");
        if (rightMenu) {
            const addPost = rightMenu.querySelector(
                ".add-post, .add-btn, [class*='add-post'], [class*='add-btn']",
            );
            if (addPost) {
                const anchor = addPost.closest(".add-post") || addPost;
                if (anchor.parentElement) {
                    return { container: anchor.parentElement, before: anchor.nextSibling || null };
                }
            }
            return { container: rightMenu, before: rightMenu.firstChild };
        }

        const addPostGlobal = document.querySelector(
            "#top-bar .add-post, .top-nav-bar .add-post, .top-bar-wrapper .add-post",
        );
        if (addPostGlobal && addPostGlobal.parentElement) {
            return {
                container: addPostGlobal.parentElement,
                before: addPostGlobal.nextSibling || null,
            };
        }

        const root = findHeaderRoot();
        if (!root) {
            return null;
        }

        let postButton = null;
        const controls = root.querySelectorAll("button, a, [role='button'], div, span");
        for (const element of controls) {
            const text = (element.textContent || "").replace(/\s+/g, "");
            const rect = element.getBoundingClientRect();
            if (text.length <= 6 && text.endsWith("发帖") && rect.width > 0 && rect.height > 0) {
                postButton = element;
            }
        }

        const anchor = postButton ? findClickableAncestor(postButton) : null;
        if (anchor && anchor.parentElement) {
            return { container: anchor.parentElement, before: anchor.nextSibling || null };
        }
        return { container: root, before: null };
    }

    let panelEventsBound = false;
    let logOpen = false;

    function buildNavButton(floating = false) {
        if ($("tbarch-nav-btn")) {
            if (!$("tbarch-panel")) {
                buildPopPanel();
            }
            return true;
        }

        const spot = floating
            ? { container: document.body || document.documentElement, before: null }
            : findNavInsertion();
        if (!spot) {
            return false;
        }

        const button = document.createElement("button");
        button.type = "button";
        button.id = "tbarch-nav-btn";
        if (floating) {
            button.classList.add("tbarch-floating");
        }
        button.title = "贴吧存档：导出本贴楼层与楼中楼";
        button.innerHTML =
            `<span class="tbarch-nav-ic">${ICONS.download}</span>` +
            `<span class="tbarch-nav-tx" id="tbarch-nav-tx">导出</span>` +
            `<i class="tbarch-nav-dot"></i>`;
        button.addEventListener("click", (event) => {
            event.preventDefault();
            event.stopPropagation();
            togglePanel();
        });

        spot.container.insertBefore(button, spot.before);
        injectStyle();
        buildPopPanel();
        refreshMeta();
        updateButtons();
        return true;
    }

    function buildPopPanel() {
        if ($("tbarch-panel")) {
            return;
        }

        const panel = document.createElement("div");
        panel.id = "tbarch-panel";
        panel.setAttribute("role", "dialog");
        panel.setAttribute("aria-label", "贴吧存档助手");
        panel.hidden = true;
        panel.innerHTML = `
      <div class="tbarch-hd">
        <div class="tbarch-brand">
          <span class="tbarch-logo">${ICONS.archive}</span>
          <div class="tbarch-brand-tx">
            <span class="tbarch-title">贴吧存档助手</span>
            <span class="tbarch-sub">TiebaArchiver · v${VERSION}</span>
          </div>
        </div>
        <span class="tbarch-status" id="tbarch-status" role="status" aria-live="polite"><i></i><em>准备就绪</em></span>
        <button class="tbarch-icon-btn" id="tbarch-close" type="button" title="关闭 (Esc)" aria-label="关闭">${ICONS.close}</button>
      </div>

      <div class="tbarch-bd">
        <section class="tbarch-meta">
          <div class="tbarch-meta-title" id="tbarch-meta-title">正在读取帖子信息…</div>
          <div class="tbarch-meta-sub">
            <span class="tbarch-chip accent" id="tbarch-forum" hidden></span>
            <span class="tbarch-chip">帖子 ID <b id="tbarch-tid">-</b></span>
            <button class="tbarch-chip-btn" id="tbarch-copy" type="button" title="复制帖子 ID">${ICONS.copy}<span>复制</span></button>
          </div>
        </section>

        <section>
          <div class="tbarch-sec-hd">导出格式</div>
          <div class="tbarch-formats" id="tbarch-format" role="radiogroup" aria-label="导出格式">
            <button class="tbarch-fmt" data-format="full" type="button" role="radio" aria-checked="false">
              <span class="tbarch-fmt-ic">${ICONS.braces}</span>
              <span class="tbarch-fmt-tx"><b>完整 JSON</b><small>保留全部字段与元数据</small></span>
              <span class="tbarch-fmt-ck">${ICONS.check}</span>
            </button>
            <button class="tbarch-fmt" data-format="lite" type="button" role="radio" aria-checked="false">
              <span class="tbarch-fmt-ic">${ICONS.text}</span>
              <span class="tbarch-fmt-tx"><b>Lite 文本</b><small>省 Token，适合 AI 分析</small></span>
              <span class="tbarch-fmt-ck">${ICONS.check}</span>
            </button>
          </div>
        </section>

        <p class="tbarch-hint" id="tbarch-hint">${ICONS.info}<span>请先登录贴吧账号。大帖可随时取消，已抓到的数据仍可下载；图片与视频仅保留链接。</span></p>

        <section class="tbarch-run" id="tbarch-run" data-state="idle" hidden>
          <ol class="tbarch-steps" id="tbarch-steps">
            <li class="tbarch-step" data-i="0"><i>1</i><span>楼层</span></li>
            <li class="tbarch-step-line"></li>
            <li class="tbarch-step" data-i="1"><i>2</i><span>楼中楼</span></li>
            <li class="tbarch-step-line"></li>
            <li class="tbarch-step" data-i="2"><i>3</i><span>导出</span></li>
          </ol>
          <div>
            <div class="tbarch-prog-hd">
              <span class="tbarch-phase" id="tbarch-phase">准备就绪</span>
              <span class="tbarch-prog-r"><b id="tbarch-percent">0%</b><span id="tbarch-elapsed"></span></span>
            </div>
            <div class="tbarch-track"><div class="tbarch-fill" id="tbarch-bar"></div></div>
          </div>
          <div class="tbarch-stats">
            <div class="tbarch-stat">${ICONS.file}<b id="tbarch-st-pages">-</b><small>页</small></div>
            <div class="tbarch-stat">${ICONS.layers}<b id="tbarch-st-posts">0</b><small>楼层</small></div>
            <div class="tbarch-stat">${ICONS.message}<b id="tbarch-st-comments">0</b><small>楼中楼</small></div>
            <div class="tbarch-stat" id="tbarch-stat-errors">${ICONS.alert}<b id="tbarch-st-errors">0</b><small>错误</small></div>
          </div>
          <div class="tbarch-logs" id="tbarch-logs" hidden>
            <button class="tbarch-live" id="tbarch-live" type="button" data-level="info" title="展开 / 收起日志">
              <i class="dot"></i><span class="msg" id="tbarch-live-msg"></span><span class="chev">${ICONS.chevron}</span>
            </button>
            <div class="tbarch-log" id="tbarch-log" hidden></div>
          </div>
        </section>

        <section class="tbarch-result" id="tbarch-result" data-kind="ok" hidden>
          <span class="ic" id="tbarch-result-ic"></span>
          <div class="tx">
            <b id="tbarch-result-title"></b>
            <span class="desc" id="tbarch-result-desc"></span>
            <code id="tbarch-result-file" hidden></code>
          </div>
        </section>
      </div>

      <div class="tbarch-ft">
        <div class="tbarch-collapse" id="tbarch-settings-wrap">
          <div class="inner">
            <div class="tbarch-settings">
              <div class="tbarch-field">
                <div class="tbarch-field-hd"><label for="tbarch-concurrency">并发请求数</label><output id="tbarch-concurrency-val">3</output></div>
                <input id="tbarch-concurrency" class="tbarch-range" type="range" min="1" max="6" step="1" value="3" />
                <p class="tbarch-field-tip">并发越高速度越快，过高可能触发限制，推荐 3。</p>
              </div>
              <div class="tbarch-field">
                <div class="tbarch-field-hd"><label for="tbarch-page-limit">页数上限</label><span>0 = 全部</span></div>
                <div class="tbarch-limit-row">
                  <input id="tbarch-page-limit" class="tbarch-num" type="number" min="0" step="1" inputmode="numeric" />
                  <div class="tbarch-chips" id="tbarch-limit-chips">
                    <button class="tbarch-pill" type="button" data-v="0">全部</button>
                    <button class="tbarch-pill" type="button" data-v="10">10 页</button>
                    <button class="tbarch-pill" type="button" data-v="50">50 页</button>
                  </div>
                </div>
                <p class="tbarch-field-tip">只抓取前 N 页，适合先试跑或超大帖。</p>
              </div>
            </div>
          </div>
        </div>
        <div class="tbarch-ft-row">
          <button class="tbarch-ghost" id="tbarch-settings-toggle" type="button" aria-expanded="false">${ICONS.sliders}<span>设置</span></button>
          <div class="tbarch-ft-r">
            <button class="tbarch-btn danger" id="tbarch-cancel" type="button" hidden>${ICONS.stop}<span>取消</span></button>
            <button class="tbarch-btn" id="tbarch-download" type="button" hidden></button>
            <button class="tbarch-btn primary" id="tbarch-start" type="button"></button>
          </div>
        </div>
      </div>
    `;
        (document.body || document.documentElement).appendChild(panel);
        injectStyle();

        $("tbarch-close").addEventListener("click", closePanel);
        $("tbarch-start").addEventListener("click", () => {
            startScrape();
        });
        $("tbarch-cancel").addEventListener("click", () => {
            cancelScrape();
        });
        $("tbarch-download").addEventListener("click", () => {
            if (!scraper.result) {
                return;
            }
            const format = scraper.exportFormat;
            const info = exportNow(scraper.result, format);
            log(`已重新导出 ${formatName(format)}（${formatBytes(info.size)}）`, "success");
            toast(`已导出 ${formatName(format)} · ${formatBytes(info.size)}`, "ok");
            renderPanel();
        });

        $("tbarch-settings-toggle").addEventListener("click", (event) => {
            const wrap = $("tbarch-settings-wrap");
            const open = !wrap.classList.contains("open");
            wrap.classList.toggle("open", open);
            event.currentTarget.classList.toggle("on", open);
            event.currentTarget.setAttribute("aria-expanded", String(open));
        });

        $("tbarch-live").addEventListener("click", () => {
            logOpen = !logOpen;
            paintLog();
        });

        $("tbarch-copy").addEventListener("click", (event) => {
            const button = event.currentTarget;
            const label = button.querySelector("span");
            const tid = String(scraper.tid || parseTid());
            copyText(tid).then((ok) => {
                label.textContent = ok ? "已复制" : "复制失败";
                toast(ok ? "已复制帖子 ID" : "复制失败，请手动选择", ok ? "ok" : "err");
                setTimeout(() => {
                    label.textContent = "复制";
                }, 1500);
            });
        });

        const concurrencyInput = $("tbarch-concurrency");
        const limitInput = $("tbarch-page-limit");
        concurrencyInput.value = String(readStoredNumber("tbarch-concurrency", 3, 1, 6));
        limitInput.value = String(readStoredNumber("tbarch-page-limit", 0, 0, 99999));
        syncSettingsUi();
        concurrencyInput.addEventListener("input", () => {
            syncSettingsUi();
            persistSettings();
        });
        limitInput.addEventListener("input", syncSettingsUi);
        limitInput.addEventListener("change", () => {
            syncSettingsUi();
            persistSettings();
        });
        for (const pill of panel.querySelectorAll(".tbarch-pill")) {
            pill.addEventListener("click", () => {
                limitInput.value = pill.dataset.v;
                syncSettingsUi();
                persistSettings();
            });
        }

        scraper.exportFormat = readStoredFormat();
        for (const button of formatButtons()) {
            button.addEventListener("click", () => {
                if (scraper.running) {
                    return;
                }
                setExportFormat(button.dataset.format);
            });
        }
        setExportFormat(scraper.exportFormat, true);

        if (!panelEventsBound) {
            panelEventsBound = true;
            document.addEventListener(
                "mousedown",
                (event) => {
                    const currentPanel = $("tbarch-panel");
                    const navButton = $("tbarch-nav-btn");
                    if (!currentPanel || currentPanel.hidden || scraper.running) {
                        return;
                    }
                    if (currentPanel.contains(event.target) || (navButton && navButton.contains(event.target))) {
                        return;
                    }
                    closePanel();
                },
                true,
            );
            document.addEventListener("keydown", (event) => {
                if (event.key === "Escape") {
                    closePanel();
                }
            });
            window.addEventListener("resize", queueReposition, { passive: true });
            window.addEventListener("scroll", queueReposition, { passive: true });
        }

        refreshMeta();
        updateButtons();
    }

    function formatButtons() {
        return document.querySelectorAll("#tbarch-format .tbarch-fmt");
    }

    function syncSettingsUi() {
        const range = $("tbarch-concurrency");
        const limit = $("tbarch-page-limit");
        const output = $("tbarch-concurrency-val");
        if (range && output) {
            output.textContent = range.value;
        }
        if (limit) {
            const current = String(Math.max(0, Math.trunc(Number(limit.value) || 0)));
            for (const pill of document.querySelectorAll("#tbarch-limit-chips .tbarch-pill")) {
                pill.classList.toggle("active", pill.dataset.v === current);
            }
        }
    }

    // ---------- Toast / 剪贴板 ----------

    let toastTimer = 0;

    function toast(message, kind = "info") {
        injectStyle();
        let node = $("tbarch-toast");
        if (!node) {
            node = document.createElement("div");
            node.id = "tbarch-toast";
            node.setAttribute("role", "status");
            node.setAttribute("aria-live", "polite");
            (document.body || document.documentElement).appendChild(node);
        }
        const iconName = kind === "ok" ? "check" : kind === "info" ? "info" : "alert";
        node.dataset.kind = kind;
        node.innerHTML = `${ICONS[iconName]}<span>${escapeHtml(message)}</span>`;
        // 触发过渡：先移除再添加 show
        node.classList.remove("show");
        void node.offsetWidth;
        node.classList.add("show");
        clearTimeout(toastTimer);
        toastTimer = setTimeout(() => node.classList.remove("show"), 2600);
    }

    async function copyText(text) {
        try {
            if (navigator.clipboard && navigator.clipboard.writeText) {
                await navigator.clipboard.writeText(text);
                return true;
            }
        } catch (error) {
            // 回退到 execCommand
        }
        try {
            const area = document.createElement("textarea");
            area.value = text;
            area.style.cssText = "position:fixed;top:-100px;opacity:0;pointer-events:none";
            (document.body || document.documentElement).appendChild(area);
            area.select();
            const ok = document.execCommand("copy");
            area.remove();
            return !!ok;
        } catch (error) {
            return false;
        }
    }

    // ---------- 面板定位 / 开关 ----------

    function positionPanel(panel, button) {
        const margin = 8;
        const width = Math.min(384, window.innerWidth - margin * 2);
        const rect = button ? button.getBoundingClientRect() : null;
        panel.style.right = "auto";

        if (rect && rect.width > 0) {
            const left = Math.min(
                Math.max(margin, rect.right - width),
                Math.max(margin, window.innerWidth - width - margin),
            );
            panel.style.left = `${Math.round(left)}px`;

            if (button.classList.contains("tbarch-floating")) {
                const bottom = Math.max(margin, window.innerHeight - rect.top + 10);
                panel.style.top = "auto";
                panel.style.bottom = `${Math.round(bottom)}px`;
                panel.style.maxHeight = `${Math.max(240, window.innerHeight - bottom - margin)}px`;
                panel.style.transformOrigin = "bottom right";
            } else {
                const top = Math.max(margin, rect.bottom + 10);
                panel.style.bottom = "auto";
                panel.style.top = `${Math.round(top)}px`;
                panel.style.maxHeight = `${Math.max(240, window.innerHeight - top - margin)}px`;
                panel.style.transformOrigin = "top right";
            }
        } else {
            const left = Math.max(margin, window.innerWidth - width - 16);
            panel.style.left = `${Math.round(left)}px`;
            panel.style.top = "64px";
            panel.style.bottom = "auto";
            panel.style.maxHeight = `${Math.max(240, window.innerHeight - 64 - margin)}px`;
        }
    }

    let repositionQueued = false;

    function queueReposition() {
        if (repositionQueued) {
            return;
        }
        repositionQueued = true;
        const run = () => {
            repositionQueued = false;
            const panel = $("tbarch-panel");
            if (panel && !panel.hidden) {
                positionPanel(panel, $("tbarch-nav-btn"));
            }
        };
        if (typeof requestAnimationFrame === "function") {
            requestAnimationFrame(run);
        } else {
            setTimeout(run, 16);
        }
    }

    function openPanel() {
        const panel = $("tbarch-panel");
        const button = $("tbarch-nav-btn");
        if (!panel) {
            return;
        }
        positionPanel(panel, button);
        panel.hidden = false;
        if (button) {
            button.classList.add("active");
        }
        refreshMeta();
        renderPanel();
    }

    function closePanel() {
        const panel = $("tbarch-panel");
        const button = $("tbarch-nav-btn");
        if (panel) {
            panel.hidden = true;
        }
        if (button) {
            button.classList.remove("active");
        }
    }

    function togglePanel() {
        const panel = $("tbarch-panel");
        if (!panel) {
            return;
        }
        if (panel.hidden) {
            openPanel();
        } else {
            closePanel();
        }
    }

    // ---------- 帖子信息 ----------

    function resolvePageMeta() {
        const scrapedTitle = scraper.thread ? scraper.thread.title : "";
        const scrapedForum = scraper.forum ? scraper.forum.name : "";
        if (scrapedTitle) {
            return { title: scrapedTitle, forum: scrapedForum };
        }

        let title = "";
        let forum = "";

        const titleNode = document.querySelector(".core_title_txt, .article-title");
        if (titleNode) {
            title = titleNode.textContent.trim();
        }
        const forumNode = document.querySelector(".card_title_fname");
        if (forumNode) {
            forum = forumNode.textContent.replace(/吧$/, "").trim();
        }

        if (!title || !forum) {
            const raw = (document.title || "").replace(/[-_]百度贴吧$/, "").trim();
            const separator = raw.lastIndexOf("_");
            if (separator > 0) {
                const tail = raw.slice(separator + 1).trim();
                if (tail.endsWith("吧") && tail.length <= 21) {
                    if (!forum) {
                        forum = tail.replace(/吧$/, "");
                    }
                    if (!title) {
                        title = raw.slice(0, separator).trim();
                    }
                } else if (!title) {
                    title = raw;
                }
            } else if (!title) {
                title = raw;
            }
        }

        return { title, forum };
    }

    function refreshMeta() {
        const tid = scraper.tid || parseTid();
        const titleNode = $("tbarch-meta-title");
        const forumNode = $("tbarch-forum");
        const tidNode = $("tbarch-tid");
        if (!titleNode) {
            return;
        }
        if (!tid) {
            titleNode.textContent = "当前页面不是帖子页";
            if (forumNode) {
                forumNode.hidden = true;
            }
            if (tidNode) {
                tidNode.textContent = "-";
            }
            return;
        }

        const { title, forum } = resolvePageMeta();
        const nextTitle = title || "正在读取帖子信息…";
        if (titleNode.textContent !== nextTitle) {
            titleNode.textContent = nextTitle;
        }
        titleNode.title = title || "";
        if (forumNode) {
            forumNode.textContent = forum ? `${forum}吧` : "";
            forumNode.hidden = !forum;
        }
        if (tidNode) {
            tidNode.textContent = String(tid);
        }
    }

    function escapeHtml(text) {
        return String(text)
            .replace(/&/g, "&amp;")
            .replace(/</g, "&lt;")
            .replace(/>/g, "&gt;")
            .replace(/"/g, "&quot;");
    }

    // ---------- 渲染 ----------

    let renderQueued = false;

    function renderPanel() {
        if (renderQueued) {
            return;
        }
        renderQueued = true;
        const run = () => {
            renderQueued = false;
            paintPanel();
        };
        if (typeof requestAnimationFrame === "function") {
            requestAnimationFrame(run);
        } else {
            setTimeout(run, 0);
        }
    }

    function setText(id, text) {
        const node = $(id);
        if (node && node.textContent !== text) {
            node.textContent = text;
        }
    }

    function setHtmlOnce(node, key, html) {
        if (node && node.dataset.key !== key) {
            node.dataset.key = key;
            node.innerHTML = html;
        }
    }

    function elapsedMs() {
        if (!scraper.startedAt) {
            return 0;
        }
        return (scraper.finishedAt || Date.now()) - scraper.startedAt;
    }

    function computePercent() {
        if (scraper.phase === "done") {
            return 100;
        }
        if (scraper.phase === "idle") {
            return 0;
        }
        if (scraper.stage <= 1) {
            const total = scraper.page.total;
            return total > 0 ? Math.min(scraper.page.done / total, 1) * 50 : 0;
        }
        const total = scraper.comment.total;
        return 50 + (total > 0 ? Math.min(scraper.comment.done / total, 1) * 50 : 0);
    }

    function stepStates() {
        if (scraper.phase === "done") {
            return ["done", "done", "done"];
        }
        const states = ["", "", ""];
        for (let i = 0; i < 3; i += 1) {
            const step = i + 1;
            if (scraper.stage > step) {
                states[i] = "done";
            } else if (scraper.stage === step) {
                states[i] =
                    scraper.phase === "error" ? "error" : scraper.phase === "cancelled" ? "warn" : "active";
            }
        }
        return states;
    }

    function isPartialResult() {
        const result = scraper.result;
        const record =
            result &&
            result.scrape_info &&
            result.scrape_info.scrape_records &&
            result.scrape_info.scrape_records[0];
        return !!(record && record.stats && record.stats.partial);
    }

    function paintSteps() {
        const items = document.querySelectorAll("#tbarch-steps .tbarch-step");
        const lines = document.querySelectorAll("#tbarch-steps .tbarch-step-line");
        const states = stepStates();
        items.forEach((item, index) => {
            const state = states[index];
            if (item.dataset.state !== state) {
                item.dataset.state = state;
                item.querySelector("i").innerHTML = state === "done" ? ICONS.check : String(index + 1);
            }
        });
        lines.forEach((line, index) => {
            line.dataset.state = states[index] === "done" ? "done" : "";
        });
    }

    function paintLog() {
        const wrap = $("tbarch-logs");
        const live = $("tbarch-live");
        const box = $("tbarch-log");
        if (!wrap || !live || !box) {
            return;
        }
        const logs = scraper.logs;
        wrap.hidden = logs.length === 0;
        if (!logs.length) {
            box.innerHTML = "";
            return;
        }
        const last = logs[logs.length - 1];
        live.dataset.level = last.level;
        live.classList.toggle("open", logOpen);
        setText("tbarch-live-msg", last.message);
        box.hidden = !logOpen;
        if (logOpen) {
            box.innerHTML = logs
                .map((entry) => {
                    const time = new Date(entry.at).toLocaleTimeString("zh-CN", { hour12: false });
                    return `<div class="lv-${entry.level}"><time>${time}</time><span>${escapeHtml(entry.message)}</span></div>`;
                })
                .join("");
            box.scrollTop = box.scrollHeight;
        }
    }

    function paintResult() {
        const box = $("tbarch-result");
        if (!box) {
            return;
        }
        const finished =
            scraper.phase === "done" || scraper.phase === "cancelled" || scraper.phase === "error";
        box.hidden = !finished;
        if (!finished) {
            return;
        }

        const posts = scraper.posts.size;
        const comments = countComments();
        const errors = scraper.errors.length;
        let kind = "ok";
        let title = "";
        let desc = "";

        if (scraper.phase === "done") {
            title = isPartialResult() ? "抓取完成（已按页数上限截取）" : "抓取完成";
            desc = `${posts} 楼 · ${comments} 条楼中楼 · 用时 ${formatDuration(elapsedMs())}`;
            if (errors) {
                kind = "warn";
                desc += ` · ${errors} 处错误`;
            }
        } else if (scraper.phase === "cancelled") {
            kind = "warn";
            title = "已取消";
            desc = posts
                ? `已保留 ${posts} 楼 / ${comments} 条楼中楼，可下载部分数据`
                : "尚未抓取到任何数据";
        } else {
            kind = "err";
            title = posts ? "抓取中断" : "抓取失败";
            desc = scraper.fatal || "未知错误";
            if (posts) {
                desc += `；已保留 ${posts} 楼，可下载`;
            }
        }

        box.dataset.kind = kind;
        setHtmlOnce($("tbarch-result-ic"), kind, kind === "ok" ? ICONS.check : kind === "warn" ? ICONS.alert : ICONS.close);
        setText("tbarch-result-title", title);
        setText("tbarch-result-desc", desc);

        const file = $("tbarch-result-file");
        const exported = scraper.phase === "done" ? scraper.lastExport : null;
        file.hidden = !exported;
        if (exported) {
            const text = `${exported.filename} · ${formatBytes(exported.size)}`;
            if (file.textContent !== text) {
                file.textContent = text;
            }
            file.title = exported.filename;
        }
    }

    function paintPanel() {
        const panel = $("tbarch-panel");
        if (!panel) {
            return;
        }

        const posts = scraper.posts.size;
        const comments = countComments();
        const pagesTotal = scraper.page.total;
        const pagesDone = Math.min(scraper.page.done, pagesTotal || scraper.page.done);
        const errors = scraper.errors.length;
        const percent = Math.min(computePercent(), 100);
        const active = scraper.phase !== "idle";

        setText("tbarch-st-pages", pagesTotal > 0 ? `${pagesDone}/${pagesTotal}` : "-");
        setText("tbarch-st-posts", String(posts));
        setText("tbarch-st-comments", String(comments));
        setText("tbarch-st-errors", String(errors));

        const errorStat = $("tbarch-stat-errors");
        if (errorStat) {
            errorStat.classList.toggle("error", errors > 0);
        }

        refreshMeta();

        const run = $("tbarch-run");
        run.hidden = !active;
        run.dataset.state = statusClass() || "idle";
        $("tbarch-hint").hidden = active;
        $("tbarch-bar").style.width = `${percent}%`;
        setText("tbarch-phase", phaseLabel());
        setText("tbarch-percent", `${Math.round(percent)}%`);
        setText("tbarch-elapsed", scraper.startedAt ? formatDuration(elapsedMs()) : "");

        const statusNode = $("tbarch-status");
        if (statusNode) {
            const label = statusNode.querySelector("em");
            if (label) {
                label.textContent = statusText();
            }
            statusNode.className = `tbarch-status ${statusClass()}`;
        }

        paintSteps();
        paintLog();
        paintResult();
        updateButtons();
        queueReposition();
    }

    function phaseLabel() {
        switch (scraper.phase) {
            case "posts":
                return `抓取楼层 ${scraper.page.done}/${scraper.page.total || "?"} 页`;
            case "comments":
                return `补全楼中楼 ${scraper.comment.done}/${scraper.comment.total} 层`;
            case "done":
                return "抓取完成";
            case "cancelled":
                return "已取消";
            case "error":
                return "已停止";
            default:
                return "准备就绪";
        }
    }

    function statusText() {
        switch (scraper.phase) {
            case "posts":
                return "抓取中";
            case "comments":
                return "补全中";
            case "done":
                return "已完成";
            case "cancelled":
                return "已取消";
            case "error":
                return "失败";
            default:
                return "准备就绪";
        }
    }

    function statusClass() {
        switch (scraper.phase) {
            case "posts":
            case "comments":
                return "running";
            case "done":
                return "success";
            case "cancelled":
                return "warn";
            case "error":
                return "error";
            default:
                return "";
        }
    }

    function updateButtons() {
        const start = $("tbarch-start");
        const cancel = $("tbarch-cancel");
        const download = $("tbarch-download");
        if (!start || !cancel || !download) {
            return;
        }

        start.disabled = scraper.running;
        if (scraper.running) {
            setHtmlOnce(start, "run", `<span class="tbarch-spin"></span><span>抓取中…</span>`);
        } else if (scraper.phase !== "idle") {
            setHtmlOnce(start, "again", `${ICONS.refresh}<span>重新抓取</span>`);
        } else {
            setHtmlOnce(start, "start", `${ICONS.play}<span>开始抓取</span>`);
        }

        cancel.hidden = !scraper.running;
        download.hidden = !scraper.result || scraper.running;
        setHtmlOnce(
            download,
            scraper.exportFormat,
            `${ICONS.download}<span>下载 ${scraper.exportFormat === "lite" ? "TXT" : "JSON"}</span>`,
        );

        for (const button of formatButtons()) {
            button.disabled = scraper.running;
        }
        for (const pill of document.querySelectorAll("#tbarch-limit-chips .tbarch-pill")) {
            pill.disabled = scraper.running;
        }
        const concurrencyInput = $("tbarch-concurrency");
        const limitInput = $("tbarch-page-limit");
        if (concurrencyInput) {
            concurrencyInput.disabled = scraper.running;
        }
        if (limitInput) {
            limitInput.disabled = scraper.running;
        }

        const navButton = $("tbarch-nav-btn");
        if (navButton) {
            const percent = Math.round(Math.min(computePercent(), 100));
            navButton.classList.toggle("running", scraper.running);
            navButton.classList.toggle("done", !scraper.running && scraper.phase === "done");
            navButton.style.setProperty("--tbarch-p", `${scraper.running ? percent : 0}%`);
            setText("tbarch-nav-tx", scraper.running ? `${percent}%` : "导出");
        }
    }

    // ---------- 设置持久化 ----------

    function parseTid() {
        const matched = location.pathname.match(/^\/p\/(\d+)/);
        return matched ? Number(matched[1]) : 0;
    }

    function readNumberInput(id, fallback, min, max) {
        const node = $(id);
        if (!node) {
            return fallback;
        }
        const value = Number(node.value);
        if (!Number.isFinite(value)) {
            return fallback;
        }
        return Math.min(Math.max(Math.trunc(value), min), max);
    }

    function readStoredNumber(key, fallback, min, max) {
        try {
            if (typeof GM_getValue === "function") {
                const value = Number(GM_getValue(key, fallback));
                if (Number.isFinite(value)) {
                    return Math.min(Math.max(Math.trunc(value), min), max);
                }
            }
        } catch (error) {
            // ignore
        }
        return fallback;
    }

    function persistSettings() {
        const concurrency = readNumberInput("tbarch-concurrency", 3, 1, 6);
        const pageLimit = readNumberInput("tbarch-page-limit", 0, 0, 99999);
        try {
            if (typeof GM_setValue === "function") {
                GM_setValue("tbarch-concurrency", concurrency);
                GM_setValue("tbarch-page-limit", pageLimit);
            }
        } catch (error) {
            // ignore
        }
    }

    function readStoredFormat() {
        try {
            if (typeof GM_getValue === "function") {
                return GM_getValue("tbarch-export-format", "full") === "lite" ? "lite" : "full";
            }
        } catch (error) {
            // ignore
        }
        return "full";
    }

    function persistFormat() {
        try {
            if (typeof GM_setValue === "function") {
                GM_setValue("tbarch-export-format", scraper.exportFormat);
            }
        } catch (error) {
            // ignore
        }
    }

    function setExportFormat(format, silent = false) {
        scraper.exportFormat = format === "lite" ? "lite" : "full";
        for (const button of formatButtons()) {
            const active = button.dataset.format === scraper.exportFormat;
            button.classList.toggle("active", active);
            button.setAttribute("aria-checked", String(active));
        }
        if (!silent) {
            persistFormat();
        }
        updateButtons();
    }

    // ---------- 启动 ----------

    function boot() {
        const tid = parseTid();
        if (!tid) {
            return;
        }
        console.info(`[贴吧存档] v${VERSION} 已加载，tid=${tid}`);

        const ensureButton = () => {
            const button = $("tbarch-nav-btn");
            if (button && button.isConnected) {
                return;
            }
            buildNavButton();
        };

        ensureButton();

        // 贴吧顶栏可能被前端框架重渲染，持续监听以便按钮被移除后重新注入
        if (typeof MutationObserver !== "undefined" && document.body) {
            let scheduled = false;
            const observer = new MutationObserver(() => {
                if (scheduled) {
                    return;
                }
                scheduled = true;
                setTimeout(() => {
                    scheduled = false;
                    ensureButton();
                }, 300);
            });
            observer.observe(document.body, { childList: true, subtree: true });
        }

        // 找不到顶部导航栏时，退化为右下角悬浮按钮
        setTimeout(() => {
            if (!$("tbarch-nav-btn")) {
                console.warn("[贴吧存档] 未找到顶部导航栏，改用悬浮按钮", {
                    topBar: !!document.querySelector("#top-bar"),
                    rightMenu: !!document.querySelector(".right-menu"),
                    addPost: !!document.querySelector(".add-post"),
                });
                buildNavButton(true);
            }
        }, 8000);

        if (typeof GM_registerMenuCommand === "function") {
            GM_registerMenuCommand("打开导出面板（贴吧存档）", () => {
                if (buildNavButton() || buildNavButton(true)) {
                    openPanel();
                }
            });
            GM_registerMenuCommand("抓取当前帖子（贴吧存档）", () => {
                if (buildNavButton() || buildNavButton(true)) {
                    openPanel();
                    startScrape();
                }
            });
        }
    }

    if (typeof document !== "undefined") {
        if (document.readyState === "loading") {
            document.addEventListener("DOMContentLoaded", boot, { once: true });
        } else {
            boot();
        }
    }
})();