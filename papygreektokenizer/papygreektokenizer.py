from sys import exit
import traceback
from functools import reduce
from itertools import groupby, chain
from collections.abc import Iterable, Generator
from io import BytesIO
from datetime import datetime
import regex as re
import glob
from lxml import etree

import unicodedata
from .wordmatcher import best_match
from .place import convert_place

punct = list(",..·;;·.§")
sent_punct = list(".·;;·.§")
bracket_symbols = r"[‹›〚〛#\(\)\|❛❜¯\_\\/^~¯↕→←\{\}\[\]\'｣｢”§°]+"

xml_atts = lambda x: (" " if len(x) else "") + (
    " ".join([f'{k.split("}")[-1]}="{v}"' for k, v in x.items()])
)
no_ns_atts = lambda x: {k.split("}")[-1]: v for k, v in x.items()}
flat_dict = lambda x: "|".join([f'{k.split("}")[-1]}={v}' for k, v in x.items()])
compose_inner_func = lambda f, g: lambda x: g(f(x))
composer = lambda *x: reduce(compose_inner_func, x, lambda x: x)
add_ud = lambda x: "".join(
    [y + "̣" if unicodedata.normalize("NFD", y)[0].lower().isalpha() else y for y in x]
)
transpose = lambda m: m and [
    list(map(lambda r: r[0], m)),
    *transpose(list(filter(len, map(lambda r: r[1:], m)))),
]
flat_list = lambda x: [item for sublist in x for item in sublist]
parse_flat_atts = lambda a: {x.split("=")[0]: x.split("=")[1] for x in a.split("|")}
transform_error = lambda f, el, atts, where: exit(
    f"Error in {where}: no bracket for {el}, {atts}\n {f}"
)
str_none = lambda i: i or ""


def get_edition_xml_str(xml_dom: etree._Element) -> str:
    try:
        return etree.tostring(xml_dom.xpath(".//div[@type='edition']")[0], encoding="utf-8").decode()  # type: ignore
    except:
        return ""


def get_match(x: str, r: str) -> str:
    if match := re.search(r, x):
        return match.group(0)
    return ""


def flatten_deep(xs: list | str) -> Generator:
    for x in xs:
        if isinstance(x, Iterable) and not isinstance(x, (str, bytes)):
            yield from flatten_deep(x)
        else:
            yield x


def re_recursive(p: str, r: str, s: str) -> str:
    while 1:
        s, n = re.subn(p, r, s)
        if not n:
            return s
    return ""


def remove_ns(xml_dom: etree._Element) -> etree._Element:
    query = "descendant-or-self::*[namespace-uri()!='']"
    for element in xml_dom.xpath(query):
        element.tag = etree.QName(element).localname
    etree.cleanup_namespaces(xml_dom, top_nsmap=None, keep_ns_prefixes=None)
    return xml_dom


def stringify_children(node: etree._Element) -> str:
    return "".join(
        chunk
        for chunk in chain(
            (node.text,),
            chain(
                *(
                    (
                        etree.tostring(
                            child, encoding="utf-8", with_tail=False  # type: ignore
                        ).decode(),
                        child.tail,
                    )
                    for child in node.getchildren()
                )
            ),
            (node.tail,),
        )
        if chunk
    )


def create_versions(data: dict) -> dict:
    """
        preformat
        transform_tags
        normalize_and_split
        bracketify_words
        transform_brackets
        stack_alternatives
    ->  create_versions
    """

    state = data["state"]

    def remove_symbols(t: str) -> str:
        replacements = [
            ("⸦[^⸧]+⸧", ""),
            ("༺[^༻]+༻", ""),
            ("⧙[^⧘]+⧘", "|"),
            ("⦓[^⦔]+⦔", ""),
            ("⧛[^⧚]+⧚", ""),
        ]
        for x, y in replacements:
            t = re.sub(x, y, t)
        return t

    def plain(x: str, diplomatic) -> str:
        diplomatic_symbols = (
            [
                "¨",
                "´",
                "῾",
                "`",
                "^",
                "᾿",
                "*",
                "-",
                "?",
                "✕",
                "╱",
                "—",
                "⸍",
                "†",
                "⳨",
                "☧",
                "✓",
                "‧",
                "∶",
                "｜",
                "⸒",
                "•",
            ]
            if diplomatic
            else []
        )
        return "".join(
            [
                unicodedata.normalize("NFD", a)[0].lower()
                for a in x
                if a.isalpha() or a in punct + ["_"] + diplomatic_symbols
            ]
        )

    def pre_plain(t: str, diplomatic: bool) -> str:
        t = re.sub(r"\$(?=.+)", "", t)
        if not diplomatic:
            t = re.sub(r"\*(.*?)\*", "", t)
        return re.sub(r"(｢[^｣]+｣)+", "_", t)

    def remove_gap_marker(t: str) -> str:
        return re.sub(r"[｢｣]+", "", t)

    def version_type(k: str) -> str:
        if not ("reg" in k or "scribaldel" in k or "corr" in k or "rdg" in k):
            return "orig"
        elif not ("rdg" in k or "scribaldel" in k):
            return "reg"
        return "var"

    def get_flag_and_info(t: str) -> tuple | str:
        nonlocal state
        flag = ""
        info = []
        app_type = []
        paths = re.findall(r"(>[a-z]+\[[0-9]+\])", t)
        for p in paths:
            el = re.search("[0-9]+", p)
            if not el:
                return ""
            el_id = int(el.group(0))
            atts = state["elements"][el_id].attrib
            if app_t := atts.get("type", ""):
                app_type.append(app_t)
            if app_type:
                if atts.get("cert", ""):
                    app_type[-1] += "?"
            if resp := atts.get("resp", ""):
                info.append(resp)

            if "reg" in p:
                flag += "r"
            elif "orig" in p:
                flag += "o"
            elif "corr" in p:
                flag += "c"
            elif "sic" in p:
                flag += "s"
            elif "scribaladd" in p:
                flag += "a"
            elif "scribaldel" in p:
                flag += "d"
            elif "lem" in p:
                flag += "l"
            elif "rdg" in p:
                flag += "g"

        t = re.sub(r"(>[a-z]+\[[0-9]+\])+", "", t)
        return t, flag, "/".join(app_type), "/".join(info)

    def get_lang(t: str, lang: str) -> str:
        if "⸦" in t:
            if match := re.search("(?<=⸦).+?(?=⸧)", t):
                return match.group(0)
        return lang

    def get_hand(t: str, hand: str, aow_n: int) -> tuple:
        if "༺" in t:  # handshift
            hand_prev = hand
            hand = re.findall(r"(?<=༺).+?(?=༻)", t)[-1]
            if hand_prev != hand:
                aow_n += 1
        return hand, aow_n

    def get_line(t: str, line: str, line_rend: str) -> tuple:
        if "⧙" in t:  # word-medial lb
            match = re.search("(?<=⧙).+?(?=⧘)", t)
            if match:
                line, line_rend = match.group(0).split("⟩")
        return line, line_rend

    def get_num(t: str, num: str, num_rend: str) -> tuple:
        if "⦓" in t:  # num
            if "✓" in t:
                num_rend = "tick"
                t.replace("✓", "")
            if num_match := re.search("(?<=⦓).+?(?=⦔)", t):
                num = num_match.group(0)
        return num, num_rend

    lang = "grc"
    document_lang = "grc"
    prev_n = 1
    n = 1
    hand = "m1"
    aow_n = 1
    sentence_n = 1
    textpart = []
    line = "1"
    line_rend = ""

    token_data = []
    increment_sentence = 0
    cancel_increment = 0

    diplomatic = data["state"]["diplomatic"]

    for t in data["tokens"]:
        info = ""
        skip = 0
        num = ""
        num_rend = ""
        lang = document_lang

        if increment_sentence:
            sentence_n += 1
            prev_n = n
            n = 1
            increment_sentence = 0

        if cancel_increment:
            n = prev_n
            sentence_n -= 1
            cancel_increment = 0

        if type(t) == str:
            if "⸨" in t:
                atts = parse_flat_atts(t[2:-1])
                if "lang" in atts:
                    document_lang = atts["lang"]
                    lang = document_lang
                else:
                    inc_atts = []
                    if "n" in atts:
                        inc_atts.append(atts["n"])
                    if "subtype" in atts:
                        inc_atts.append(atts["subtype"])
                    textpart.append(".".join(inc_atts))
                skip = 1

            elif "⸩" in t:
                try:
                    textpart.pop()
                except:
                    pass
                skip = 1

            elif "⧛" in t:
                try:
                    line, line_rend = t[1:-1].split("⟩")
                    skip = 1
                except:
                    print(t)
                    print(data["state"])
                    exit()

            elif "figure-" in t:
                if fig_match := re.search("(?<=figure-)[0-9]+", t):
                    info = state["figures"][int(fig_match.group(0)) - 1]

            elif "note-" in t:
                if note_match := re.search("(?<=note-)[0-9]+", t):
                    info = state["notes"][int(note_match.group(0)) - 1]

            else:
                if any(s in t for s in sent_punct):
                    increment_sentence = 1

                if "§" in t:
                    skip = 1

                if "°" in t:
                    cancel_increment = 1
                    skip = 1

                lang = get_lang(t, lang)
                hand, aow_n = get_hand(t, hand, aow_n)
                line, line_rend = get_line(t, line, line_rend)
                num, num_rend = get_num(t, num, num_rend)

            t = remove_symbols(t)

            if not re.sub(bracket_symbols, "", t).replace("$", ""):
                skip = 1

            plain_t = plain(pre_plain(t, diplomatic), diplomatic)
            t = remove_gap_marker(t)

            if not skip:
                token_data.append(
                    {
                        "orig_form": t,
                        "orig_plain": plain_t,
                        "orig_flag": "",
                        "orig_app_type": "",
                        "orig_num": num,
                        "orig_num_rend": num_rend,
                        "orig_lang": lang,
                        "orig_info": info,
                        "orig_lemma": None,
                        "orig_postag": None,
                        "orig_relation": None,
                        "orig_head": None,
                        "reg_form": t,
                        "reg_plain": plain_t,
                        "reg_flag": "",
                        "reg_app_type": "",
                        "reg_num": num,
                        "reg_num_rend": num_rend,
                        "reg_lang": lang,
                        "reg_info": info,
                        "reg_lemma": None,
                        "reg_postag": None,
                        "reg_relation": None,
                        "reg_head": None,
                        "vars": [],
                        "n": n,
                        "line": line,
                        "line_rend": line_rend,
                        "sentence_n": sentence_n,
                        "hand": hand,
                        "aow_n": aow_n,
                        "textpart": "/".join(textpart),
                        "artificial": None,
                        "insertion_id": None,
                    }
                )
                n += 1

        else:
            for t_word in t:
                info = ""
                num = ""
                num_rend = ""
                lang = document_lang
                reg_collected = 0
                var_data = []
                orig_data = {}
                reg_data = {}
                have_reg = 0
                have_orig = 0
                prev_n = n

                if increment_sentence:
                    sentence_n += 1
                    n = 1
                    increment_sentence = 0

                for t_version in t_word.split("⧽"):
                    v = version_type(t_version)

                    if v == "reg":
                        if reg_collected:
                            v = "var"
                        reg_collected = 1

                    t_version, flag, app_type, info = get_flag_and_info(t_version)

                    if "⧛" in t_version:
                        line, line_rend = t_version[1:-1].split("⟩")

                    elif "figure-" in t_version:
                        info_n = 0
                        if info_n_match := re.search("(?<=figure-)[0-9]+", t_version):
                            info_n = info_n_match.group(0)
                        info += "/" + state["figures"][int(info_n) - 1]

                    elif "note-" in t_version:
                        note_n = 0
                        if note_n_match := re.search("(?<=note-)[0-9]+", t_version):
                            note_n = note_n_match.group(0)
                        info += "/" + state["notes"][int(note_n) - 1]

                    else:
                        if any(s in t_version for s in sent_punct) and v in [
                            "orig",
                            "reg",
                        ]:
                            increment_sentence = 1

                        lang = get_lang(t_version, lang)
                        if v != "var":
                            hand, aow_n = get_hand(t_version, hand, aow_n)
                            line, line_rend = get_line(t_version, line, line_rend)
                        num, num_rend = get_num(t_version, num, num_rend)

                    t_version = remove_symbols(t_version)

                    very_plain = re.sub(bracket_symbols, "", t_version)

                    if very_plain:
                        if v == "reg":
                            have_reg = very_plain
                        elif v == "orig":
                            have_orig = very_plain

                    plain_t_version = plain(
                        pre_plain(t_version, diplomatic), diplomatic
                    )
                    t_version = remove_gap_marker(t_version)

                    if v == "orig":
                        orig_data = {
                            "orig_form": t_version,
                            "orig_plain": plain_t_version,
                            "orig_flag": flag,
                            "orig_app_type": app_type,
                            "orig_num": num,
                            "orig_num_rend": num_rend,
                            "orig_lang": lang,
                            "orig_info": info,
                            "orig_lemma": None,
                            "orig_postag": None,
                            "orig_relation": None,
                            "orig_head": None,
                        }
                    elif v == "reg":
                        reg_data = {
                            "reg_form": t_version,
                            "reg_plain": plain_t_version,
                            "reg_flag": flag,
                            "reg_app_type": app_type,
                            "reg_num": num,
                            "reg_num_rend": num_rend,
                            "reg_lang": lang,
                            "reg_info": info,
                            "reg_lemma": None,
                            "reg_postag": None,
                            "reg_relation": None,
                            "reg_head": None,
                        }
                    else:
                        var_data.append(
                            {
                                "form": t_version,
                                "plain": plain_t_version,
                                "flag": flag,
                                "app_type": app_type,
                                "info": info,
                                "num": num,
                                "num_rend": num_rend,
                                "lang": lang,
                            }
                        )
                if not have_reg:
                    have_reg = "$"
                if have_orig and not (have_orig == have_reg == "$"):
                    if not reg_data:
                        reg_data = {
                            k.replace("orig", "reg"): v for k, v in orig_data.items()
                        }

                    common_data = {
                        "vars": var_data,
                        "n": n,
                        "line": line,
                        "line_rend": line_rend,
                        "sentence_n": sentence_n,
                        "hand": hand,
                        "aow_n": aow_n,
                        "textpart": "/".join(textpart),
                        "artificial": None,
                        "insertion_id": None,
                    }

                    token_data.append(orig_data | reg_data | common_data)

                    n += 1

        # TODO: Do sentence division more robustly

    return {"tokens": token_data, "state": data["state"]}


def stack_alternatives(data: dict) -> dict:
    """
        preformat
        transform_tags
        normalize_and_split
        bracketify_words
        transform_brackets
    ->  stack_alternatives
        create_versions
    """

    def move_brackets(ts: list) -> list:
        for i, t in enumerate(ts):
            t_parts = t.split("⧽")
            for k, part in enumerate(t_parts):
                t_parts[k] = re.sub(r"(^[^>]+)((>[a-zA-Z]+\[[0-9]+\])+)", r"\2\1", part)
            ts[i] = "⧽".join(t_parts)

        return ts

    def group_recu(ts: list, rg: str) -> list:
        res = []
        for i, j in groupby(ts, lambda x: get_match(x, rg)):
            k = list(j)
            if not i:
                res += k
                continue
            res += [group_recu(k, re.escape(i) + r".*?(>([a-z]+)\[[0-9]+\])")]
        return res

    def stack_variants(x: list | str) -> list | str:
        my = []
        if type(x) == str:
            return x
        elif type(x) == list:
            if (
                len(x) > 1
                and all([type(y) == list for y in x])
                and all([type(y) == str for y in flat_list(x)])
            ):
                n = best_match(x, clean_regex=r"(>[a-z]+\[[0-9]+\])+")
                return [
                    "⧽".join(
                        [re.sub(r">(app|choice|subst)\[[0-9]+\]", "", x) for x in l]
                    )
                    for l in zip(*n)
                ]

            elif any([type(y) == list for y in x]) and all(
                [type(y) == str for y in flat_list(x)]
            ):
                return list(flatten_deep(x))

            for i in x:
                my += [stack_variants(i)]
        return my

    grouped_tokens = group_recu(data["tokens"], r"(?<!>)>(app|choice|subst)\[[0-9]+\]")
    for i, g in enumerate(grouped_tokens):
        if type(g) == list:
            old_g = []
            c = 0
            while g != old_g:
                old_g = g
                g = stack_variants(g)
                c += 1

            grouped_tokens[i] = move_brackets(list(g))

    return {"tokens": grouped_tokens, "state": data["state"]}


def transform_brackets(data: dict) -> dict:
    """
        preformat
        transform_tags
        normalize_and_split
        bracketify_words
    ->  transform_brackets
        stack_alternatives
        create_versions
    """

    element_stack = data["state"]["elements"]
    tokens = data["tokens"]
    cur_file = data["state"]["file"]

    def bracket_grammar(tag: str, atts: dict) -> list | None:
        match tag:
            case "supplied":
                match atts.get("reason", ""):
                    case "omitted":
                        return ["‹", "›"]
                    case "lost":
                        if atts.get("evidence", "") == "parallel":
                            return ["_[", "]_"]
                        else:
                            return ["[", "]"]
                    case "undefined":
                        return ["|_", "_|"]
            case "surplus":
                return ["{", "}"]
            case "del":
                match atts.get("rend", ""):
                    case "slashes":
                        s = "/"
                    case "cross-strokes":
                        s = "✕"
                    case _:
                        s = ""
                return [f"〚{s}", "〛"]

            case "add":
                match atts.get("place", ""):
                    case "above":
                        return ["\\", "/"]
                    case "below" | "bottom":
                        return ["/", "\\"]
                    case "left":
                        return ["||←:", "||"]
                    case "right":
                        return ["||→:", "||"]
                    case "interlinear":
                        return ["||↕:", "||"]
                    case "margin":
                        if atts.get("rend", "") == "underline":
                            return ["‹_", "_›"]
                        elif atts.get("rend", "") == "sling":
                            return ["‹|", "|›"]

            case "hi":
                match atts.get("rend", ""):
                    case "supraline":
                        return ["¯", "¯"]
                    case "tall":
                        return ["~||", "||~"]
                    case "superscript":
                        return ["|^", "^|"]
                    case "above":
                        return ["|^", "^|"]
                    case "subscript":
                        return ["\\|", "|/"]
                    case "supraline-underline":
                        return ["¯_", "_¯"]
                    case "underline" | "underlined":
                        return ["_", "_"]
                    case "diaeresis":
                        return ["", "(¨)"]
                    case "acute":
                        return ["", "(´)"]
                    case "asper":
                        return ["", "(῾)"]
                    case "grave":
                        return ["", "(`)"]
                    case "circumflex":
                        return ["", "(^)"]
                    case "lenis":
                        return ["", "(᾿)"]
                    case _:
                        return ["", ""]

            case "q":
                return ["❛", "❜"]
            case "expan":
                return ["(", ")"]
            case "ex":
                return ["(", ")"]
            case "abbr":
                return ["(|", "|)"]
            case "num":
                val = atts.get("value", "?") or "?"
                tick = "✓" if atts.get("rend", "") == "tick" else ""
                return ["", f"⦓{val}{tick}⦔"]

            case "foreign":
                l = atts.get("lang", "")
                return ["", f"⸦{l}⸧"]

            case "l" | "lb":
                brackets = ["⧙", "⧘"] if atts.get("break", "") == "no" else ["⧛", "⧚"]
                return [
                    f' {brackets[0]}{atts.get("n", "?")}⟩{atts.get("rend", "")}{brackets[1]} ',
                    "",
                ]

            case "unclear" | "lg" | "seg":
                return ["", ""]

    def bracket_transformer(br: str, stack_id: int) -> str:
        nonlocal element_stack
        m = 0 if br == ">" else 1
        el = element_stack[stack_id]
        tag = el.tag
        atts = no_ns_atts(el.attrib)
        u = "?" if (m and (atts.get("cert", "") or atts.get("precision"))) else ""

        if tags := bracket_grammar(tag, atts):
            return u + tags[m]

        elif tag in [
            "app",
            "choice",
            "subst",
            "lem",
            "rdg",
            "reg",
            "orig",
            "scribaladd",
            "scribaldel",
            "corr",
            "sic",
        ]:
            if not m:
                return f"{br}{tag}[{stack_id}]"
            return ""
        else:
            transform_error(cur_file, tag, atts, "bracket_transform")
        return ""

    transformed_tokens = [
        re.sub(
            r"([><])\[([0-9]+)\]",
            lambda x: bracket_transformer(x.group(1), int(x.group(2))),
            t,
        )
        for t in tokens
    ]

    # We need to stringify again, then split again...
    tokens_str = " ".join(transformed_tokens)
    tokens_str = re.sub(r"\s+", " ", tokens_str).strip()

    return {"tokens": tokens_str.split(), "state": data["state"]}


def bracketify_words(data: dict) -> dict:
    """
        preformat
        transform_tags
        normalize_and_split
    ->  bracketify_words
        transform_brackets
        stack_alternatives
        create_versions
    """

    tokens = data["tokens"]

    for i, t in enumerate(tokens):
        req_closings = []
        brackets = r"([><]\[[0-9]+\])"
        ms = re.findall(brackets, t)
        for s in ms:
            if s[0] == ">":
                req_closings.insert(0, "<" + s[1:])
            elif s[0] == "<":
                if req_closings[0] == s:
                    req_closings = req_closings[1:]

        if req_closings:
            tokens[i] += "".join(req_closings)
            req_openings = []
            for r in req_closings:
                req_openings.insert(0, ">" + r[1:])
            if req_openings:
                try:
                    tokens[i + 1] = "".join(req_openings) + tokens[i + 1]
                except:
                    pass

    return {"tokens": tokens, "state": data["state"]}


def normalize_and_split(data: dict) -> dict:
    """
        preformat
        transform_tags
    ->  normalize_and_split
        bracketify_words
        transform_brackets
        stack_alternatives
        create_versions
    """

    xml_str = data["text"]
    xml_str = re_recursive(rf"(>\[[0-9]+\])(\s+)", r"\2\1", xml_str)  # moving spaces
    xml_str = re_recursive(rf"(\s+)(<\[[0-9]+\])", r"\2\1", xml_str)  # moving spaces
    xml_str = re.sub(r"\s+⧙", "⧙", xml_str)  # non-breaking lbs
    xml_str = re.sub(r"⧘\s+", "⧘", xml_str)  # non-breaking lbs

    # Craseis
    xml_str = re.sub(
        r"([κτχθ])([αεοηωυ]*)([ἀἐἠἰὀὐὠᾀᾐᾠῤἄἔἤἴὄὔὤᾄᾔᾤἂἒἢἲὂὒὢᾂᾒᾢἆἦἶὖὦᾆᾖᾦ])",
        r"\1ʼ \2\3",
        xml_str,
    )
    xml_str = re.sub(r"\s+", " ", xml_str).strip()  # normalize spaces
    xml_str = re.sub(r" (⸩.*?⸨[^ ]+)(⧙[^ ]+)", r"\2 \1", xml_str)  # bugfix
    xml_str = re.sub(r"(⧙[^⧘]+?⧘)(⧛)", " \2", xml_str)  # bugfix 2

    return {"tokens": xml_str.split(), "state": data["state"]}


def transform_tags(data: dict) -> dict:
    """
        preformat
    ->  transform_tags
        normalize_and_split
        bracketify_words
        transform_brackets
        stack_alternatives
        create_versions
    """

    root = data["root"]
    state = data["state"]
    things_i = 0
    things_l = []
    unclear = 0
    diplomatic = data["state"]["diplomatic"]

    def symbolify(el: etree._Element, unclear: int) -> str:
        nonlocal state
        nonlocal diplomatic
        tag = el.tag
        atts = no_ns_atts(el.attrib)
        match tag:
            case "lb" | "l":
                brackets = ["⧙", "⧘"] if atts.get("break", "") == "no" else ["⧛", "⧚"]
                return f' {brackets[0]}{atts.get("n", "?")}⟩{atts.get("rend", "")}{brackets[1]} '

            case "milestone":
                rend = atts.get("rend", "")
                return f'*{rend or "milestone"}*'

            case "g":
                g_type = atts.get("type", "")
                u = "(?)" if unclear else ""
                match g_type:
                    case "x":
                        return f"*✕{u}*"
                    case "slanting-stroke":
                        return f"*╱{u}*"
                    case "extension":
                        return f"*—{u}*"
                    case "apostrophe":
                        return f"*⸍{u}*"
                    case "stauros":
                        return f"*†{u}*"
                    case "rho-cross":
                        return f"*⳨{u}*"
                    case "chirho":
                        return f"*☧{u}*"
                    case "check":
                        return f"*✓{u}*"
                    case "middot":
                        return f"*‧{u}*"
                    case "dipunct":
                        return f"*∶{u}*"
                    case "long-vertical-bar":
                        return f"*｜{u}*"
                    case "diastole":
                        return f"*⸒{u}*"
                    case "dot":
                        return f"*•{u}*"
                    case "unintelligible":
                        return f"*?{u}*"
                    case _:
                        return f"*{g_type}{u}*"

            case "gap" | "space":
                pd = "․"
                brackets = {
                    "lost": ["[", "]"],
                    "omitted": ["‹", "›"],
                    "illegible": ["", ""],
                    "ellipsis": ["", ""],
                    "none": ["", ""],
                }
                units = {
                    "character": "",
                    "line": "lin",
                    "column": "col",
                    "none": "",
                }

                sp = "vac" if tag == "space" else "_"
                desc = atts.pop("desc", "").lower()
                if desc:
                    if desc == "non transcribed":
                        desc = f"{pd}nontr"
                    elif desc == "vestiges":
                        desc = f"{pd}vestig"
                    else:
                        desc = f"{pd}{desc}"

                ell = f"{pd}ell" if atts.get("reason", "") == "ellipsis" else ""

                ca = f"{pd}ca" if atts.get("precision", "") else ""

                quantity = atts.pop("quantity", "")
                atleast = atts.pop("atLeast", "")
                atmost = atts.pop("atMost", "")

                ext = "?" if atts.get("extent", "") else ""
                if quantity:
                    ext = quantity
                elif atleast and atmost:
                    ext = atleast + "-" + atmost

                br = brackets[atts.get("reason", "none")]

                prec = (
                    "?" if (atts.get("precision", "") or atts.get("cert", "")) else ""
                )
                unit = units[atts.get("unit", "none")]

                return f"｢{br[0]}{sp}{desc}{ell}{ca}{pd}{ext}{unit}{prec}{br[1]}｣"

            case "note":
                note = []
                note_text = atts.pop("text", "")
                note_ref = atts.pop("ref_n", "")
                note_ref_text = atts.pop("ref_text", "")
                if note_text:
                    note.append(note_text)
                if note_ref:
                    note.append(f"(ref:{note_ref})")
                if note_ref_text:
                    note.append(f"({note_ref_text})")
                state["notes"].append(" ".join(note))
                return f' note-{len(state["notes"])} '

            case "figure":
                state["figures"].append(
                    atts.get("desc", "") + ("(?)" if atts.get("cert", "") else "")
                )
                return f' figure-{len(state["figures"])} '

            case "handShift":
                n = atts.pop("new", "")
                u = "?" if atts.get("cert", "") else ""
                return f"༺{n}{u}༻"

            case "supplied" | "unclear" | "ab" | "del" | "div" | "hi" | "add" | "q" | "w" | "r":
                return ""

            case _:
                if not diplomatic:
                    transform_error(state["file"], tag, atts, "symbolize")
                else:
                    return ""
        return ""

    def pre_tokenize(s: str, unclear: int) -> str:
        s = add_ud(s) if unclear else s
        return re.sub(f'([{"".join(punct)}])', r" \1 ", s)

    def transformer(root: etree._Element) -> str:
        nonlocal things_i
        nonlocal things_l
        nonlocal unclear
        nonlocal state
        transf = ""
        unclear = 1 if root.tag == "unclear" else unclear
        if not (len(root) or root.text):  # <el/>
            transf += symbolify(root, unclear)
        else:
            if root.tag == "div":
                atts = no_ns_atts(root.attrib)
                l = root.attrib.pop("lang", "")
                atts.pop("space", "")
                atts.pop("type", "")
                if l:
                    transf += f" ⸨[lang={l}] "
                else:
                    transf += f" ⸨[{flat_dict(atts)}] "
            else:
                state["elements"].append(root)
                things_l.append(things_i)

                sep = " " if root.tag in ["app", "choice", "subst"] else ""

                transf += f"{sep}>[{things_i}]"
                things_i += 1
            if root.text:
                transf += pre_tokenize(root.text, unclear)

            if len(root):
                for elem in root.iterchildren(tag=None):
                    transf += transformer(elem)
                    if elem.tail:
                        transf += pre_tokenize(elem.tail, unclear)

            if root.tag == "div":
                transf += " ⸩ "
            else:
                transf += f"<[{things_l[-1]}]"
                things_l.pop()
        unclear = 0 if root.tag == "unclear" else unclear
        return transf

    transformed = transformer(root)

    return {"text": transformed, "state": state}


def preformat(data: dict) -> dict:
    """
    ->  preformat
        transform_tags
        normalize_and_split
        bracketify_words
        transform_brackets
        stack_alternatives
        create_versions
    """

    def remove_keeping_tail(node):
        if node.tail:
            previous = node.getprevious()
            if (
                previous is not None
            ):  # if there is a previous sibling it will get the tail
                if previous.tail is None:
                    previous.tail = node.tail
                else:
                    previous.tail = previous.tail + node.tail
            else:  # The parent will get the tail as text
                parent = node.getparent()
                if parent.text is None:
                    parent.text = node.tail
                else:
                    parent.text = parent.text + node.tail

        node.getparent().remove(node)

    xml_str = data["text"]
    replacements = [
        (r"<[\/]?ab>", ""),
        (r"<num[^>]*\/>", ""),
        (r"\s+<\/ex>", "-?</ex>"),
        (r"</lem>([\s\S]*?)<rdg", "</lem><rdg"),
        (r' break="no"/><choice', "/><choice"),
        (r' break="no"/><app', "/><app"),
        (
            r"(<\/(lem|rdg|sic|corr|orig|reg|subst|choice|app)>)(<(lem|rdg|sic|corr|orig|reg|subst|choice|app))",
            r"\1 \3",
        ),
        (
            r"(<(lem|rdg|sic|corr|orig|reg|subst|choice|app)[^>]*\/>)(<(lem|rdg|sic|corr|orig|reg|subst|choice|app))",
            r"\1 \3",
        ),
        (
            r"(<\/(lem|rdg|sic|corr|orig|reg|subst|choice|app)[^>]*>)(<(lem|rdg|sic|corr|orig|reg|subst|choice|app))",
            r"\1 \3",
        ),
        (r"<\/add><del", "</add> <del"),
        (r"(<add[^>]*>)(<del)", r"\1 \2"),
        (r"(<add[^>]*>)(<del)", r"\1 \2"),
        (r"(<lb[^>]+>)", r" \1 "),
        (r'(\s*)(<lb[^\/]+break="no"[^\/]*\/>)(\s*)', r"\2"),
    ]

    for x, y in replacements:
        xml_str = re.sub(x, y, xml_str)
    xml_str = xml_str or "<r/>"
    root = etree.parse(
        BytesIO(xml_str.encode("ascii", "xmlcharrefreplace")), parser=None
    ).getroot()

    # Transform .. to <gap>
    for t in root.xpath("//*[text()]"):
        if t.text:
            t.text = re.sub(
                r"\.{2,}",
                '<gap reason="illegible" extent="unknown" unit="character"/>',
                t.text,
            )

    for bad in root.xpath(
        ".//p|.//locus|.//div[@type='bibliography']|.//div[@type='commentary']"
    ):
        remove_keeping_tail(bad)

    if data["state"]["diplomatic"]:
        for bad in root.xpath(
            ".//ex|.//note|.//figure|.//ref|.//g|.//desc|.//figDesc|.//handShift"
        ):
            remove_keeping_tail(bad)
        for s in root.xpath(".//supplied"):
            s.text = "_"

    for x in root.xpath(
        './/app|.//certainty|.//desc|.//figDesc|.//ref|.//g|.//note|.//del[@rend="corrected"]|.//add[@place="inline"]|num|.//reg[@xml:lang]'
    ):
        match x.tag:
            case "app":
                app_type = x.attrib.get("type", "")
                for c in x.getchildren():
                    if c.tag in ["lem", "rdg"]:
                        c.attrib["type"] = app_type
            case "certainty":
                x.getparent().attrib["cert"] = "low"
                remove_keeping_tail(x)
            case "desc" | "figDesc":
                x.getparent().attrib["desc"] = x.text
                remove_keeping_tail(x)
            case "ref":
                x.getparent().attrib["ref_n"] = x.attrib.get("n", "")
                x.getparent().attrib["ref_text"] = x.text
                remove_keeping_tail(x)
            case "g":
                x.text = ""
            case "note":
                if len(x):
                    x.attrib["text"] = stringify_children(x).strip()
                    for c in x.getchildren():
                        if not c.tag == "ref":
                            x.remove(c)
                else:
                    x.attrib["text"] = x.text or ""
                x.text = ""

            case "del":
                x.tag = "scribaldel"
                x.attrib.clear()
            case "add":
                x.tag = "scribaladd"
                x.attrib.clear()
            # case 'reg':
            #    x.tag = 'langreg'
            #    x.attrib.clear()=

    for x in root.xpath(
        ".//lem|.//rdg|.//scribaladd|.//scribaldel|.//reg|.//orig|.//sic|.//corr"
    ):
        if not "".join(x.itertext()):
            x.text = "$"

    # Remove comments
    comments = root.xpath("//comment()")
    for c in comments:
        p = c.getparent()
        p.remove(c)

    # The below code does some additional preformatting
    # with the variation containers <subst>, <app>, and <choice>

    # First, to string again
    xml_str = etree.tostring(root, encoding="utf-8").decode()  # type: ignore

    def move_subst_prefix(x: re.Match) -> str:
        """Moves [prefix]<subst> to <subst><add>[prefix]"""
        space = x.group(1)
        prefix = x.group(2)
        subst = x.group(4)

        # Only move if prefix is valid XML
        try:
            _ = etree.fromstring(
                ("<r>" + prefix + "</r>").encode("ascii", "xmlcharrefreplace"),
                parser=None,
            )
            return space + subst + prefix

        # Otherwise, return as is
        except:
            return space + prefix + subst

    def move_choice_suffix(x: re.Match) -> str:
        """Moves <choice>[suffix] to [suffix]</orig> and [suffix]</reg>"""
        return re.sub(r"(</(orig|reg)>)", x.group(3) + r"\1", x.group(1))

    # ---- SUBST ----

    # Move [prefix]<subst> to subst
    xml_str = re.sub(
        r"(\s+)((<[^/>]+/?>|[a-zA-Z0-9]|</[a-z]+>|\p{Greek})+)(<subst><scribaladd>)",
        lambda x: move_subst_prefix(x),
        xml_str,
    )

    # Move [prefix]<subst> to subst (for multi-word <add>s)
    xml_str = re.sub(
        r'(<add place="above">[^>]+)\s([^>]+</add>)(<subst><scribaladd>)',
        r'\1</add> \3<add place="above">\2',
        xml_str,
    )

    # Finally, isolate <subst>
    xml_str = re.sub(r"(?<!\s)<subst>", " <subst>", xml_str)
    xml_str = re.sub(r"</subst>(?!\s)", "</subst> ", xml_str)

    # ---- CHOICE ----

    # Move <expan> or <abbr> suffix to <choice>
    xml_str = re.sub(
        r"(<choice>(?:(?!(<choice|</choice>)).)*</choice>)(<expan>.*?</expan>)",
        lambda x: move_choice_suffix(x),
        xml_str,
    )
    xml_str = re.sub(
        r"(<choice>(?:(?!(<choice|</choice>)).)*</choice>)(<abbr>.*?</abbr>)",
        lambda x: move_choice_suffix(x),
        xml_str,
    )
    xml_str = re.sub(
        r"(<choice>(?:(?!(<choice|</choice>)).)*</choice>)(<gap[^>]*?>)",
        lambda x: move_choice_suffix(x),
        xml_str,
    )
    # Isolate <choice>
    xml_str = re.sub(r"(?<!\s)<choice>", " <choice>", xml_str)
    xml_str = re.sub(r"</choice>(?!\s)", "</choice> ", xml_str)

    # ---- APP ----

    # Isolate <app>
    xml_str = re.sub(r"(?<!\s)<app", " <app", xml_str)
    xml_str = re.sub(r"</app>(?!\s)", "</app> ", xml_str)

    # Ensure space after ’
    xml_str = re.sub(r"’(?!\s)", "’ ", xml_str)
    xml_str = re.sub(r"ʼ(?!\s)", "ʼ ", xml_str)

    # To tree again
    try:
        root = etree.parse(
            BytesIO(xml_str.encode("ascii", "xmlcharrefreplace")),
            parser=None,
        ).getroot()
    except:
        traceback.print_exc()
        print(xml_str)
        exit()

    data["state"]["preformatted_xml"] = xml_str

    return {"root": root, "state": data["state"]}


def get_hgv_meta(hgv_path: str, hgvs: list, file_name: str) -> dict:
    # Get metadata from HGV file

    hgv_data = {
        "dna": "",
        "dnb": "",
        "found": {
            "ancient": set(),
            "nome": set(),
            "region": set(),
        },
        "written": {
            "ancient": set(),
            "nome": set(),
            "region": set(),
        },
        "place_name": "",
    }

    def get_dates(hgv_data: dict, targets: list, date: etree._Element) -> tuple:
        nonlocal hgv_path

        for target in targets:
            if d := date.attrib.get(target, ""):
                date_parts = d.split("-")
                try:
                    year = int(date_parts[0] if date_parts[0] else f"-{date_parts[1]}")
                    if target == "when":
                        hgv_data["dna"] = hgv_data["dnb"] = year
                    elif target == "notBefore":
                        if not hgv_data["dnb"] or year > hgv_data["dnb"]:
                            hgv_data["dnb"] = year
                    elif target == "notAfter":
                        if not hgv_data["dna"] or year < hgv_data["dna"]:
                            hgv_data["dna"] = year

                except:
                    print(f"Non-parsable date: {hgv_path}")
                    print(f"{date_parts}")
                    pass

        return hgv_data["dna"], hgv_data["dnb"]

    for hgv in hgvs:
        file = glob.glob(f"{hgv_path}/**/{hgv}.xml", recursive=True)
        if not file:
            continue

        xml_dom = remove_ns(etree.parse(file[0], parser=None))

        # Date
        for date in xml_dom.xpath(".//origDate"):
            hgv_data["dna"], hgv_data["dnb"] = get_dates(
                hgv_data, ["when", "notAfter", "notBefore"], date
            )

        # Place names
        for prov in xml_dom.xpath(".//provenance"):
            provtype = prov.attrib.get("type", "found")
            if provtype in ["found", "located"]:
                provtype = "found"
            elif provtype in ["written", "composed"]:
                provtype = "written"

            if provtype in ["written", "found"]:
                for p in prov.xpath(".//placeName"):
                    main_type = p.attrib.get("type", "ancient")
                    sub_type = str_none(p.attrib.get("subtype", "")).strip()
                    place_name = str_none(p.text).strip()
                    if main_type == "ancient":
                        if not sub_type:
                            hgv_data[provtype]["ancient"].add(place_name)
                        else:
                            if sub_type in ["nome", "region"]:
                                hgv_data[provtype][sub_type].add(place_name)

    hgv_data["place"] = convert_place(hgv_data, file_name)
    return hgv_data


def get_meta(xml_dom: etree._Element, xml_file_path: str) -> dict:
    # Get metadata from the EpiDoc XML document
    series_name = "Unknown series"
    if series_path_fragment := re.findall(
        r"(DDB_EpiDoc_XML|DCLP)\/(.*?)(?=\/)", xml_file_path
    ):
        series_name = (
            series_path_fragment[-1][-1]
            if len(series_path_fragment[0]) > 1
            else series_path_fragment[-1]
        )

    return {
        "series_name": series_name,
        "name": xml_file_path.split("/")[-1],
        "language": "".join(xml_dom.xpath(".//div/@xml:lang")) or "grc",
        "hgv": " ".join(xml_dom.xpath('.//idno[@type="HGV"]/text()')).split(" "),
        "tm": " ".join(xml_dom.xpath('.//idno[@type="TM"]/text()')).split(" "),
        "last_change": datetime.strptime(
            (xml_dom.xpath(".//change/@when") or ["9999-12-31"])[0][:10], "%Y-%m-%d"
        ),
    }


def init_tokenizer(xml_str: str, state: dict) -> object:
    # Init the tokenizer using function composition
    return composer(
        preformat,
        transform_tags,
        normalize_and_split,
        bracketify_words,
        transform_brackets,
        stack_alternatives,
        create_versions,
    )({"text": xml_str, "state": state})


def init_state(xml_file_path: str, diplomatic: bool) -> dict:
    # Init the global state of the tokenizer
    return {
        "elements": [],
        "notes": [],
        "figures": [],
        "file": xml_file_path,
        "diplomatic": diplomatic,
    }


def tokenize_file(
    # Tokenize an EpiDoc XML file
    xml_file_path: str,
    hgv_path: str = "",
    diplomatic: bool = False,
) -> dict:
    xml_dom = remove_ns(etree.parse(xml_file_path, parser=None))
    meta = get_meta(xml_dom, xml_file_path)
    xml_str = get_edition_xml_str(xml_dom)

    state = init_state(xml_file_path, diplomatic)
    return {
        "meta": meta,
        "hgv_meta": lambda: get_hgv_meta(hgv_path, meta["hgv"], meta["name"]),
        "edition_xml": xml_str,
        "tokens": lambda: init_tokenizer(xml_str, state),
    }


def tokenize_string(xml_str: str, diplomatic: bool = False) -> dict:
    # Tokenize an EpiDoc XML string
    state = init_state("", diplomatic)

    return {
        "edition_xml": xml_str,
        "tokens": lambda: init_tokenizer(
            xml_str.encode("ascii", "xmlcharrefreplace").decode(), state
        ),
    }
