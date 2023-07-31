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


def remove_node(child, keep_content=False):
    """
    Remove an XML element, preserving its tail text.

    :param child: XML element to remove
    :param keep_content: ``True`` to keep child text and sub-elements.
    """
    parent = child.getparent()
    parent_text = parent.text or ""
    prev_node = child.getprevious()
    if keep_content:
        # insert: child text
        child_text = child.text or ""
        if prev_node is None:
            parent.text = "{0}{1}".format(parent_text, child_text) or None
        else:
            prev_tail = prev_node.tail or ""
            prev_node.tail = "{0}{1}".format(prev_tail, child_text) or None
        # insert: child elements
        index = parent.index(child)
        parent[index:index] = child[:]
    # insert: child tail
    parent_text = parent.text or ""
    prev_node = child.getprevious()
    child_tail = child.tail or ""
    if prev_node is None:
        parent.text = "{0}{1}".format(parent_text, child_tail) or None
    else:
        prev_tail = prev_node.tail or ""
        prev_node.tail = "{0}{1}".format(prev_tail, child_tail) or None
    # remove: child
    parent.remove(child)


punct = list(",..·;;·.§")
sent_punct = list(".·;;·.§")

no_ns_atts = lambda x: {k.split("}")[-1]: v for k, v in x.items()}
compose_inner_func = lambda f, g: lambda x: g(f(x))
composer = lambda *x: reduce(compose_inner_func, x, lambda x: x)
add_ud = lambda x: "".join(
    [y + "̣" if unicodedata.normalize("NFD", y)[0].lower().isalpha() else y for y in x]
)
flat_list = lambda x: [item for sublist in x for item in sublist]


def format_token_html(form: str, token_data: list) -> str:
    def bracket_grammar(tag, atts):
        atts_html = " ".join([f"data-att-{x}='{y}'" for x, y in atts.items()])
        atts_html = (" " + atts_html) if atts_html else atts_html
        return f"<span data-tag='{tag}'{atts_html}>"

    form_symbols = list(form) + [""]
    start_brackets = [""] * (len(form_symbols))
    end_brackets = [""] * (len(form_symbols))
    for el in token_data:
        bracket = bracket_grammar(el["tag"], el["atts"])
        start_brackets[el["start"]] += bracket
        end_brackets[el["end"]] += "</span>"

    for i, bracket in enumerate(start_brackets):
        form_symbols[i] = bracket + form_symbols[i]
    for i, bracket in enumerate(end_brackets):
        form_symbols[i] = form_symbols[i] + bracket

    return "".join(form_symbols).replace("█", "").replace("⧙⧘", "|").replace("▒", "")


def format_tokens_html(tokens: list) -> list:
    for i, token in enumerate(tokens):
        token[i]["format_html"] = format_token_html(
            token["form_unformatted"], token["token_data"]
        )
    return tokens


def format_papygreek(form: str, token_data: list) -> str:
    def bracket_grammar(tag, atts):
        # Uncertain
        u = "(?)" if atts.get("cert", "") or atts.get("precision", "") else ""
        match tag:
            case "supplied":
                match atts.get("reason", ""):
                    case "omitted":
                        return ["<", f"{u}>"]
                    case "lost":
                        if atts.get("evidence", "") == "parallel":
                            return ["_[", f"{u}]_"]
                        else:
                            return ["[", f"{u}]"]
                    case "undefined":
                        return ["|_", f"{u}_|"]
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
                return [f"〚{s}", f"{u}〛"]

            case "add":
                match atts.get("place", ""):
                    case "above":
                        return ["\\", f"{u}/"]
                    case "below" | "bottom":
                        return ["/", f"{u}\\"]
                    case "left":
                        return ["||←:", f"{u}||"]
                    case "right":
                        return ["||→:", f"{u}||"]
                    case "interlinear":
                        return ["||↕:", f"{u}||"]
                    case "margin":
                        if atts.get("rend", "") == "underline":
                            return ["<_", f"{u}_>"]
                        elif atts.get("rend", "") == "sling":
                            return ["<|", f"{u}|>"]

            case "hi":
                match atts.get("rend", ""):
                    case "supraline":
                        return ["¯", f"{u}¯"]
                    case "tall":
                        return ["~||", f"{u}||~"]
                    case "superscript":
                        return ["|^", f"{u}^|"]
                    case "above":
                        return ["|^", f"{u}^|"]
                    case "subscript":
                        return ["\\|", f"{u}|/"]
                    case "supraline-underline":
                        return ["¯_", f"{u}_¯"]
                    case "underline" | "underlined":
                        return ["_", f"{u}_"]
                    case "diaeresis":
                        return ["", f"(¨{u})"]
                    case "acute":
                        return ["", f"(´{u})"]
                    case "asper":
                        return ["", f"(῾{u})"]
                    case "grave":
                        return ["", f"(`{u})"]
                    case "circumflex":
                        return ["", f"(^{u})"]
                    case "lenis":
                        return ["", f"(᾿{u})"]

            case "q":
                return ["❛", f"{u}❜"]
            case "expan":
                return ["(", f"{u})"]

            case "ex":
                u = "?" if atts.get("cert", "") or atts.get("precision", "") else ""
                return ["(", f"{u})"]
            case "abbr":
                u = "?" if atts.get("cert", "") or atts.get("precision", "") else ""
                return ["(|", f"{u}|)"]

            case "num":
                u = "?" if atts.get("cert", "") or atts.get("precision", "") else ""
                return ["", f"{u}"]

            case "milestone":
                rend = atts.get("rend", "")
                return [f"*{rend or 'milestone'}*", ""]

            case "g":
                g_type = atts.get("type", "")
                u = "(?)" if atts.get("cert", "") else ""
                match g_type:
                    case "x":
                        return [f"*✕{u}*", f""]
                    case "slanting-stroke":
                        return [f"*╱{u}*", ""]
                    case "extension":
                        return [f"*—{u}*", ""]
                    case "apostrophe":
                        return [f"*⸍{u}*", ""]
                    case "stauros":
                        return [f"*†{u}", "*"]
                    case "rho-cross":
                        return [f"*⳨{u}*", ""]
                    case "chirho":
                        return [f"*☧{u}*", ""]
                    case "check":
                        return [f"*✓{u}*", ""]
                    case "middot":
                        return [f"*‧{u}*", ""]
                    case "dipunct":
                        return [f"*∶{u}*", ""]
                    case "long-vertical-bar":
                        return [f"*｜{u}*", ""]
                    case "diastole":
                        return [f"*⸒{u}*", ""]
                    case "dot":
                        return [f"*•{u}*", ""]
                    case "unintelligible":
                        return [f"*?{u}*", ""]
                    case _:
                        return [f"*{g_type}{u}*", ""]

            case "gap" | "space":
                pd = "."
                brackets = {
                    "lost": ["[", "]"],
                    "omitted": ["<", ">"],
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
                desc = atts.get("desc", "").lower()
                if desc:
                    if desc == "non transcribed":
                        desc = f"{pd}nontr"
                    elif desc == "vestiges":
                        desc = f"{pd}vestig"
                    else:
                        desc = f"{pd}{desc}"

                ell = f"{pd}ell" if atts.get("reason", "") == "ellipsis" else ""

                ca = f"{pd}ca" if atts.get("precision", "") else ""

                quantity = atts.get("quantity", "")
                atleast = atts.get("atLeast", "")
                atmost = atts.get("atMost", "")

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

                return [f"{br[0]}{sp}{desc}{ell}{ca}{pd}{ext}{unit}{prec}{br[1]}", ""]

        return ["", f"{u}"]

    form_symbols = list(form) + [""]
    start_brackets = [""] * (len(form_symbols))
    end_brackets = [""] * (len(form_symbols))

    for el in token_data:
        if el["tag"] == "unclear":
            for s in range(el["start"], el["end"] + 1):
                form_symbols[s] = add_ud(form_symbols[s])
        else:
            brackets = bracket_grammar(el["tag"], el["atts"])
            start_brackets[el["start"]] += brackets[0]
            end_brackets[el["end"]] = brackets[1] + end_brackets[el["end"]]

    for i, bracket in enumerate(start_brackets):
        form_symbols[i] = bracket + form_symbols[i]
    for i, bracket in enumerate(end_brackets):
        form_symbols[i] = form_symbols[i] + bracket

    return "".join(form_symbols).replace("█", "").replace("⧙⧘", "|").replace("▒", "")


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

    def plain(x: str) -> str:
        return "".join(
            [
                unicodedata.normalize("NFD", a)[0].lower()
                for a in x
                if a.isalpha() or a in punct + ["_"]
            ]
        )

    def version_type(k: str) -> str:
        if not ("reg" in k or "scribaldel" in k or "corr" in k or "rdg" in k):
            return "orig"
        elif not ("rdg" in k or "scribaldel" in k):  # These are "var" versions
            return "reg"
        return "var"

    # Initial settings
    token_lang = "grc"
    document_lang = "grc"
    prev_n = 1
    n = 1
    hand = "m1"
    aow_n = 1
    sentence_n = 1
    textpart = []
    line = "1"
    line_rend = ""
    tokens_data = []
    increment_sentence = False
    cancel_increment = False

    for token in data["tokens"]:
        if type(token) == str:
            token = [token]

        # The main iteration. If token has no variation, the list will
        # contain just the single token
        for t in token:
            # Init the dict for the result data
            token_all_data = {"orig": {}, "reg": {}, "var": [], "common": {}}

            # Last token had sentence-ending symbol
            if increment_sentence:
                sentence_n += 1
                prev_n = n
                n = 1
                increment_sentence = False

            # Last token had the symbol ° (for canceling sentence end)
            if cancel_increment:
                n = prev_n
                sentence_n -= 1
                cancel_increment = False

            for t_version in t.split("⧽"):
                # Get the version. If the token has no variation,
                # version will be "orig"
                version = version_type(t_version)
                num = ""
                num_rend = ""
                token_lang = document_lang

                # Get just one regularized version (the first one)
                if version == "reg":
                    if token_all_data["reg"]:  # Other regs will be "var" versions
                        version = "var"

                # If version is orig or reg, get sentence data
                if version != "var":
                    if any(s in t_version for s in sent_punct):
                        increment_sentence = True

                    if "§" in t_version:
                        # This symbol (included in sent_punct) marks sentence end.
                        # Skipping, because this is not a real token
                        continue

                    if "°" in t_version:
                        # This symbol prevents sentence breaks
                        cancel_increment = True
                        continue

                token_els = {}  # Token elements
                token_str = ""  # The unformatted string
                token_edited_str = ""  # Plain edited string
                token_transcript_str = ""  # Plain pure transcript

                # Break down token to a list of elements and strings
                t_parts = [
                    x
                    for x in re.split(r"((?:[><][a-zA-Z]*)?\[[0-9]+\])", t_version)
                    if x
                ]
                within_supplied = 0
                within_ex = 0
                within_surplus = 0
                token_string_id = 0
                increment_token_string_id = False
                decrement_token_string_id = False
                variation_type = []
                prev_hand = hand

                # Iterate elements and strings
                for t_part in t_parts:
                    # Test if this part is element (and not string)
                    element_id = (re.findall(r"\[([0-9]+)\]", t_part) or [""])[0]

                    # Got element
                    if element_id:
                        # Get data
                        el = data["state"]["elements"][int(element_id)]
                        atts = no_ns_atts(el.attrib)

                        # Starting tag or empty tag
                        if "<" not in t_part:
                            # Skip the following if this is "var"
                            if version != "var":
                                if el.tag == "div":
                                    if "lang" in atts:
                                        document_lang = atts["lang"]
                                        token_lang = document_lang
                                    else:
                                        inc_atts = []
                                        if "n" in atts:
                                            inc_atts.append(atts["n"])
                                        if "subtype" in atts:
                                            inc_atts.append(atts["subtype"])
                                        textpart.append(".".join(inc_atts))

                                if el.tag == "handShift":
                                    token_str += "▒"
                                    increment_token_string_id = True
                                    hand = atts.get("new", hand)
                                    hand += "?" if atts.get("cert", "") else ""

                                if el.tag in ["lb", "l"]:
                                    line = atts.get("n", line)
                                    line_rend = atts.get("rend", "")
                                    if atts.get("break", "") == "no":
                                        token_str += "█"
                                        decrement_token_string_id = True

                            if el.tag == "foreign":
                                token_lang = atts.get("lang", token_lang)

                            elif el.tag == "num":
                                num = atts.get("value", "")
                                num_rend = atts.get("rend", "")

                            elif el.tag == "supplied":
                                if atts.get("reason", "") != "omitted":
                                    token_transcript_str += "_"
                                within_supplied += 1
                                    
                            elif el.tag == "ex":
                                within_ex += 1

                            elif el.tag == "surplus":
                                within_surplus += 1

                            elif el.tag in ["gap", "space", "milestone", "g"]:
                                token_str += "█"
                                increment_token_string_id = True

                                if el.tag == "gap":
                                    token_edited_str += "_"
                                    token_transcript_str += "_"

                            elif el.tag in [
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
                                variation_type.append(el.tag)

                            token_els[element_id] = {
                                "tag": el.tag,
                                "start": token_string_id,
                                "end": token_string_id,
                                "atts": atts,
                            }

                            if increment_token_string_id:
                                token_string_id += 1
                                increment_token_string_id = False

                            if decrement_token_string_id:
                                token_string_id -= 1
                                decrement_token_string_id = False

                        # Ending tag
                        else:
                            # Skip the following if this is "var"
                            if version != "var":
                                if el.tag == "div":
                                    try:
                                        textpart.pop()
                                    except:
                                        pass

                                    continue

                            if el.tag == "foreign":
                                token_lang = document_lang

                            elif el.tag == "supplied":
                                within_supplied -= 1

                            elif el.tag == "ex":
                                within_ex -= 1

                            elif el.tag == "surplus":
                                within_surplus -= 1

                            token_els[element_id]["end"] = token_string_id - 1
                            if token_els[element_id]["end"] == -1:
                                token_els[element_id]["end"] = 0

                    # String part
                    else:
                        token_string_id += len(t_part)
                        token_str += t_part

                        if not (within_supplied or within_ex):
                            token_transcript_str += t_part
                        if not within_surplus:
                            token_edited_str += t_part

                # Hand changed (test here, because token-internal hand change
                # does not count; see e.g. upz.1.46.xml)
                if hand != prev_hand:
                    aow_n += 1

                common_data = {
                    "n": n,
                    "sentence_n": sentence_n,
                    "line": line,
                    "line_rend": line_rend,
                    "hand": hand,
                    "aow_n": aow_n,
                    "textpart": "/".join(textpart),
                    "artificial": None,
                    "insertion_id": None,
                }

                formatted_token = format_papygreek(token_str, list(token_els.values()))
                # print(formatted_token)
                # if re.sub(r"[⸨⸩⧛⧚▒\[\]¯⧛⧚]*", "", formatted_token):
                if re.sub(r"[⸨⸩⧛⧚▒”\']+", "", token_str) or formatted_token in [
                    "<(?)>"
                ]:
                    token_edited_str_plain = plain(re.sub("_+", "_", token_edited_str))
                    token_transcript_str_plain = plain(
                        re.sub("_+", "_", token_transcript_str)
                    )

                    token_data = list(token_els.values())

                    token_version_data = {
                        f"{version}_form_unformatted": token_str.replace("⧙", "")
                        .replace("⧘", "")
                        .replace("▒", ""),
                        f"{version}_form": formatted_token,
                        f"{version}_plain": token_edited_str_plain,
                        f"{version}_plain_transcript": token_transcript_str_plain,
                        f"{version}_lang": token_lang,
                        f"{version}_data": token_data,
                        f"{version}_num": num,
                        f"{version}_num_rend": num_rend,
                        f"{version}_variation_path": "/".join(variation_type),
                        f"{version}_lemma": None,
                        f"{version}_postag": None,
                        f"{version}_relation": None,
                        f"{version}_head": None,
                    }

                    if version == "var":
                        token_all_data[version].append(token_version_data)
                    else:
                        token_all_data[version] = token_version_data

                    token_all_data["common_data"] = common_data
            if token_all_data["orig"]:
                if not token_all_data["reg"]:
                    token_all_data["reg"] = {
                        k.replace("orig_", "reg_"): v
                        for k, v in token_all_data["orig"].items()
                    }

                if (
                    token_all_data["reg"]["reg_form_unformatted"] == "$"
                    and token_all_data["orig"]["orig_form_unformatted"] == "$"
                ):
                    continue

                token_all_data["common_data"]["var"] = token_all_data["var"]

                tokens_data.append(
                    token_all_data["orig"]
                    | token_all_data["reg"]
                    | token_all_data["common_data"]
                )
                n += 1

    return {"tokens": tokens_data}


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
                t_parts[k] = re.sub(
                    r"(^[^>]+)((>[a-zA-Z]{2,}\[[0-9]+\])+)", r"\2\1", part
                )
            ts[i] = "⧽".join(t_parts)

        return ts

    def group_recu(tokens: list, pattern: str) -> list:
        # Group tokens by variant containing tag
        res = []
        grouped_tokens = groupby(tokens, lambda x: get_match(x, pattern))
        for i, group_iterator in grouped_tokens:
            group = list(group_iterator)
            if not i:  # No group, add as is
                res += group
                continue
            res += [group_recu(group, re.escape(i) + r".*?(>([a-zA-Z]{2,})\[[0-9]+\])")]
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
                n = best_match(x, clean_regex=r"([><][a-zA-Z]+\[[0-9]+\])")
                return ["⧽".join(l) for l in zip(*n)]

            elif any([type(y) == list for y in x]) and all(
                [type(y) == str for y in flat_list(x)]
            ):
                return list(flatten_deep(x))

            for i in x:
                my += [stack_variants(i)]
        return my

    # Start by grouping tokens contained in app, choice and subst

    grouped_tokens = group_recu(data["tokens"], r"(?<!>)>(app|choice|subst)\[[0-9]+\]")

    for i, group in enumerate(grouped_tokens):
        if type(group) == list:
            old_group = []
            c = 0
            while group != old_group:
                old_group = group
                group = stack_variants(group)
                c += 1

            grouped_tokens[i] = move_brackets(list(group))

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

    def bracket_transformer(direction: str, stack_id: int) -> str:
        nonlocal element_stack
        mode = 0 if direction == ">" else 1
        el = element_stack[stack_id]
        tag = el.tag

        if tag in [
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
            if mode == 0:
                return f"{direction}{tag}[{stack_id}]"
        return f"{direction}e[{stack_id}]"

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

    def transformer(root: etree._Element) -> str:
        nonlocal things_i
        nonlocal things_l
        nonlocal state
        transformed = ""

        atts = no_ns_atts(root.attrib)

        if not (len(root) or root.text):  # <el/>
            if root.tag not in [
                "supplied",
                "unclear",
                "ab",
                "del",
                "div",
                "hi",
                "add",
                "q",
                "w",
                "r",
            ]:
                state["elements"].append(root)
                # things_l.append(things_i)
                if root.tag in ["lb", "l"]:
                    brackets = (
                        ["⧙", "⧘"] if atts.get("break", "") == "no" else ["⧛", "⧚"]
                    )
                    transformed += f" {brackets[0]}[{things_i}]{brackets[1]} "
                elif root.tag in ["note", "figure"]:
                    transformed += f" [{things_i}] "
                else:
                    transformed += f"[{things_i}]"

                things_i += 1

        else:
            state["elements"].append(root)
            things_l.append(things_i)
            if root.tag == "div":
                transformed += f" ⸨[{things_i}] "
            else:
                sep = " " if root.tag in ["app", "choice", "subst"] else ""
                transformed += f"{sep}>[{things_i}]"

            things_i += 1
            if root.text:
                transformed += re.sub(f'([{"".join(punct)}])', r" \1 ", root.text)

            if len(root):
                for elem in root.iterchildren(tag=None):
                    transformed += transformer(elem)
                    if elem.tail:
                        transformed += re.sub(
                            f'([{"".join(punct)}])', r" \1 ", elem.tail
                        )

            if root.tag == "div":
                transformed += f" ⸩ "
            else:
                transformed += f"<[{things_l[-1]}]"
            things_l.pop()

        return transformed

    root = data["root"]
    state = data["state"]
    things_i = 0
    things_l = []

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

    xml_str = data["text"]
    replacements = [
        (r"<[\/]?ab>", ""),
        # (r"<num[^>]*\/>", ""),
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
        remove_node(bad)

    for x in root.xpath(
        './/app|.//certainty|.//desc|.//figDesc|.//ref|.//g|.//note|.//del[@rend="corrected"]|.//add[@place="inline"]|num|.//reg[@xml:lang]'
    ):
        match x.tag:
            # case "app":
            #    app_type = x.attrib.get("type", "")
            #    for c in x.getchildren():
            #        if c.tag in ["lem", "rdg"]:
            #            c.attrib["type"] = app_type
            case "certainty":
                x.getparent().attrib["cert"] = "low"
                remove_node(x)
            case "desc" | "figDesc":
                x.getparent().attrib["desc"] = x.text
                remove_node(x)
            case "ref":
                x.getparent().attrib["ref_n"] = x.attrib.get("n", "")
                x.getparent().attrib["ref_text"] = x.text
                remove_node(x)
            case "g":
                x.text = ""
                if list(x.iterancestors(tag="unclear")):
                    x.attrib["cert"] = "low"
            case "note":
                if len(x):
                    x.attrib["text"] = stringify_children(x).strip()
                    for c in x.getchildren():
                        if not c.tag == "ref":
                            x.remove(c)
                else:
                    x.attrib["text"] = x.text or "note"
                x.text = "note"
                x.text = f" {x.text} "

            case "del":
                x.tag = "scribaldel"
                x.attrib.clear()
            case "add":
                x.tag = "scribaladd"
                x.attrib.clear()
            # case 'reg':
            #    x.tag = 'langreg'
            #    x.attrib.clear()=

    for x in root.xpath(".//figure"):
        x.text = " figure "

    for x in root.xpath(".//unclear"):
        if not ((x.text or "").strip() or len(x)):
            remove_node(x, True)

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
                    sub_type = p.attrib.get("subtype", "").strip()
                    place_name = (p.text or "").strip()
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


def init_state(xml_file_path: str) -> dict:
    # Init the global state of the tokenizer
    return {
        "elements": [],
        "file": xml_file_path,
    }


def tokenize_file(
    # Tokenize an EpiDoc XML file
    xml_file_path: str,
    hgv_path: str = "",
) -> dict:
    xml_dom = remove_ns(etree.parse(xml_file_path, parser=None))
    meta = get_meta(xml_dom, xml_file_path)
    xml_str = get_edition_xml_str(xml_dom)

    state = init_state(xml_file_path)
    return {
        "meta": meta,
        "hgv_meta": lambda: get_hgv_meta(hgv_path, meta["hgv"], meta["name"]),
        "edition_xml": xml_str,
        "tokens": lambda: init_tokenizer(xml_str, state),
    }


def tokenize_string(xml_str: str) -> dict:
    # Tokenize an EpiDoc XML string
    state = init_state("")

    return {
        "edition_xml": xml_str,
        "tokens": lambda: init_tokenizer(
            xml_str.encode("ascii", "xmlcharrefreplace").decode(), state
        ),
    }
