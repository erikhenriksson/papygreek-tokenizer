import sys

from dotenv import dotenv_values
from papygreektokenizer import tokenize_file, tokenize_string, format_tokens_html

import example

from pprint import pprint

config = dotenv_values(".env")
DDBDP_PATH = config["DDBDP_PATH"]
HGV_PATH = config["HGV_PATH"]

if __name__ == "__main__":
    if sys.argv[1] == "-f":
        tokenizer = tokenize_file(sys.argv[2], HGV_PATH or "")
        meta = tokenizer["meta"]
        hgv_meta = tokenizer["hgv_meta"]()
        tokens = tokenizer["tokens"]()["tokens"]
        print(hgv_meta)
        print(meta)
        print(tokens)
        print(tokenizer["edition_xml"])

    elif sys.argv[1] == "example":
        example = example.xml_str
        tokenizer = tokenize_string(example)
        tokens = tokenizer["tokens"]()["tokens"]
        pprint(tokens)
        exit()
        pg = " ".join([(x["reg"] or x["orig"])["form_papygreek"] for x in tokens])
        print(pg)
