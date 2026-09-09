#!/usr/bin/env python3
"""Enumerate formalProofs from native metadata; Lychee checks HTTP reachability only."""
import argparse
import json
from pathlib import Path
import urllib.request
from problem_metadata import proof_links
URL = "https://google-deepmind.github.io/formal-conjectures/data/catalog.json"

def unique_links(links):
    return list(dict.fromkeys(link for link in links if link))

def links_from_extract(path):
    return proof_links(json.loads(Path(path).read_text()))

def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--extract",type=Path,help="Use a local native schema-2 extract")
    args=parser.parse_args(argv)
    if args.extract:links=links_from_extract(args.extract)
    else:
        with urllib.request.urlopen(URL,timeout=30) as response:
            links=proof_links(json.load(response))
    for link in links:print(link)
    return 0
if __name__=="__main__":raise SystemExit(main())
