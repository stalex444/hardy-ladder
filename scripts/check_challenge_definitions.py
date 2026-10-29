#!/usr/bin/env python3
"""Check that every `-- verbatim: <path>` ... `-- end verbatim` block of Challenge.lean is a
byte-identical contiguous slice of the named library file, and count the `sorry` tokens of
Challenge.lean against the theorem names of comparator.json.

Usage:  python3 scripts/check_challenge_definitions.py   (from the package root)
Exit status 0 iff every block matches and the counts agree.
"""
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CHALLENGE = os.path.join(ROOT, "Challenge.lean")
COMPARATOR = os.path.join(ROOT, "comparator.json")


def blocks(text):
    """Yield (source path, list of lines) for each verbatim block."""
    lines = text.split("\n")
    i = 0
    while i < len(lines):
        m = re.match(r"^-- verbatim: (\S+)$", lines[i])
        if m:
            j = i + 1
            body = []
            while j < len(lines) and lines[j] != "-- end verbatim":
                body.append(lines[j])
                j += 1
            if j == len(lines):
                raise SystemExit("unterminated verbatim block starting at line %d" % (i + 1))
            yield m.group(1), body
            i = j + 1
        else:
            i += 1


def contiguous_in(body, source_lines):
    n = len(body)
    for k in range(len(source_lines) - n + 1):
        if source_lines[k:k + n] == body:
            return k + 1
    return None


def main():
    text = open(CHALLENGE, encoding="utf-8").read()
    ok = True
    nblocks = 0
    for path, body in blocks(text):
        nblocks += 1
        src = open(os.path.join(ROOT, path), encoding="utf-8").read().split("\n")
        at = contiguous_in(body, src)
        if at is None:
            print("MISMATCH: block from %s (%d lines) is not a contiguous slice of that file"
                  % (path, len(body)))
            ok = False
        else:
            print("verbatim: %s lines %d-%d (%d lines) match byte for byte"
                  % (path, at, at + len(body) - 1, len(body)))
    if nblocks == 0:
        # This entry's Challenge uses no definition of its own (every formula is written out),
        # so there is nothing to copy: the check is that the Challenge really declares none.
        decls = re.findall(r"^\s*(?:noncomputable\s+)?(?:def|abbrev|structure|inductive|class)\s+",
                           text, re.M)
        if decls:
            print("no verbatim blocks, but Challenge.lean declares %d definition(s)" % len(decls))
            ok = False
        else:
            print("no verbatim blocks and no definitions in Challenge.lean: nothing to copy")
    nsorry = len(re.findall(r"\bsorry\b", text))
    names = json.load(open(COMPARATOR, encoding="utf-8"))["theorem_names"]
    declared = re.findall(r"^theorem\s+([\w.₀-₉']+)", text, re.M)
    print("sorry tokens in Challenge.lean: %d; compared theorems: %d; theorem declarations: %d"
          % (nsorry, len(names), len(declared)))
    if nsorry != len(names) or len(declared) != len(names):
        ok = False
    print("CHALLENGE DEFINITIONS CHECK:", "PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
