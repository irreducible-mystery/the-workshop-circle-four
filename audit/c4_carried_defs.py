#!/usr/bin/env python3
"""Extract a named top-level Lean declaration's text from a file.

Used by audit/c4_carried_defs.sh to re-measure every declaration Circle
Four copied out of the sealed artifact against the sealed artifact itself.
A declaration is taken to start at the line `def NAME` / `theorem NAME`
and to run until the next top-level opener or end of file; the docstring
immediately above it, if any, is included, because a copied definition
whose docstring drifted is still drift.

Prints the declaration text on stdout, or exits 2 with a message on
stderr if the name is absent or ambiguous.
"""

import re
import sys

OPENER = re.compile(r"^(def|theorem|abbrev|instance|structure|inductive|@\[|/--|/-!|/-)")


def extract(path, name):
    with open(path, "r", encoding="utf-8") as handle:
        lines = handle.read().split("\n")

    starts = [
        idx
        for idx, line in enumerate(lines)
        if re.match(r"^(def|theorem|abbrev)\s+" + re.escape(name) + r"(\s|$|\()", line)
    ]
    if not starts:
        print("c4_carried_defs: declaration not found: %s in %s" % (name, path),
              file=sys.stderr)
        sys.exit(2)
    if len(starts) > 1:
        print("c4_carried_defs: declaration ambiguous (%d occurrences): %s in %s"
              % (len(starts), name, path), file=sys.stderr)
        sys.exit(2)

    start = starts[0]

    # Pull in a docstring block sitting immediately above the declaration.
    doc_start = start
    probe = start - 1
    if probe >= 0 and lines[probe].rstrip().endswith("-/"):
        while probe >= 0:
            if lines[probe].lstrip().startswith("/--"):
                doc_start = probe
                break
            probe -= 1

    end = len(lines)
    for idx in range(start + 1, len(lines)):
        if OPENER.match(lines[idx]):
            end = idx
            break

    body = lines[doc_start:end]
    while body and body[-1].strip() == "":
        body.pop()
    return "\n".join(body)


def main():
    if len(sys.argv) != 3:
        print("usage: c4_carried_defs.py <lean-file> <declaration-name>",
              file=sys.stderr)
        sys.exit(2)
    sys.stdout.write(extract(sys.argv[1], sys.argv[2]) + "\n")


if __name__ == "__main__":
    main()
