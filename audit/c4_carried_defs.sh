#!/bin/sh
# ---------------------------------------------------------------------------
# THE WORKSHOP -> CIRCLE FOUR.  audit/c4_carried_defs.sh
# The carried-declaration gate — Circle Four's own, bitten at birth.
#
# WHY THIS EXISTS: `lean/C4_Q1.lean` is a zero-import single file, the way
#   the sealed artifact is, and the record runs it as one.  It therefore
#   COPIES the sealed definitions it builds on rather than importing them.
#   A copy with no mechanism keeping it honest is a defect waiting to
#   happen (door §7's own warning), so this gate re-measures every copied
#   declaration against the sealed artifact, character for character.
#
# WHAT THIS CHECKS: for each declaration named below, the text in
#   lean/C4_Q1.lean is byte-identical to the text of the same declaration
#   in the carried seal at inherited/circle-two-three/lean/Zi.lean —
#   docstring included, because a copy whose docstring drifted is drift.
#   Red on any difference, on a missing declaration, or on an ambiguous
#   one.
#
# WHAT IT DOES NOT CHECK: that the carried seal itself is the sealed
#   artifact — audit/c4_inherited.sh measures that against the manifest,
#   and the manifest against admission.  Nor the TRUTH of anything: a
#   faithfully copied definition can still be the wrong definition to
#   build on, and that is the non-author seat's to adjudicate.  Nor
#   declarations Circle Four wrote itself, which are its own and are
#   supposed to differ.
#
# USAGE:  sh audit/c4_carried_defs.sh            (from the repo root)
# EXIT:   0 = every carried declaration matches;  1 = drift;  2 = cannot run
# ---------------------------------------------------------------------------

set -u

ROOT=$(git rev-parse --show-toplevel 2>/dev/null) || {
    echo "c4_carried_defs: not a git repository" >&2; exit 2; }
cd "$ROOT" || exit 2

SEAL=inherited/circle-two-three/lean/Zi.lean
MINE=lean/C4_Q1.lean
HELPER=audit/c4_carried_defs.py

# Every declaration copied out of the sealed artifact, by name.
CARRIED="sumTo swapT eBasis antiM eDiff upTo upperPairs"

for f in "$SEAL" "$MINE" "$HELPER"; do
    if [ ! -f "$f" ]; then
        echo "c4_carried_defs: missing $f" >&2
        exit 2
    fi
done

red=0
count=0
for name in $CARRIED; do
    count=$((count + 1))
    a=$(python3 "$HELPER" "$SEAL" "$name") || exit 2
    b=$(python3 "$HELPER" "$MINE" "$name") || exit 2
    if [ "$a" = "$b" ]; then
        printf '  %-14s CARRIED EXACT\n' "$name"
    else
        printf '  %-14s DRIFT: the copy no longer matches the seal\n' "$name"
        red=1
    fi
done

if [ "$red" -eq 0 ]; then
    echo "RESULT: $count carried declarations re-measured against the seal.  PASS."
    exit 0
else
    echo "RESULT: a carried declaration drifted from the sealed artifact.  FAIL."
    echo "        The copy is not the seat's to edit.  Restore it, or carry a"
    echo "        differently-named declaration of Circle Four's own."
    exit 1
fi
