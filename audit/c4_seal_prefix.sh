#!/bin/sh
# ---------------------------------------------------------------------------
# THE WORKSHOP -> CIRCLE FOUR.  audit/c4_seal_prefix.sh
# The seal-prefix gate — for files that carry the sealed artifact WHOLE.
#
# WHY THIS EXISTS: `lean/C4_Q3.lean` instantiates the sealed gauge
#   classification, so it needs the sealed theorems themselves — not seven
#   definitions but the whole chain behind `at_most_two_classes`.  A
#   zero-import file cannot import them, so it carries the sealed artifact
#   ENTIRE, byte-for-byte, as its prefix, and appends Circle Four's own
#   work after it.
#
# WHAT THIS CHECKS: the first N bytes of each carrying file, where N is the
#   size of the sealed artifact, are byte-identical to the sealed artifact
#   — the same prefix law the system record adopted for its constitution,
#   applied to a Lean file.  One test, no parsing, nothing to smuggle
#   past: any edit anywhere in the carried region breaks the prefix.
#   A symlinked carrying file is refused, the mode the prefix test alone
#   cannot see (the builder's probe, round 2).
#
# WHAT IT DOES NOT CHECK: that the carried seal is the sealed artifact —
#   audit/c4_inherited.sh measures that against the manifest.  Nor anything
#   about the TAIL, which is Circle Four's own and is supposed to differ;
#   the kernel and the non-author seat adjudicate that.
#
# USAGE:  sh audit/c4_seal_prefix.sh              (from the repo root)
# EXIT:   0 = every carrying file carries the seal exactly;  1 = drift;
#         2 = cannot run
# ---------------------------------------------------------------------------

set -u

ROOT=$(git rev-parse --show-toplevel 2>/dev/null) || {
    echo "c4_seal_prefix: not a git repository" >&2; exit 2; }
cd "$ROOT" || exit 2

SEAL=inherited/circle-two-three/lean/Zi.lean

# Every file that carries the sealed artifact as its prefix.
CARRYING="lean/C4_Q3.lean"

if [ ! -f "$SEAL" ]; then
    echo "c4_seal_prefix: missing $SEAL" >&2
    exit 2
fi

n=$(wc -c < "$SEAL")
sealsum=$(sha256sum "$SEAL" | cut -d' ' -f1)

red=0
count=0
for f in $CARRYING; do
    count=$((count + 1))
    if [ -L "$f" ]; then
        printf '  %-20s VIOLATION: carrying file is a symlink\n' "$f"
        red=1
        continue
    fi
    if [ ! -f "$f" ]; then
        printf '  %-20s VIOLATION: carrying file missing\n' "$f"
        red=1
        continue
    fi
    m=$(wc -c < "$f")
    if [ "$m" -lt "$n" ]; then
        printf '  %-20s VIOLATION: shorter than the seal (%s < %s bytes)\n' "$f" "$m" "$n"
        red=1
        continue
    fi
    have=$(head -c "$n" "$f" | sha256sum | cut -d' ' -f1)
    if [ "$have" = "$sealsum" ]; then
        printf '  %-20s SEAL CARRIED EXACT (%s bytes, tail %s bytes)\n' \
               "$f" "$n" "$((m - n))"
    else
        printf '  %-20s DRIFT: the carried region is not the sealed artifact\n' "$f"
        red=1
    fi
done

if [ "$red" -eq 0 ]; then
    echo "RESULT: $count carrying file(s) carry the seal byte-exact.  PASS."
    exit 0
else
    echo "RESULT: a carried seal drifted.  FAIL."
    echo "        The sealed artifact is not this circle's to edit — append"
    echo "        after it, never into it."
    exit 1
fi
