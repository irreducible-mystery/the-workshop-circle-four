#!/bin/sh
# ---------------------------------------------------------------------------
# THE WORKSHOP -> CIRCLE FOUR.  audit/c4_artifact_prefix.sh
# Q3-i, the ratchet — the builder's proposal, round 7, both seats' words.
#
# WHY THIS EXISTS: the round-7 delivery said its artifact "grew by
#   appending, as its own gate requires."  Measured by the non-author
#   seat, the growth was an INSERTION before the closing `end Zi`: a
#   148,113-byte common prefix with the round-6 file's last seven bytes
#   ("end Zi\n") consumed and re-emitted at the new end.  No gate was
#   violated — the seal-prefix gate guards the seal and says nothing about
#   the tail — which is exactly the point: the sentence was true of the
#   law and false of the file, and nothing could tell.  This instrument
#   makes that sentence machine-true from here on.
#
# WHAT THIS CHECKS: for each listed artifact, HEAD's committed copy must
#   be a BYTE-PREFIX of the working copy, and if the working copy is
#   longer, HEAD's copy must end on a newline — so growth is appending and
#   never an insertion, an in-place edit, or an extension of the last
#   committed line.  A symlinked artifact is refused.
#
# HOW TO GROW A LEAN ARTIFACT UNDER THIS LAW: append a fresh
#   `namespace Zi … end Zi` block after the existing close.  Semantically
#   identical to inserting before the old close; measurably different, and
#   the difference is the whole instrument.
#
# WHAT IT DOES NOT CHECK: the seal inside a carrying artifact (that is
#   audit/c4_seal_prefix.sh); the TRUTH of anything appended; history
#   rewrites (row 5's honest gap, inherited whole).
#
# NOTE ON SCOPE, twice-established and named again: CARRYING lists are
#   maintained by hand, so an artifact that is not listed arrives ungated.
#   The builder named this pattern at round 5 and again at round 6; it is
#   named here a third time, at authoring rather than at bite time.
#
# USAGE:  sh audit/c4_artifact_prefix.sh          (from the repo root)
# EXIT:   0 = every artifact grew by appending;  1 = violation;  2 = cannot run
# ---------------------------------------------------------------------------

set -u

ROOT=$(git rev-parse --show-toplevel 2>/dev/null) || {
    echo "c4_artifact_prefix: not a git repository" >&2; exit 2; }
cd "$ROOT" || exit 2

# Every artifact that must grow by appending.
ARTIFACTS="lean/C4_Q1.lean lean/C4_Q2.lean lean/C4_Q3.lean"

TMP=$(mktemp -d) || exit 2
trap 'rm -rf "$TMP"' 0

red=0
count=0
for f in $ARTIFACTS; do
    count=$((count + 1))
    if ! git cat-file -e "HEAD:$f" 2>/dev/null; then
        printf '  %-18s BORN THIS COMMIT (nothing to preserve)\n' "$f"
        continue
    fi
    if [ -L "$f" ]; then
        printf '  %-18s VIOLATION: artifact is a symlink\n' "$f"
        red=1
        continue
    fi
    if [ ! -f "$f" ]; then
        printf '  %-18s VIOLATION: artifact missing from the working copy\n' "$f"
        red=1
        continue
    fi
    git show "HEAD:$f" > "$TMP/head" || {
        echo "c4_artifact_prefix: cannot read HEAD:$f" >&2; exit 2; }
    n=$(wc -c < "$TMP/head")
    m=$(wc -c < "$f")
    if [ "$m" -lt "$n" ]; then
        printf '  %-18s VIOLATION: shorter than HEAD (%s < %s bytes)\n' "$f" "$m" "$n"
        red=1
        continue
    fi
    head -c "$n" "$f" > "$TMP/pref"
    if ! cmp -s "$TMP/head" "$TMP/pref"; then
        printf '  %-18s VIOLATION: not an append — HEAD is not a byte-prefix\n' "$f"
        cmp "$TMP/head" "$TMP/pref" 2>/dev/null | head -1 | sed 's/^/      /'
        red=1
        continue
    fi
    if [ "$m" -gt "$n" ]; then
        last=$(tail -c 1 "$TMP/head" | od -An -tx1 | tr -d ' \n')
        if [ "$last" != "0a" ]; then
            printf '  %-18s VIOLATION: the append extends the last committed line\n' "$f"
            red=1
            continue
        fi
        printf '  %-18s APPENDED (+%s bytes)\n' "$f" "$((m - n))"
    else
        printf '  %-18s UNCHANGED\n' "$f"
    fi
done

if [ "$red" -eq 0 ]; then
    echo "RESULT: $count artifact(s) grew by appending only.  PASS."
    exit 0
else
    echo "RESULT: an artifact grew by something other than appending.  FAIL."
    echo "        Append a fresh namespace block after the existing close;"
    echo "        never insert before it."
    exit 1
fi
