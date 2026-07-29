#!/bin/sh
# ---------------------------------------------------------------------------
# THE WORKSHOP -> CIRCLE FOUR.  audit/c4_manifest_prefix.sh
# P3: the manifest under the prefix law — both seats' words, 2026-07-29.
#
# WHY THIS EXISTS: the carry-forward gate (c4_inherited.sh) proves the
#   manifest and the tree AGREE.  It cannot see a commit that moves a
#   carried file and its manifest row TOGETHER (the builder's plant P5,
#   green over a tampered carry), nor one that deletes both (P6, green
#   with only the row count shrinking).  Both compound modes need the
#   manifest itself to be append-only, and that is a claim about writes,
#   not about agreement — so it is enforced here, at the write surface.
#
# WHAT THIS CHECKS: HEAD's copy of inherited/MANIFEST.md must be a
#   BYTE-PREFIX of the working copy.  A carried file's row never changes
#   and rows only arrive; under that law P5's row edit and P6's row
#   deletion both break the prefix and bite where they are written.
#   The newline-boundary clause rides too: if the working copy is longer,
#   HEAD's copy must end in a newline, so an "append" can never extend
#   the last committed row in place.  A symlinked manifest is refused —
#   the mode the prefix test alone cannot see (the builder's symlink
#   probe, measured on both containers).
#
# WHAT IT DOES NOT CHECK: the TRUTH of any row (a row may be honestly
#   appended and wrong — the non-author seat adjudicates content); files
#   other than the manifest (c4_inherited.sh measures those); history
#   rewrites (row 5's honest gap, inherited whole); a mode-bit-only
#   change.
#
# USAGE:  sh audit/c4_manifest_prefix.sh          (from the repo root)
# EXIT:   0 = the manifest grew by appending;  1 = violation;  2 = cannot run
# ---------------------------------------------------------------------------

ROOT=$(git rev-parse --show-toplevel 2>/dev/null) || {
    echo "c4_manifest_prefix: not a git repository" >&2; exit 2; }
cd "$ROOT" || exit 2

f=inherited/MANIFEST.md

if ! git cat-file -e "HEAD:$f" 2>/dev/null; then
    printf '  %-28s BORN THIS COMMIT (nothing to preserve)\n' "$f"
    echo "RESULT: the manifest grew by appending only.  PASS."
    exit 0
fi
if [ -L "$f" ]; then
    printf '  %-28s VIOLATION: the manifest is a symlink\n' "$f"
    echo "RESULT: the manifest's prefix law was broken.  FAIL."
    exit 1
fi
if [ ! -f "$f" ]; then
    printf '  %-28s VIOLATION: the manifest is missing from the working copy\n' "$f"
    echo "RESULT: the manifest's prefix law was broken.  FAIL."
    exit 1
fi

TMP=$(mktemp -d) || exit 2
trap 'rm -rf "$TMP"' 0
git show "HEAD:$f" > "$TMP/head" || {
    echo "c4_manifest_prefix: cannot read HEAD:$f" >&2; exit 2; }
n=$(wc -c < "$TMP/head")
m=$(wc -c < "$f")

if [ "$m" -lt "$n" ]; then
    printf '  %-28s VIOLATION: rows were removed (%s < %s bytes)\n' "$f" "$m" "$n"
    echo "RESULT: the manifest's prefix law was broken.  FAIL."
    echo "        A carried file's row never changes; corrections arrive"
    echo "        as new rows.  Revert and append."
    exit 1
fi
head -c "$n" "$f" > "$TMP/pref"
if ! cmp -s "$TMP/head" "$TMP/pref"; then
    printf '  %-28s VIOLATION: a committed row changed in place\n' "$f"
    cmp "$TMP/head" "$TMP/pref" 2>/dev/null | head -1 | sed 's/^/      /'
    echo "RESULT: the manifest's prefix law was broken.  FAIL."
    echo "        A carried file's row never changes; corrections arrive"
    echo "        as new rows.  Revert and append."
    exit 1
fi
if [ "$m" -gt "$n" ]; then
    last=$(tail -c 1 "$TMP/head" | od -An -tx1 | tr -d ' \n')
    if [ "$last" != "0a" ]; then
        printf '  %-28s VIOLATION: the append extends the last committed row\n' "$f"
        echo "RESULT: the manifest's prefix law was broken.  FAIL."
        exit 1
    fi
fi

printf '  %-28s PREFIX LAW HOLDS\n' "$f"
echo "RESULT: the manifest grew by appending only.  PASS."
exit 0
