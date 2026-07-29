#!/bin/sh
# audit/c4_inherited.sh — the carry-forward gate (door §7, adopted at the founding).
#
# Re-measures every carried file against inherited/MANIFEST.md. Red on:
#   - any manifest row whose file is missing,
#   - any manifest row whose sha256 no longer matches (drift),
#   - any file under crossing/ or inherited/, or the root charge, with no
#     manifest row (an uncarried arrival posing as a carried one).
#
# What a green here proves: the carried files have not drifted SINCE
# ADMISSION. It does not prove the source repository still says what it
# said — only a seat that can reach the source can confirm that, and
# such a seat should (door §7, the honest boundary).
#
# Run from the repository root:  sh audit/c4_inherited.sh

set -u
MANIFEST=inherited/MANIFEST.md
red=0

if [ ! -f "$MANIFEST" ]; then
  echo "RED: $MANIFEST missing"
  exit 1
fi

# --- pass 1: every manifest row re-measured -------------------------------
rows=0
while IFS='|' read -r _ path _src _commit sha _; do
  path=$(echo "$path" | sed 's/^ *//;s/ *$//')
  sha=$(echo "$sha" | sed 's/^ *//;s/ *$//')
  case "$path" in
    path|---|'') continue ;;
  esac
  rows=$((rows + 1))
  if [ ! -f "$path" ]; then
    echo "RED: carried file missing: $path"
    red=1
    continue
  fi
  have=$(sha256sum "$path" | cut -d' ' -f1)
  if [ "$have" != "$sha" ]; then
    echo "RED: drift: $path"
    echo "     manifest $sha"
    echo "     measured $have"
    red=1
  fi
done < "$MANIFEST"

# --- pass 2: nothing carried without a row --------------------------------
for f in CIRCLE-FOUR-CHARGE.md $(find crossing inherited -type f | sort); do
  [ "$f" = "$MANIFEST" ] && continue
  if ! grep -q "| $f |" "$MANIFEST"; then
    echo "RED: no manifest row for: $f"
    red=1
  fi
done

if [ "$red" -eq 0 ]; then
  echo "PASS: $rows manifest rows re-measured, no drift, no uncarried file"
  exit 0
else
  echo "RED: the carry-forward gate bit"
  exit 1
fi
