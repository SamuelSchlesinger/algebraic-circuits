#!/usr/bin/env bash
# Build the doc-gen4 API reference and assemble the static site published to
# GitHub Pages.
#
# Usage: scripts/build_docs.sh
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
site="$root/_site"

if (( $# != 0 )); then
  echo "usage: scripts/build_docs.sh" >&2
  exit 2
fi

# The library must build before its documentation can be generated.
(cd "$root" && lake build --wfail)

# Always regenerate the HTML, even when the documentation database is already
# up to date (for example after restoring it from a CI cache without the HTML).
# doc-gen4 merges existing HTML and per-module search data into its output.
# Clear those generated files so deleted modules disappear from the site,
# while keeping the database and .doc markers for cached extraction.
rm -rf "$root/docbuild/.lake/build/doc"
rm -f "$root"/docbuild/.lake/build/doc-data/declaration-data-*.bmp
# The bibliography prepass also writes into doc/, so regenerate its output.
rm -f "$root/docbuild/.lake/build/doc-data/references.json"
rm -f "$root"/docbuild/.lake/build/doc-data/*.docs_built
(cd "$root/docbuild" && lake build Algebraic:docs)

rm -rf "$site"
mkdir -p "$site"
cp -R "$root/docbuild/.lake/build/doc/." "$site/"

echo "Site assembled in $site"
echo "Preview with: python3 -m http.server --directory '$site'"
