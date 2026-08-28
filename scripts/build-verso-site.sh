#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
site_dir="${1:-}"
verso_site="$repo_root/docs/_out/site/html-multi"

cd "$repo_root/docs"
# Verso updates an existing output tree in place. Remove only its generated
# multi-page directory so chapters deleted from the source cannot survive as
# orphaned public pages in local previews or restored CI workspaces.
rm -rf "$verso_site"
lake exe vbp build
lake exe vbp check

test -f "$verso_site/index.html"
test -f "$verso_site/-verso-data/blueprint-manifest.json"
test -f "$verso_site/-verso-data/blueprint-html-cache.json"

if [[ -n "$site_dir" ]]; then
  if [[ "$site_dir" != /* ]]; then
    site_dir="$repo_root/$site_dir"
  fi
  mkdir -p "$site_dir"
  cp -R "$verso_site"/. "$site_dir"/
  cp -R "$repo_root/pages/legacy-redirects"/. "$site_dir"/
  touch "$site_dir/.nojekyll"
fi
