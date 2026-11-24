#!/usr/bin/env bash
# Nonstructural groups with multiple retained members must still fail.
set -euo pipefail
version=${1:?expected target version}
case "$version" in 8.20|9.0) ;; *) exit 2 ;; esac
fixture_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
workspace=$(cd "$fixture_dir/../../.." && pwd)
export STACK_YAML="$workspace/stack.yaml"
[[ -d "$workspace/.stack-work" ]] || { printf 'Run stack build first.\n' >&2; exit 1; }
tmp=$(mktemp -d "$workspace/.stack-work/inline-mutual.XXXXXX")
trap 'rm -rf "$tmp"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
reject() {
  local name=$1 source=$2 edits=$3 diagnostic=$4 status=0 text
  mkdir "$tmp/$name"
  stack --allow-different-user exec hs-to-rocq -- --strict -N \
    --target-version "$version" -e "$workspace/examples/tests/renamings" \
    -e "$edits" -o "$tmp/$name" "$source" \
    >"$tmp/$name/translator.log" 2>&1 || status=$?
  text=$(<"$tmp/$name/translator.log")
  if [[ $status -eq 0 || "$text" != *"$diagnostic"* ]]; then
    printf 'not ok - inline mutual %s/%s (exit %s)\n%s\n' "$version" "$name" "$status" "$text" >&2
    exit 1
  fi
  printf 'ok - inline mutual %s/%s\n' "$version" "$name"
}
for name in no-inline two-remaining; do
  reject "$name" "$workspace/examples/tests/InlineMutualEdits.hs" \
    "$fixture_dir/$name.edits" 'non-structural mutual recursion unsupported'
done
reject partial "$fixture_dir/InlinePartial.hs" "$fixture_dir/partial.edits" \
  'partial application of a nonstructural inline helper'
reject root-capture "$fixture_dir/InlineRootCapture.hs" "$fixture_dir/root-capture.edits" \
  'closure/recursive-parameter name collision in nonstructural inlining'
