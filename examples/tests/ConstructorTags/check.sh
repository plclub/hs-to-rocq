#!/usr/bin/env bash
# Fail-closed public CLI checks accompanying ConstructorTags.pass.
set -euo pipefail
version=${1:?expected target version}
case "$version" in 8.20|9.0) ;; *) exit 2 ;; esac
fixture_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
workspace=$(cd "$fixture_dir/../../.." && pwd)
export STACK_YAML="$workspace/stack.yaml"
[[ -d "$workspace/.stack-work" ]] || { printf 'Run stack build first.\n' >&2; exit 1; }
tmp=$(mktemp -d "$workspace/.stack-work/constructor-tags.XXXXXX")
trap 'rm -rf "$tmp"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

reject() {
  local name=$1 source=$2 diagnostic=$3 status=0 log
  shift 3
  mkdir "$tmp/$name"
  log="$tmp/$name/translator.log"
  stack --allow-different-user exec hs-to-rocq -- --strict -N \
    --target-version "$version" -e "$workspace/examples/tests/renamings" \
    -e "$fixture_dir/negative.edits" "$@" -o "$tmp/$name" "$source" \
    >"$log" 2>&1 || status=$?
  if [[ $status -eq 0 || $(<"$log") != *"$diagnostic"* ]]; then
    printf 'not ok - constructor tags %s/%s (exit %s)\n' "$version" "$name" "$status" >&2
    cat "$log" >&2
    exit 1
  fi
  printf 'ok - constructor tags %s/%s\n' "$version" "$name"
}

reject skipped "$workspace/examples/tests/ConstructorTags.hs" \
  'dataToTag#: target constructor list differs from source' \
  -e "$fixture_dir/skip.edits" -e "$fixture_dir/edits"
reject redefined "$workspace/examples/tests/ConstructorTags.hs" \
  'dataToTag#: redefined datatype is unsupported' \
  -e "$fixture_dir/redefine.edits" -e "$fixture_dir/edits"
for name in TagShadow TagLetShadow TagLambdaShadow; do
  reject "$name" "$fixture_dir/$name.hs" 'dataToTag#: unknown operand type: x'
done
reject builtin "$fixture_dir/TagBuiltin.hs" 'dataToTag#: no unique local source ADT'
reject gadt "$fixture_dir/TagGadt.hs" 'dataToTag#: non-vanilla constructors are unsupported'
