#!/usr/bin/env bash
# Exercise real concurrent translators; fake tools cannot expose GHC file races.
set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
workspace=$(cd "$script_dir/../../.." && pwd)
export STACK_YAML="$workspace/stack.yaml"
translator=(stack --allow-different-user exec hs-to-rocq --)
tmp=$(mktemp -d "${TMPDIR:-/tmp}/hs-to-rocq-concurrent.XXXXXX")
trap 'rm -rf "$tmp"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

sources="$tmp/sources"
mkdir -p "$sources"
printf '%s\n' \
    'module ConcurrentShared where' \
    'shared :: Bool -> Bool' \
    'shared x = x' > "$sources/ConcurrentShared.hs"
for side in Left Right; do
    printf '%s\n' \
        "module Concurrent$side where" \
        'import ConcurrentShared' \
        "value$side :: Bool -> Bool" \
        "value$side x = shared x" > "$sources/Concurrent$side.hs"
done

fail() {
    printf 'not ok - %s\n' "$*" >&2
    local log line
    for log in "$work"/*.log; do
        [[ -f "$log" ]] || continue
        printf '%s:\n' "$log" >&2
        while IFS= read -r line; do printf '%s\n' "$line" >&2; done < "$log"
    done
    exit 1
}

translate() {
    local module=$1
    shift
    "${translator[@]}" --target-version "$version" -N \
        -e "$workspace/examples/tests/renamings" -i "$sources" \
        --iface-dir "$out" -o "$out" "$@" "$sources/$module.hs"
}

for version in 8.20 9.0; do
    work="$tmp/$version"
    out="$work/out"
    mkdir -p "$out" "$work/bootstrap"
    # Bootstrap elsewhere so the concurrent processes start with no GHC cache.
    (cd "$work/bootstrap"; translate ConcurrentShared) > "$work/shared.log" 2>&1 ||
        fail "$version/shared translation failed"
    for suffix in v h2ci; do
        [[ -s "$out/ConcurrentShared.$suffix" ]] || fail "$version/shared output missing"
    done

    (
        cd "$work"
        translate ConcurrentLeft > left.log 2>&1 &
        left=$!
        translate ConcurrentRight > right.log 2>&1 &
        right=$!
        status=0
        wait "$left" || status=1
        wait "$right" || status=1
        exit "$status"
    ) || fail "$version/concurrent translation failed"
    # A failed GHC load can exit zero, so require both complete output kinds.
    for side in Left Right; do
        for suffix in v h2ci; do
            [[ -s "$out/Concurrent$side.$suffix" ]] || fail "$version/$side output missing"
        done
    done
    # Check the race-prevention invariant even when scheduling hides the race.
    [[ ! -e "$work/.ghc-tmp" ]] || fail "$version/default translation generated shared GHC artifacts"
    printf 'ok - %s/concurrent real translations\n' "$version"
done

# Explicit GHC code-generation flags must still override the translator default.
work="$tmp/override"
mkdir -p "$work"
(cd "$work"; translate ConcurrentShared --ghc -fobject-code) > "$work/override.log" 2>&1 ||
    fail 'explicit GHC code-generation override failed'
[[ -s "$work/.ghc-tmp/ConcurrentShared.o" ]] || fail 'explicit GHC code-generation override ignored'
printf 'ok - explicit GHC code-generation override\n'
