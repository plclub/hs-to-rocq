#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
tests="$here/tests"
root=$(cd "$here/../.." && pwd)
export STACK_YAML="$root/stack.yaml"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/parkour-checks.XXXXXXXX")
trap 'rm -rf "$tmp"' EXIT

# Compile a dedicated one-query file. Reports on other definitions cannot
# satisfy this check. DIR contains the freshly compiled target library.
check_closed() {
    local dir=$1 name=$2
    shift 2
    [[ "$name" =~ ^([A-Za-z_][A-Za-z0-9_]*\.)+[A-Za-z_][A-Za-z0-9_]*$ ]] || return 2
    printf 'Require %s.\nPrint Assumptions %s.\n' "${name%.*}" "$name" > "$tmp/ParkourClosure.v"
    rocq c -w +deprecated-dirpath-Coq "$@" -Q "$dir" '' "$tmp/ParkourClosure.v" > "$tmp/closure.log" 2>&1 || {
        cat "$tmp/closure.log" >&2
        return 1
    }
    cat "$tmp/closure.log"
    if ! awk '/^Closed under the global context$/ { closed++ }
              /^Axioms:/ { axioms++ }
              END { exit !(closed == 1 && !axioms) }' "$tmp/closure.log"; then
        printf 'Assumption check failed for %s\n' "$name" >&2
        return 1
    fi
}

if [[ ${1:-} == --check-closed ]]; then
    shift
    check_closed "$@"
    exit
fi

cd "$here"
translator=(stack --allow-different-user exec hs-to-rocq --)
args=(--strict --target-version 9.0 -N -e "$root/base/edits")
required=(--require-origin Probe.keep=Probe.keep)

# Every negative test requires a nonzero status *and* its own diagnostic.
reject() {
    local label=$1
    shift
    local -a needles=()
    while [[ $1 != -- ]]; do needles+=("$1"); shift; done
    shift
    if "$@" > "$tmp/negative.log" 2>&1; then
        printf '%s: unexpected success\n' "$label" >&2
        exit 1
    fi
    local needle
    for needle in "${needles[@]}"; do
        if ! awk -v text="$needle" 'index(tolower($0), tolower(text)) { found=1 }
                                   END { exit !found }' "$tmp/negative.log"; then
            cat "$tmp/negative.log" >&2
            printf '%s: missing diagnostic: %s\n' "$label" "$needle" >&2
            exit 1
        fi
    done
    printf 'PASS: %s\n' "$label"
}

translate() {
    local out=$1
    shift
    mkdir -p "$out"
    "${translator[@]}" "${args[@]}" -o "$out" "$@"
}
compile() {
    rocq c -w +deprecated-dirpath-Coq -Q "$1" '' "$1/$2.v"
}

./test-vc1

good="$tmp/good"
mkdir -p "$good"
./checked-tool translate --strict --target-version 9.0 -N -e ../../base/edits \
    -e tests/allowed.edits -o "$good" "${required[@]}" tests/Probe.hs
cp "$tests/Contract.v" "$good"
compile "$good" Probe
compile "$good" Contract
check_closed "$good" Probe.keep

missing() {
    local label=$1
    shift
    reject "$label" 'required origin Probe.keep=Probe.keep: missing source-derived definition' -- translate "$@"
}
missing omit "$tmp/omit" "${required[@]}" "$tests/missing/Probe.hs"
for edit in skip axiom direct; do
    missing "origin/$edit" "$tmp/$edit" "${required[@]}" -e "$tests/$edit.edits" "$tests/Probe.hs"
done
# Renaming even makes the *emitted* qualified name match. Only the original
# Haskell identity distinguishes this program from the requested one.
other="$tmp/other"
translate "$other" -e "$tests/wrong-module.edits" --require-origin Other.keep=Probe.keep "$tests/Other.hs"
cp "$tests/Contract.v" "$other"
compile "$other" Probe
compile "$other" Contract
missing wrong-module "$tmp/other-origin" "${required[@]}" -e "$tests/wrong-module.edits" "$tests/Other.hs"

# Show that the very same handwritten preamble really supplies the missing
# definition, has the requested type and computes the requested results.
manual="$tmp/manual"
translate "$manual" -p "$tests/handwritten.v" "$tests/missing/Probe.hs"
cp "$tests/Contract.v" "$manual"
compile "$manual" Probe
compile "$manual" Contract
missing handwritten "$tmp/manual-origin" "${required[@]}" -p "$tests/handwritten.v" "$tests/missing/Probe.hs"

# Keep both the prior source output and compiled artifacts at the same paths.
[[ -s "$good/Probe.vo" && -s "$good/Probe.v" && -s "$good/Probe.h2ci" ]]
missing stale "$good" -e "$tests/allowed.edits" "${required[@]}" "$tests/missing/Probe.hs"

cp "$tests/Alias.v" "$tmp/Alias.v"
compile "$tmp" Alias
printf 'Require Alias.\nCheck @Alias.keep : forall a : Type, a -> a.\n' > "$tmp/AliasType.v"
compile "$tmp" AliasType
reject axiom-alias 'Assumption check failed for Alias.keep' 'Alias.opaqueKeep' -- check_closed "$tmp" Alias.keep
printf 'Parkour acceptance controls passed.\n'
