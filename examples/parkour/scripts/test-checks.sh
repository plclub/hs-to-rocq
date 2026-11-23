#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
tests="$here/tests"
root=$(cd "$here/../.." && pwd)
export STACK_YAML="$root/stack.yaml"

verify_contract() {
    (cd "$here" &&
        echo '2eaf6aa2825530ad31ce5e0a46e8574a089076e0bad34e3fe59fc1b369112502  tests/slice1.sha256' |
            shasum -a 256 -c - && shasum -a 256 -c tests/slice1.sha256)
}
verify_contract

check_closed() {
    python3 "$here/scripts/check-assumptions.py" closed "$@"
}

if [[ ${1:-} == --check-closed || ${1:-} == --check-client ]]; then
    policy=${1#--check-}
    shift
    exec python3 "$here/scripts/check-assumptions.py" "$policy" "$@"
fi

cd "$here"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/parkour-checks.XXXXXXXX")
trap 'rm -rf "$tmp"' EXIT
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
    python3 "$here/scripts/parkour_rocq.py" -Q "$1" '' "$1/$2.v"
}

controls="$tmp/controls"
cp -R "$tests/slice1" "$controls"
cp "$tests/Alias.v" "$controls"
compile "$controls" ExtraPremise
check_closed "$controls" ExtraPremise.keep
while IFS=$'\t' read -r name expected; do
    if [[ $expected == pass ]]; then
        compile "$controls" "$name"
    elif [[ $name == ExtraType ]]; then
        reject "$name" "$expected" 'False -> forall' 'while it is expected to have type' -- compile "$controls" "$name"
    else
        reject "$name" "$expected" -- compile "$controls" "$name"
    fi
done < "$controls/controls.tsv"
# The 9.2 exception must keep the diagnostic visible, even on success.
if [[ $(rocq c --print-version) == 9.2* ]]; then
    echo 'Notation ParkourList := list.' > "$controls/Compat.v"
    compile "$controls" Compat > "$tmp/compat.log"
    rg -F 'notation-for-abbreviation' "$tmp/compat.log"
fi
compile "$controls" Alias
compile "$controls" AliasType
reject axiom-alias 'Assumption check failed for Alias.keep' 'Alias.opaqueKeep' -- check_closed "$controls" Alias.keep
compile "$controls" Parkour/Runtime
compile "$controls" Client
client=(python3 "$here/scripts/check-assumptions.py" client "$controls")
"${client[@]}" Client.allowed
reject mixed-client 'Assumption check failed for Client.mixed: Constant Client.IO' -- "${client[@]}" Client.mixed

scripts/test-vc1

good="$tmp/good"
mkdir -p "$good"
scripts/checked-tool translate --strict --target-version 9.0 -N -e ../../base/edits \
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

printf 'Parkour acceptance controls passed.\n'
