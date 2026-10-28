#!/usr/bin/env bash
# Check edit application and diagnostics through the real translator CLI.
set -euo pipefail

usage() {
    printf 'Usage: bash %s [--target-version 8.20|9.0]\n' "${0##*/}"
}

versions=(8.20 9.0)
case $# in
    0) ;;
    1)
        if [[ "$1" == --help || "$1" == -h ]]; then usage; exit 0; fi
        usage >&2; exit 2
        ;;
    2)
        if [[ "$1" != --target-version || ( "$2" != 8.20 && "$2" != 9.0 ) ]]; then
            usage >&2; exit 2
        fi
        versions=("$2")
        ;;
    *) usage >&2; exit 2 ;;
esac

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
workspace=$(cd "$script_dir/../../.." && pwd)
export STACK_YAML="$workspace/stack.yaml"
translator=(stack --allow-different-user exec hs-to-rocq --)
fixtures="$script_dir/edit-fixtures"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/hs-to-rocq-edits.XXXXXX")
trap 'rm -rf "$tmp"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
count=0

print_file() {
    local file=$1 line
    [[ -f "$file" ]] || return 0
    printf '%s:\n' "$file" >&2
    while IFS= read -r line || [[ -n "$line" ]]; do
        printf '%s\n' "$line" >&2
    done < "$file"
}

fail() {
    printf 'not ok - %s/%s: %s\n' "$version" "$case_name" "$*" >&2
    local file
    print_file "$log"
    for file in "$work"/*.edits "$out"/*.v; do print_file "$file"; done
    exit 1
}

contains() {
    local file=$1 needle=$2 line
    while IFS= read -r line || [[ -n "$line" ]]; do
        [[ "$line" != *"$needle"* ]] || return 0
    done < "$file"
    return 1
}

require_text() {
    contains "$1" "$2" || fail "missing '$2' in ${1##*/}"
}

reject_text() {
    if contains "$1" "$2"; then fail "unexpected '$2' in ${1##*/}"; fi
}

source_contains() {
    local text
    text=$(< "$generated")
    text=${text//$'\n'/ }
    text=${text//$'\t'/ }
    while [[ "$text" == *'  '* ]]; do text=${text//'  '/' '}; done
    [[ "$text" == *"$1"* ]]
}

require_source() {
    source_contains "$1" || fail "missing '$1' in ${generated##*/}"
}

reject_source() {
    if source_contains "$1"; then fail "unexpected '$1' in ${generated##*/}"; fi
}

require_skipped() {
    local name=$1
    require_source "Skipping definition \`EditCli.$name'"
    reject_text "$generated" "Definition $name "
    reject_text "$generated" "Axiom $name "
}

begin_case() {
    case_name=$1
    work="$tmp/$version/$case_name"
    out="$work/out"
    log="$work/translator.log"
    mkdir -p "$out"
}

write_edits() {
    local name=$1
    shift
    printf '%s\n' "$@" > "$work/$name.edits"
}

translate() {
    local module=$1
    shift
    generated="$out/$module.v"
    status=0
    (
        cd "$work"
        "${translator[@]}" --target-version "$version" --strict -N \
            -e "$workspace/examples/tests/renamings" -i "$fixtures" \
            --iface-dir "$out" -o "$out" "$@" "$fixtures/$module.hs"
    ) > "$log" 2>&1 || status=$?
}

require_outputs() {
    local module=$1 suffix
    # A GHC load failure can exit zero; require both kinds of complete output.
    for suffix in v h2ci; do
        [[ -s "$out/$module.$suffix" ]] || fail "missing or empty $module.$suffix"
    done
}

expect_success() {
    local module=$1
    translate "$@"
    [[ $status -eq 0 ]] || fail "translator exited $status (expected success)"
    require_outputs "$module"
}

expect_error() {
    local module=$1 diagnostic=$2
    shift 2
    translate "$module" "$@"
    [[ $status -ne 0 ]] || fail "translator exited zero (expected '$diagnostic')"
    require_text "$log" "$diagnostic"
}

pass() {
    count=$((count + 1))
    printf 'ok - %s/%s\n' "$version" "$case_name"
}

for version in "${versions[@]}"; do
    begin_case baseline
    expect_success EditCli "$fixtures/EditClassCli.hs"
    require_outputs EditClassCli
    require_source 'Definition probe : bool := sourceA.'
    require_source 'Definition replacement : bool := true.'
    require_text "$out/EditClassCli.v" 'Identity__Token_identityMethod'
    pass

    begin_case duplicate-promote
    write_edits duplicate 'promote EditCli.value' 'promote EditCli.value'
    expect_error EditCli 'Duplicate promotions for EditCli.value' -e "$work/duplicate.edits"
    pass

    begin_case duplicate-polyrec
    write_edits duplicate 'polyrec EditCli.value' 'polyrec EditCli.value'
    expect_error EditCli 'Duplicate polymorphic recursion requests for EditCli.value' -e "$work/duplicate.edits"
    pass

    begin_case duplicate-skip
    write_edits duplicate 'skip EditCli.value' 'skip EditCli.value'
    expect_error EditCli 'Duplicate skips for EditCli.value' -e "$work/duplicate.edits"
    pass

    begin_case duplicate-rename
    write_edits duplicate \
        'rename value EditCli.value = EditCli.firstValue' \
        'rename value EditCli.value = EditCli.secondValue'
    expect_error EditCli 'Duplicate renamings for value EditCli.value' -e "$work/duplicate.edits"
    pass

    begin_case duplicate-redefine
    write_edits duplicate \
        'redefine Definition EditCli.replacement : bool := false.' \
        'redefine Definition EditCli.replacement : bool := true.'
    expect_error EditCli 'Duplicate redefinitions for EditCli.replacement' -e "$work/duplicate.edits"
    pass

    # Every file must be valid, even if an earlier file would override its map.
    begin_case duplicate-in-later-file
    write_edits first 'rename value EditCli.value = EditCli.firstValue'
    write_edits later \
        'rename value EditCli.value = EditCli.secondValue' \
        'rename value EditCli.value = EditCli.thirdValue'
    expect_error EditCli 'Duplicate renamings for value EditCli.value' \
        -e "$work/first.edits" --edits "$work/later.edits"
    pass

    begin_case cyclic-renames
    write_edits cycle \
        'rename value EditCli.value = EditCli.cycleHop' \
        'rename value EditCli.cycleHop = EditCli.value'
    expect_error EditCli 'Cyclic renamings EditCli.cycleHop and EditCli.value' -e "$work/cycle.edits"
    pass

    begin_case cyclic-renames-across-files
    write_edits first 'rename value EditCli.value = EditCli.cycleHop'
    write_edits second 'rename value EditCli.cycleHop = EditCli.value'
    expect_error EditCli 'Cyclic renamings EditCli.cycleHop and EditCli.value' \
        -e "$work/first.edits" -e "$work/second.edits"
    pass

    equations_prefix='equations edit for Qualified "EditCli" "value"'
    for conflict in skip redefine axiomatize-definition axiomatize-module deferred corecursive; do
        begin_case "equations-$conflict"
        case "$conflict" in
            skip)
                edit='skip EditCli.value'
                diagnostic="$equations_prefix conflicts with skip (remove one)"
                ;;
            redefine)
                edit='redefine Definition EditCli.value : bool -> bool := fun x => x.'
                diagnostic="$equations_prefix conflicts with redefine (remove one)"
                ;;
            axiomatize-definition)
                edit='axiomatize definition EditCli.value'
                diagnostic="$equations_prefix conflicts with axiomatize (remove one)"
                ;;
            axiomatize-module)
                edit='axiomatize module EditCli'
                diagnostic="$equations_prefix conflicts with axiomatize (remove one)"
                ;;
            deferred)
                edit='termination EditCli.value deferred'
                diagnostic="$equations_prefix is incompatible with deferred termination (use deferredFix instead)"
                ;;
            corecursive)
                edit='termination EditCli.value corecursive'
                diagnostic="$equations_prefix is incompatible with corecursive termination"
                ;;
        esac
        write_edits conflict 'equations EditCli.value' "$edit"
        expect_error EditCli "$diagnostic" -e "$work/conflict.edits"
        pass
    done

    equations_prefix='equations edit for Qualified "EditCli" "copyList"'
    begin_case equations-recursive-deferred
    write_edits conflict 'equations EditCli.copyList' 'termination EditCli.copyList deferred'
    expect_error EditCli "$equations_prefix is incompatible with deferred termination (use deferredFix instead)" -e "$work/conflict.edits"
    pass

    begin_case equations-recursive-corecursive
    write_edits conflict 'equations EditCli.copyList' 'termination EditCli.copyList corecursive'
    expect_error EditCli "$equations_prefix is incompatible with corecursive termination" -e "$work/conflict.edits"
    pass

    begin_case skip-class-on-datatype
    write_edits invalid 'skip class EditCli.Token'
    expect_error EditCli "skipping non-type classes with \`skip class\`" -e "$work/invalid.edits"
    pass

    begin_case plain-skip-on-class
    write_edits invalid 'skip EditClassCli.Identity'
    expect_error EditClassCli "skipping type class declarations (without \`skip class')" -e "$work/invalid.edits"
    pass

    # Plain skip on a class default is supported. An instance method must use
    # skip method instead; its generated name is checked by the baseline case.
    begin_case plain-skip-on-instance-method
    write_edits invalid 'skip EditClassCli.Identity__Token_identityMethod'
    expect_error EditClassCli "skipping instance method definitions (without \`skip method')" -e "$work/invalid.edits"
    pass

    begin_case wf-on-nonrecursive-function
    write_edits invalid 'termination EditCli.value {wf relation x}'
    expect_error EditCli 'cannot "termination" a definition that is not a recursive function' -e "$work/invalid.edits"
    pass

    # GHC supplies inferred types even without Haskell signatures. Explicitly
    # clearing the translated type reaches the missing-signature diagnostic.
    begin_case wf-with-cleared-signature
    write_edits invalid 'set type EditCli.copyList no type' 'termination EditCli.copyList {wf relation xs}'
    expect_error EditCli 'cannot "termination" a definition without a type signature' -e "$work/invalid.edits"
    pass

    # Map-valued edits merge left-biased across files, but duplicates within
    # either file are errors. Check both a generated name and a changed body.
    for order in first-second second-first; do
        begin_case "file-precedence-$order"
        write_edits first \
            'rename value EditCli.value = EditCli.firstValue' \
            'redefine Definition EditCli.replacement : bool := false.'
        write_edits second \
            'rename value EditCli.value = EditCli.secondValue' \
            'redefine Definition EditCli.replacement : bool := true.'
        if [[ "$order" == first-second ]]; then
            expect_success EditCli -e "$work/first.edits" --edits "$work/second.edits"
            winner=firstValue
            loser=secondValue
            body=false
        else
            expect_success EditCli --edits "$work/second.edits" -e "$work/first.edits"
            winner=secondValue
            loser=firstValue
            body=true
        fi
        require_source "Definition $winner : bool -> bool := fun x => x."
        require_source "Definition useValue : bool -> bool := fun x => $winner x."
        require_source "Definition replacement : bool := $body."
        reject_source "Definition $loser "
        reject_source 'Definition value '
        pass
    done

    begin_case alias-expansion
    write_edits alias \
        'alias module This EditCli' \
        'rename value This.value = This.aliasValue'
    expect_success EditCli -e "$work/alias.edits"
    require_source 'Definition aliasValue : bool -> bool := fun x => x.'
    require_source 'Definition useValue : bool -> bool := fun x => aliasValue x.'
    reject_source 'Definition value '
    reject_source 'This.'
    pass

    begin_case alias-file-local
    write_edits first 'alias module This EditCli'
    write_edits second 'rename value This.value = This.aliasValue'
    expect_success EditCli -e "$work/first.edits" -e "$work/second.edits"
    require_source 'Definition value : bool -> bool := fun x => x.'
    require_source 'Definition useValue : bool -> bool := fun x => value x.'
    reject_source 'aliasValue'
    pass

    # Within a file, the last rewrite runs first. Across files, the first
    # file's rewrite list runs first. The chain must stop at B or reach C
    # according to that order; these are not fixed-point rewrites.
    for layout in single-forward single-reverse multiple-forward multiple-reverse; do
        begin_case "rewrite-$layout"
        ab='rewrite forall , EditCli.sourceA = EditCli.sourceB'
        bc='rewrite forall , EditCli.sourceB = EditCli.sourceC'
        case "$layout" in
            single-forward)
                write_edits chain "$ab" "$bc"
                expect_success EditCli -e "$work/chain.edits"
                result=sourceB
                ;;
            single-reverse)
                write_edits chain "$bc" "$ab"
                expect_success EditCli -e "$work/chain.edits"
                result=sourceC
                ;;
            multiple-forward)
                write_edits first "$ab"
                write_edits second "$bc"
                expect_success EditCli -e "$work/first.edits" -e "$work/second.edits"
                result=sourceC
                ;;
            multiple-reverse)
                write_edits first "$ab"
                write_edits second "$bc"
                expect_success EditCli -e "$work/second.edits" -e "$work/first.edits"
                result=sourceB
                ;;
        esac
        require_source "Definition probe : bool := $result."
        reject_source 'Definition probe : bool := sourceA.'
        pass
    done

    for mode in definition module; do
        begin_case "skip-redefine-axiomatize-$mode"
        write_edits precedence \
            'skip EditCli.dropped' \
            'redefine Definition EditCli.dropped : bool := false.' \
            'axiomatize definition EditCli.dropped' \
            'skip EditCli.skippedAxiom' \
            'axiomatize definition EditCli.skippedAxiom' \
            'redefine Definition EditCli.replacement : bool := false.' \
            'axiomatize definition EditCli.replacement' \
            'axiomatize definition EditCli.ordinary' \
            'unaxiomatize definition EditCli.restored' \
            'axiomatize definition EditCli.restored' \
            'skip EditCli.skipRestored' \
            'unaxiomatize definition EditCli.skipRestored' \
            'axiomatize definition EditCli.skipRestored'
        if [[ "$mode" == module ]]; then
            write_edits module 'axiomatize module EditCli'
            expect_success EditCli -e "$work/precedence.edits" -e "$work/module.edits"
            # A module's unaxiomatize exception also overrides a simultaneous
            # definition axiomatization; outside a module it has no effect.
            require_source 'Definition restored : bool := true.'
            reject_source 'Axiom restored '
            require_source 'Axiom sourceA : bool.'
        else
            expect_success EditCli -e "$work/precedence.edits"
            require_source 'Axiom restored : bool.'
            reject_source 'Definition restored '
            require_source 'Definition sourceA : bool := true.'
        fi
        require_skipped dropped
        require_skipped skippedAxiom
        require_skipped skipRestored
        require_source 'Definition replacement : bool := false.'
        reject_source 'Axiom replacement '
        require_source 'Axiom ordinary : bool.'
        reject_source 'Definition ordinary '
        pass
    done
done

printf '%s real-translator edit CLI cases passed\n' "$count"
