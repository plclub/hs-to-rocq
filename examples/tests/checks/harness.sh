#!/usr/bin/env bash
# Exercise the production test makefiles without a Haskell or Coq toolchain.
set -euo pipefail

log_call() {
    local kind=$1 module=$2
    shift 2
    {
        printf '%s:%s' "$kind" "$module"
        printf ' <%s>' "$@"
        printf '\n'
    } >> "$HARNESS_LOG"
}

# Reuse this script as both fake tools so the check needs no installed packages.
case "${1:-}" in
    --fake-translator)
        shift
        module=
        renamed=false
        for arg in "$@"; do
            case "$arg" in
                */RenameMe.hs|RenameMe.hs) renamed=true ;;
            esac
            case "$arg" in
                *.hs) module=${arg##*/}; module=${module%.hs} ;;
            esac
        done
        test -n "$module"
        if "$renamed"; then module=Renamed; fi
        log_call translate "$module" "$@"
        mode=success
        if [[ "$module" == Renamed ]]; then
            mode=${RENAMED_MODE:-success}
        elif [[ "$module" == "${FAULT_MODULE:-Probe}" ]]; then
            mode=${TRANSLATOR_MODE:-success}
        fi
        case "$mode" in
            success) printf 'generated %s\n' "${GENERATION:-initial}" > "$module.v" ;;
            error) exit 42 ;;
            partial) printf 'partial output\n' > "$module.v"; exit 42 ;;
            missing) : ;;
            *) exit 99 ;;
        esac
        exit 0
        ;;
    --fake-compiler)
        shift
        source=
        for arg in "$@"; do
            case "$arg" in *.v) source=$arg ;; esac
        done
        test -n "$source"
        module=${source##*/}
        module=${module%.v}
        log_call compile "$module" "$@"
        test -f "$source"
        if [[ "$module" == "${COMPILER_FAULT_MODULE:-Probe}" && ${COMPILER_MODE:-success} == error ]]; then
            exit 43
        fi
        : > "${source%.v}.vo"
        exit 0
        ;;
esac

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
workspace=$(cd "$script_dir/../../.." && pwd)
script="$script_dir/harness.sh"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/hs-to-rocq-harness.XXXXXX")
trap 'rm -rf "$tmp"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
checks=0
test_dir=

fail() {
    printf 'not ok - %s\n' "$*" >&2
    local file line
    for file in "$test_dir/make.log" "$test_dir/tools.log"; do
        if [[ -f "$file" ]]; then
            printf '%s:\n' "$file" >&2
            while IFS= read -r line; do printf '%s\n' "$line" >&2; done < "$file"
        fi
    done
    exit 1
}

new_case() {
    suite=$1
    name=$2
    local case_root="$tmp/$suite/$name" source module
    if [[ "$suite" == shared ]]; then
        test_dir="$case_root/examples/tests"
        source=sources
    else
        test_dir="$case_root/examples/base-tests"
        source=.
    fi
    mkdir -p "$test_dir/$source/Probe" "$test_dir/$source/RenameMe"
    ln -s "$workspace/common.mk" "$case_root/common.mk"
    if [[ "$suite" == shared ]]; then
        ln -s "$workspace/examples/tests/Makefile" "$test_dir/Makefile"
        ln -s "$workspace/examples/tests/test-rules.mk" "$test_dir/test-rules.mk"
    else
        ln -s "$workspace/examples/base-tests/Makefile" "$test_dir/Makefile"
    fi
    for module in Probe ProbeExtra Control Future RenameMe RenameMeToo RenameModule; do
        : > "$test_dir/$source/$module.hs"
    done
    : > "$test_dir/$source/RenameMe.hs-boot"
    : > "$test_dir/$source/RenameMe/edits"
    : > "$test_dir/$source/renamings"
    : > "$test_dir/$source/Probe/edits"
    : > "$test_dir/$source/Probe/preamble.v"
    : > "$test_dir/$source/Probe/midamble.v"
    : > "$test_dir/tools.log"
    pass_modules=
    todo_pass_modules=
    todo_translate_modules=
    translator_mode=success
    compiler_mode=success
    renamed_mode=success
    fault_module=Probe
    compiler_fault_module=Probe
    generation=initial
}

run_make() {
    local expected=$1 actual
    shift
    local args=(
        --no-print-directory -C "$test_dir"
        FOREIGN_HS_TO_ROCQ=1 "HS_TO_ROCQ_DIR=$workspace"
        "HS_TO_ROCQ=bash \"$script\" --fake-translator"
        "PASS=$pass_modules" "TODO_PASS=$todo_pass_modules"
    )
    if [[ "$suite" == shared ]]; then
        args+=(
            "COMPILER=bash \"$script\" --fake-compiler"
            SRC_DIR=sources 'HS_EXTRA=--target-version 9.0' 'HS_IMPORT=-i sources'
            "TODO_TRANSLATE=$todo_translate_modules"
        )
    else
        # base-tests has its own TYPECHECK rather than the shared COMPILER hook.
        args+=("TYPECHECK=bash \"$script\" --fake-compiler")
    fi
    if MAKEFLAGS='' MFLAGS='' GNUMAKEFLAGS='' MAKEFILES='' MAKELEVEL=0 \
        HARNESS_LOG="$test_dir/tools.log" \
        TRANSLATOR_MODE="$translator_mode" COMPILER_MODE="$compiler_mode" \
        RENAMED_MODE="$renamed_mode" FAULT_MODULE="$fault_module" \
        COMPILER_FAULT_MODULE="$compiler_fault_module" GENERATION="$generation" \
        make "${args[@]}" "$@" > "$test_dir/make.log" 2>&1; then
        actual=0
    else
        actual=$?
    fi
    [[ "$actual" == "$expected" ]] || fail "$suite/$name: make returned $actual, expected $expected"
}

assert_calls() {
    local prefix="$1:$2 " expected=$3 count=0 line
    while IFS= read -r line; do
        if [[ "$line" == "$prefix"* ]]; then count=$((count + 1)); fi
    done < "$test_dir/tools.log"
    [[ "$count" == "$expected" ]] || fail "$suite/$name: $prefix called $count times, expected $expected"
}

assert_contains() {
    local file=$1 needle=$2 line
    while IFS= read -r line; do
        if [[ "$line" == *"$needle"* ]]; then return 0; fi
    done < "$test_dir/$file"
    fail "$suite/$name: $file did not contain $needle"
}

assert_output() {
    local file=$1 expected=$2 line
    if [[ "$expected" == absent ]]; then
        [[ ! -e "$test_dir/$file" ]] || fail "$suite/$name: $file was not removed"
    else
        [[ -f "$test_dir/$file" ]] || fail "$suite/$name: $file is missing"
        IFS= read -r line < "$test_dir/$file"
        [[ "$line" == "generated $generation" ]] || fail "$suite/$name: $file contains stale or partial output"
    fi
}

passed() {
    checks=$((checks + 1))
    printf 'ok %d - %s/%s\n' "$checks" "$suite" "$name"
}

# Each row drives a real .pass, .fail, or .fail_translate prerequisite chain.
for suite_name in shared base; do
    categories='PASS TODO_PASS'
    if [[ "$suite_name" == shared ]]; then categories+=' TODO_TRANSLATE'; fi
    for category in $categories; do
        for scenario in positive compiler-error translator-error partial-output no-output; do
            new_case "$suite_name" "$category-$scenario"
            expected=2
            expected_compiles=0
            output=absent
            case "$category" in
                PASS) pass_modules=Probe; target=Probe.pass ;;
                TODO_PASS) todo_pass_modules=Probe; target=Probe.fail ;;
                TODO_TRANSLATE) todo_translate_modules=Probe; target=Probe.fail_translate ;;
            esac
            case "$scenario" in
                positive|compiler-error)
                    output=present
                    expected_compiles=1
                    if [[ "$scenario" == compiler-error ]]; then compiler_mode=error; fi
                    if [[ "$category/$scenario" == PASS/positive || "$category/$scenario" == TODO_PASS/compiler-error ]]; then
                        expected=0
                    fi
                    ;;
                translator-error) translator_mode=error ;;
                partial-output) translator_mode=partial ;;
                no-output) translator_mode=missing ;;
            esac
            if [[ "$category" == TODO_TRANSLATE && "$output" == absent ]]; then expected=0; fi
            printf 'stale output\n' > "$test_dir/Probe.v"
            run_make "$expected" "$target"
            assert_calls translate Probe 1
            assert_calls compile Probe "$expected_compiles"
            assert_output Probe.v "$output"
            if [[ "$suite" == shared ]]; then
                assert_contains tools.log '<--target-version> <9.0>'
                assert_contains tools.log '<--edits> <sources/Probe/edits> <-N> <-e> <sources/renamings> <-i> <sources> <-o> <.> <--preamble> <sources/Probe/preamble.v> <--midamble> <sources/Probe/midamble.v> <sources/Probe.hs>'
            else
                assert_contains tools.log '<-e> <Probe/edits> <-e> <../../base/edits> <--iface-dir> <../../base/> <-o> <.> <-p> <Probe/preamble.v> <-m> <Probe/midamble.v> <Probe.hs>'
            fi
            passed
        done
    done
done

# Assume-old bypasses generation to exercise the missing-output .fail branch itself.
for suite_name in shared base; do
    new_case "$suite_name" known-failure-missing
    todo_pass_modules=Probe
    run_make 2 -o Probe.v Probe.fail
    assert_calls translate Probe 0
    assert_calls compile Probe 0
    assert_contains make.log 'missing'
    passed
done

# The target suffix and a substring match must not grant TODO_TRANSLATE tolerance.
for membership in unlisted near-match listed; do
    new_case shared "translation-membership-$membership"
    translator_mode=error
    expected=2
    case "$membership" in
        unlisted) : ;;
        near-match) todo_translate_modules=ProbeExtra ;;
        listed) todo_translate_modules='Before Probe After'; expected=0 ;;
    esac
    run_make "$expected" Probe.fail_translate
    assert_calls translate Probe 1
    assert_calls compile Probe 0
    assert_output Probe.v absent
    passed
done

new_case shared renamed-forced-refresh
generation=first
run_make 0 Renamed.v
assert_output Renamed.v present
generation=second
run_make 0 Renamed.v
assert_output Renamed.v present
assert_calls translate Renamed 2
assert_calls compile Renamed 0
assert_contains tools.log 'translate:Renamed <--target-version> <9.0> <-N> <-e> <sources/RenameMe/edits> <-e> <sources/renamings> <-i> <sources> <-o> <.> <sources/RenameMe.hs> <sources/RenameMeToo.hs>'
passed

for mode in error partial missing; do
    new_case shared "renamed-$mode"
    renamed_mode=$mode
    printf 'stale output\n' > "$test_dir/Renamed.v"
    run_make 2 Renamed.v
    assert_calls translate Renamed 1
    assert_calls compile Renamed 0
    assert_output Renamed.v absent
    passed
done

new_case shared rename-module-dependency
pass_modules=RenameModule
run_make 0 RenameModule.pass
assert_output Renamed.v present
assert_output RenameModule.v present
set -- 'translate:Renamed ' 'compile:Renamed ' 'translate:RenameModule ' 'compile:RenameModule '
while IFS= read -r line; do
    [[ $# -gt 0 ]] || fail "$suite/$name: unexpected tool call $line"
    [[ "$line" == "$1"* ]] || fail "$suite/$name: wrong dependency order at $line"
    shift
done < "$test_dir/tools.log"
[[ $# == 0 ]] || fail "$suite/$name: missing tool calls"
assert_contains tools.log 'compile:Renamed <-Q> <.> <> <Renamed.v>'
passed

new_case shared rename-module-partial-failure
pass_modules=RenameModule
renamed_mode=partial
run_make 2 RenameModule.pass
assert_calls translate Renamed 1
assert_calls compile Renamed 0
assert_calls translate RenameModule 0
assert_calls compile RenameModule 0
assert_output Renamed.v absent
assert_output RenameModule.v absent
passed

# No target argument: exercise the actual default main -> make -k all entry point.
for suite_name in shared base; do
    for outcome in failure success; do
        new_case "$suite_name" "default-main-$outcome"
        pass_modules=Control
        todo_pass_modules=Probe
        expected=2
        expected_compiles=0
        output=absent
        translator_mode=partial
        if [[ "$outcome" == success ]]; then
            expected=0
            expected_compiles=1
            output=present
            translator_mode=success
            compiler_mode=error
            if [[ "$suite" == shared ]]; then
                todo_translate_modules=Future
                fault_module=Future
                translator_mode=error
            fi
        fi
        run_make "$expected"
        assert_contains make.log ' -k all'
        assert_calls translate Control 1
        assert_calls compile Control 1
        assert_calls translate Probe 1
        assert_calls compile Probe "$expected_compiles"
        assert_output Probe.v "$output"
        assert_output Control.v present
        if [[ "$suite" == shared ]]; then
            # VFILES includes Renamed.v even when it is not in any category.
            assert_calls translate Renamed 1
            assert_calls compile Renamed 0
            assert_output Renamed.v present
            if [[ "$outcome" == success ]]; then
                assert_calls translate Future 1
                assert_calls compile Future 0
                assert_output Future.v absent
            fi
        fi
        passed
    done
done

printf 'Passed %d production-make harness checks.\n' "$checks"
