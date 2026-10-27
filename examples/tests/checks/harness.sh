#!/usr/bin/env bash
# Exercise the production test makefiles without a Haskell or Coq toolchain.
set -euo pipefail

log_call() {
    local kind=$1 module=$2 args record
    shift 2
    # Append the complete record once so parallel tools cannot mix its fields.
    printf -v args ' <%s>' "$@"
    printf -v record '%s:%s%s\n' "$kind" "$module" "$args"
    printf '%s' "$record" >> "$HARNESS_LOG"
}

# Reuse this script as fake tools so the check needs no installed packages.
case "${1:-}" in
    --fake-translator)
        shift
        translator_args=("$@")
        module=
        renamed=false
        output=.
        while [[ $# -gt 0 ]]; do
            arg=$1
            case "$arg" in
                */RenameMe.hs|RenameMe.hs) renamed=true ;;
            esac
            case "$arg" in
                -o) shift; output=$1 ;;
                # The production GHC/Base rule merges sources ending in Maybe.hs.
                */ghc-internal/src/GHC/Internal/Maybe.hs) module=GHC/Base ;;
                */ghc-internal/src/GHC/Internal/*.hs)
                    module=${arg#*/ghc-internal/src/GHC/Internal/}
                    module=${module%.hs}
                    ;;
                *.hs) module=${arg##*/}; module=${module%.hs} ;;
            esac
            shift
        done
        test -n "$module"
        if "$renamed"; then module=Renamed; fi
        log_call translate "$module" "${translator_args[@]}"
        mode=success
        if [[ "$module" == Renamed ]]; then
            mode=${RENAMED_MODE:-success}
        elif [[ "$module" == "${FAULT_MODULE:-Probe}" ]]; then
            mode=${TRANSLATOR_MODE:-success}
        fi
        mkdir -p "$(dirname "$output/$module.v")"
        case "$mode" in
            success) printf 'generated %s\n' "${GENERATION:-initial}" > "$output/$module.v" ;;
            error) exit 42 ;;
            partial) printf 'partial output\n' > "$output/$module.v"; exit 42 ;;
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
        IFS= read -r line < "$source"
        [[ "$line" == "generated ${GENERATION:-initial}" ]] || exit 44
        if [[ "$module" == "${COMPILER_FAULT_MODULE:-Probe}" && ${COMPILER_MODE:-success} == error ]]; then
            exit 43
        fi
        : > "${source%.v}.vo"
        exit 0
        ;;
    --fake-coq-makefile)
        shift
        log_call coq_makefile base "$@"
        [[ "$*" == '-f _CoqProject -o Makefile' ]]
        sources=()
        while IFS= read -r line; do
            for source in $line; do
                case "$source" in *.v) sources+=("$source") ;; esac
            done
        done < _CoqProject
        [[ ${#sources[@]} -gt 0 ]]
        {
            printf 'all:'
            for source in "${sources[@]}"; do printf ' %s' "${source%.v}.vo"; done
            printf '\n\n%%.vo: %%.v\n\tbash "%s" --fake-compiler "$<"\n' "${BASH_SOURCE[0]}"
        } > Makefile
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
    elif [[ "$suite" == rocq9 ]]; then
        test_dir="$case_root/examples/rocq9.0"
    else
        test_dir="$case_root/examples/base-tests"
        source=.
    fi
    mkdir -p "$test_dir"
    ln -s "$workspace/common.mk" "$case_root/common.mk"
    if [[ "$suite" == rocq9 ]]; then
        mkdir -p "$test_dir/base-src" "$test_dir/bin" "$case_root/examples/base-src"
        ln -s "$workspace/examples/rocq9.0/Makefile" "$test_dir/Makefile"
        ln -s "$workspace/examples/rocq9.0/base-src/Makefile" "$test_dir/base-src/Makefile"
        ln -s "$workspace/examples/base-src/modules.mk" "$case_root/examples/base-src/modules.mk"
        : > "$case_root/examples/base-src/edits"
        printf '#!/usr/bin/env bash\nexec bash "%s" --fake-coq-makefile "$@"\n' "$script" > "$test_dir/bin/coq_makefile"
        chmod +x "$test_dir/bin/coq_makefile"
    else
        mkdir -p "$test_dir/$source/Probe" "$test_dir/$source/RenameMe"
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
    fi
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
    elif [[ "$suite" == rocq9 ]]; then
        # Keep the real module-list and dependency rules, with just two sources.
        args+=(
            HANDMOD= EARLY_GHC_INTERNAL_MODULES= EARLY_BASE_MODULES=
            GHC_INTERNAL_MODULES=Data/Bool GHC_INTERNAL_GHC_MODULES= BASE_MODULES=
            RENAMED= DROPIN= SPECIAL_MODULES=GHC/Base
        )
    else
        # base-tests has its own TYPECHECK rather than the shared COMPILER hook.
        args+=("TYPECHECK=bash \"$script\" --fake-compiler")
    fi
    if MAKEFLAGS='' MFLAGS='' GNUMAKEFLAGS='' MAKEFILES='' MAKELEVEL=0 \
        PATH="$test_dir/bin:$PATH" \
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

# Concurrent fake tools must each leave one complete, uniquely identifiable
# record. Separate output directories keep file writes out of this log check.
new_case shared concurrent-tool-logging
workers=32
pids=()
: > "$test_dir/expected.log"
for ((worker=1; worker<=workers; worker++)); do
    output="$test_dir/worker $worker"
    (
        export HARNESS_LOG="$test_dir/tools.log" GENERATION="$generation"
        bash "$script" --fake-translator -o "$output" -e "worker $worker" "Log$worker.hs" &&
            bash "$script" --fake-compiler -Q "$output" "" "$output/Log$worker.v"
    ) &
    pids+=("$!")
    printf '%s\n' \
        "translate:Log$worker <-o> <$output> <-e> <worker $worker> <Log$worker.hs>" \
        "compile:Log$worker <-Q> <$output> <> <$output/Log$worker.v>" >> "$test_dir/expected.log"
done
tool_failed=false
for pid in "${pids[@]}"; do
    wait "$pid" || tool_failed=true
done
if "$tool_failed"; then fail "$suite/$name: a concurrent fake tool failed"; fi

# Comparing sorted full records also rejects missing, duplicate, or extra calls.
LC_ALL=C sort "$test_dir/expected.log" > "$test_dir/expected.sorted"
LC_ALL=C sort "$test_dir/tools.log" > "$test_dir/tools.sorted"
cmp -s "$test_dir/expected.sorted" "$test_dir/tools.sorted" ||
    fail "$suite/$name: concurrent tool log records were corrupted"
for ((worker=1; worker<=workers; worker++)); do
    assert_output "worker $worker/Log$worker.v" present
    [[ -f "$test_dir/worker $worker/Log$worker.vo" ]] ||
        fail "$suite/$name: Log$worker was not compiled"
done
passed

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

# Exercise failed regeneration and an unchanged-command retry through both real
# Rocq makefiles. A later failure must retain Base.v but discard any failed .v.
for jobs in 1 2; do
    for failure in early later partial; do
        new_case rocq9 "base-retry-j$jobs-$failure"
        translator_mode=error
        fault_module=GHC/Base
        base_translations=2
        bool_translations=1
        if [[ "$failure" != early ]]; then
            fault_module=Data/Bool
            base_translations=1
            bool_translations=2
        fi
        if [[ "$failure" == partial ]]; then translator_mode=partial; fi
        run_make 2 "-j$jobs" base
        assert_contains make.log 'Error 42'
        assert_calls translate GHC/Base 1
        assert_calls coq_makefile base 0
        assert_calls compile Base 0
        assert_calls compile Bool 0
        assert_output base/Data/Bool.v absent
        if [[ "$failure" == early ]]; then
            assert_calls translate Data/Bool 0
            assert_output base/GHC/Base.v absent
        else
            assert_calls translate Data/Bool 1
            assert_output base/GHC/Base.v present
        fi

        translator_mode=success
        run_make 0 "-j$jobs" base
        assert_calls translate GHC/Base "$base_translations"
        assert_calls translate Data/Bool "$bool_translations"
        assert_calls coq_makefile base 1
        assert_calls compile Base 1
        assert_calls compile Bool 1
        assert_output base/GHC/Base.v present
        assert_output base/Data/Bool.v present

        # A complete convenience copy must not trigger another translation.
        run_make 0 "-j$jobs" base
        assert_calls translate GHC/Base "$base_translations"
        assert_calls translate Data/Bool "$bool_translations"
        assert_calls coq_makefile base 1
        assert_calls compile Base 1
        assert_calls compile Bool 1
        passed
    done
done

printf 'Passed %d harness checks.\n' "$checks"
