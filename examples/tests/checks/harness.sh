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
        dependency_dir=
        while [[ $# -gt 0 ]]; do
            arg=$1
            case "$arg" in
                */RenameMe.hs|RenameMe.hs) renamed=true ;;
            esac
            case "$arg" in
                -o) shift; output=$1 ;;
                --dependency-dir) shift; dependency_dir=$1 ;;
                # The production GHC/Base rule merges sources ending in Maybe.hs.
                */ghc-internal/src/GHC/Internal/*.hs|ghc-internal/src/GHC/Internal/*.hs)
                    module=${arg#*ghc-internal/src/GHC/Internal/}
                    module=${module%.hs}
                    case "$module" in
                        Base|Maybe) module=GHC/Base ;;
                        Data/Semigroup/Internal) module=Data/SemigroupInternal ;;
                        Data/*|Control/*) : ;;
                        *) module=GHC/$module ;;
                    esac
                    ;;
                */base/src/*.hs|base/src/*.hs)
                    module=${arg#*base/src/}
                    module=${module%.hs}
                    ;;
                *.hs)
                    module=${arg##*/}; module=${module%.hs}
                    if [[ -f "$arg" ]]; then
                        while read -r keyword declared rest; do
                            if [[ "$keyword" == module ]]; then
                                module=${declared//./\/}
                                break
                            fi
                        done < "$arg"
                    fi
                    ;;
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
            success)
                printf 'generated %s\n' "${GENERATION:-initial}" > "$output/$module.v"
                printf 'generated %s\n' "${GENERATION:-initial}" > "$output/$module.h2ci"
                # Like the real translator, do not create the dependency directory.
                if [[ -n "$dependency_dir" ]]; then
                    printf '%s:\n' "$output/$module.v" > "$dependency_dir/${module//\//.}.mk"
                fi
                ;;
            error) exit 42 ;;
            partial) printf 'partial output\n' > "$output/$module.v"; exit 42 ;;
            missing) : ;;
            *) exit 99 ;;
        esac
        exit 0
        ;;
    --fake-compiler|--fake-coqc|--fake-rocq)
        compiler_command=()
        case "$1" in
            --fake-coqc) compiler_command=(coqc) ;;
            --fake-rocq) compiler_command=(rocq); [[ "${2:-}" == c ]] ;;
        esac
        shift
        compiler_args=("$@")
        source=
        local_load_path=false
        while [[ $# -gt 0 ]]; do
            case "$1" in
                -Q)
                    if [[ "$2" == . && "$3" == "" ]]; then local_load_path=true; fi
                    shift 2
                    ;;
                *.v) source=$1 ;;
            esac
            shift
        done
        test -n "$source"
        module=${source##*/}
        module=${module%.v}
        log_call compile "$module" ${compiler_command[@]+"${compiler_command[@]}"} "${compiler_args[@]}"
        test -f "$source"
        IFS= read -r line < "$source"
        [[ "$line" == "generated ${GENERATION:-initial}" ]] || exit 44
        if [[ "$module" == "${COMPILER_FAULT_MODULE:-Probe}" && ${COMPILER_MODE:-success} == error ]]; then
            exit 43
        fi
        if [[ "$module" == RocqFromImports || "$source" == Other/Coq/Init/Decimal.v ]]; then
            "$local_load_path" || exit 45
            if [[ "$module" == RocqFromImports ]]; then test -f Other/Coq/Init/Decimal.vo; fi
        fi
        : > "${source%.v}.vo"
        : > "${source%.v}.vok"
        : > "${source%.v}.vos"
        : > "${source%.v}.glob"
        : > "$(dirname "$source")/.${module}.aux"
        exit 0
        ;;
    --fake-lndir)
        shift
        log_call manual Prim "$@"
        # lndir requires an existing destination and resolves its source there.
        test -d "$2"
        mkdir -p "$2/GHC"
        for suffix in v h2ci; do
            cp "$2/$1/GHC/Prim.$suffix" "$2/GHC/Prim.$suffix"
        done
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
    version_options=
    import_options=
    compiler_options='<coqc>'
    if [[ "$suite" == shared ]]; then
        test_dir="$case_root/examples/tests"
        source=.
    elif [[ "$suite" == rocq-tests ]]; then
        test_dir="$case_root/examples/rocq9.0/tests"
        source=../../tests
        version_options='<--target-version> <9.0> '
        import_options='<-i> <../../tests> '
        compiler_options='<rocq> <c> <-w> <+deprecated-dirpath-Coq>'
    elif [[ "$suite" == rocq9 ]]; then
        test_dir="$case_root/examples/rocq9.0"
    elif [[ "$suite" == base-src8 ]]; then
        test_dir="$case_root/examples/base-src"
    else
        test_dir="$case_root/examples/base-tests"
        source=.
    fi
    mkdir -p "$test_dir/bin"
    ln -s "$workspace/common.mk" "$case_root/common.mk"
    for compiler in coqc rocq; do
        printf '#!/usr/bin/env bash\nexec bash "%s" --fake-%s "$@"\n' "$script" "$compiler" > "$test_dir/bin/$compiler"
        chmod +x "$test_dir/bin/$compiler"
    done
    if [[ "$suite" == rocq9 || "$suite" == base-src8 ]]; then
        mkdir -p "$case_root/examples/base-src"
        if [[ "$suite" == rocq9 ]]; then
            mkdir -p "$test_dir/base-src"
            ln -s "$workspace/examples/rocq9.0/Makefile" "$test_dir/Makefile"
            ln -s "$workspace/examples/rocq9.0/base-src/Makefile" "$test_dir/base-src/Makefile"
        else
            ln -s "$workspace/examples/base-src/Makefile" "$test_dir/Makefile"
        fi
        ln -s "$workspace/examples/base-src/modules.mk" "$case_root/examples/base-src/modules.mk"
        ln -s "$workspace/examples/base-src/base-rules.mk" "$case_root/examples/base-src/base-rules.mk"
        : > "$case_root/examples/base-src/edits"
        printf '#!/usr/bin/env bash\nexec bash "%s" --fake-coq-makefile "$@"\n' "$script" > "$test_dir/bin/coq_makefile"
        chmod +x "$test_dir/bin/coq_makefile"
        printf '#!/usr/bin/env bash\nexec bash "%s" --fake-lndir "$@"\n' "$script" > "$test_dir/bin/lndir"
        chmod +x "$test_dir/bin/lndir"
    else
        fixture_source=$source
        mkdir -p "$test_dir/$source/Probe" "$test_dir/$source/RenameMe"
        if [[ "$suite" == shared || "$suite" == rocq-tests ]]; then
            if [[ "$suite" == shared ]]; then
                ln -s "$workspace/examples/tests/Makefile" "$test_dir/Makefile"
            else
                ln -s "$workspace/examples/rocq9.0/tests/Makefile" "$test_dir/Makefile"
            fi
            ln -s "$workspace/examples/tests/test-rules.mk" "$test_dir/$source/test-rules.mk"
            mkdir -p "$test_dir/$source/Other/Coq/Init/Decimal"
            ln -s "$workspace/examples/tests/Other/Coq/Init/Decimal.hs" "$test_dir/$source/Other/Coq/Init/Decimal.hs"
            ln -s "$workspace/examples/tests/Other/Coq/Init/Decimal/edits" "$test_dir/$source/Other/Coq/Init/Decimal/edits"
            ln -s "$workspace/examples/tests/RocqFromImports.hs" "$test_dir/$source/RocqFromImports.hs"
            ln -s "$workspace/examples/tests/RocqFromImports" "$test_dir/$source/RocqFromImports"
        else
            ln -s "$workspace/examples/base-tests/Makefile" "$test_dir/Makefile"
        fi
        for module in Probe ProbeExtra Control Future RenameMe RenameMeToo RenameModule; do
            printf 'module %s where\n' "$module" > "$test_dir/$source/$module.hs"
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
    if [[ "$suite" == shared || "$suite" == rocq-tests ]]; then
        args+=("TODO_TRANSLATE=$todo_translate_modules")
    elif [[ "$suite" == rocq9 || "$suite" == base-src8 ]]; then
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

assert_call_order() {
    local line
    while IFS= read -r line; do
        [[ $# -gt 0 ]] || fail "$suite/$name: unexpected tool call $line"
        [[ "$line" == "$1 "* ]] || fail "$suite/$name: wrong dependency order at $line"
        shift
    done < "$test_dir/tools.log"
    [[ $# == 0 ]] || fail "$suite/$name: missing tool calls"
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

assert_base_project() {
    printf '%s\n' '-Q . ""' '' 'Data/Bool.v' '' 'GHC/Base.v' '' > "$test_dir/expected-project"
    cmp -s "$test_dir/expected-project" "$test_dir/$1" ||
        fail "$suite/$name: $1 changed the project-file contents or module order"
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
for suite_name in shared rocq-tests base; do
    categories='PASS TODO_PASS'
    if [[ "$suite_name" != base ]]; then categories+=' TODO_TRANSLATE'; fi
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
            if [[ "$suite" != base ]]; then
                assert_contains tools.log "translate:Probe ${version_options}<--edits> <$fixture_source/Probe/edits> <-N> <-e> <$fixture_source/renamings> ${import_options}<-o> <.> <--preamble> <$fixture_source/Probe/preamble.v> <--midamble> <$fixture_source/Probe/midamble.v> <$fixture_source/Probe.hs>"
                if [[ "$expected_compiles" == 1 ]]; then
                    assert_contains tools.log "compile:Probe $compiler_options <Probe.v>"
                fi
            else
                assert_contains tools.log '<-e> <Probe/edits> <-e> <../../base/edits> <--iface-dir> <../../base/> <-o> <.> <-p> <Probe/preamble.v> <-m> <Probe/midamble.v> <Probe.hs>'
            fi
            passed
        done
    done
done

# Assume-old bypasses generation to exercise the missing-output .fail branch itself.
for suite_name in shared rocq-tests base; do
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

for suite_name in shared rocq-tests; do
    new_case "$suite_name" renamed-forced-refresh
    generation=first
    run_make 0 Renamed.v
    assert_output Renamed.v present
    generation=second
    run_make 0 Renamed.v
    assert_output Renamed.v present
    assert_calls translate Renamed 2
    assert_calls compile Renamed 0
    assert_contains tools.log "translate:Renamed ${version_options}<-N> <-e> <$fixture_source/RenameMe/edits> <-e> <$fixture_source/renamings> ${import_options}<-o> <.> <$fixture_source/RenameMe.hs> <$fixture_source/RenameMeToo.hs>"
    passed
done

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
assert_contains tools.log 'compile:Renamed <coqc> <-Q> <.> <> <Renamed.v>'
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

# The nested helper must retain its module path and compile before its consumer.
# Use both production wrappers' compiler, version, and source-path defaults.
for suite_name in shared rocq-tests; do
    for jobs in 1 2; do
        new_case "$suite_name" "from-imports-forced-j$jobs"
        pass_modules=RocqFromImports
        run_make 0 "-j$jobs" RocqFromImports.pass
        assert_output Other/Coq/Init/Decimal.v present
        assert_output Other/Coq/Init/Decimal.h2ci present
        assert_output RocqFromImports.v present
        generation=second
        run_make 0 "-j$jobs" RocqFromImports.pass
        assert_output Other/Coq/Init/Decimal.v present
        assert_output Other/Coq/Init/Decimal.h2ci present
        assert_output RocqFromImports.v present
        assert_output Decimal.v absent
        assert_output Decimal.h2ci absent
        assert_calls translate Other/Coq/Init/Decimal 2
        assert_calls translate RocqFromImports 2
        assert_calls compile Decimal 2
        assert_calls compile RocqFromImports 2
        assert_contains tools.log "translate:Other/Coq/Init/Decimal ${version_options}<-N> <-e> <$fixture_source/Other/Coq/Init/Decimal/edits> <-e> <$fixture_source/renamings> ${import_options}<-o> <.> <$fixture_source/Other/Coq/Init/Decimal.hs>"
        assert_contains tools.log "compile:Decimal $compiler_options <-Q> <.> <> <Other/Coq/Init/Decimal.v>"
        assert_contains tools.log "compile:RocqFromImports $compiler_options <-Q> <.> <> <RocqFromImports.v>"
        assert_call_order \
            translate:Other/Coq/Init/Decimal compile:Decimal translate:RocqFromImports compile:RocqFromImports \
            translate:Other/Coq/Init/Decimal compile:Decimal translate:RocqFromImports compile:RocqFromImports
        passed

        for mode in error partial missing compiler-error; do
            new_case "$suite_name" "from-imports-retry-j$jobs-$mode"
            pass_modules=RocqFromImports
            fault_module=Other/Coq/Init/Decimal
            expected_compiles=0
            output=absent
            if [[ "$mode" == compiler-error ]]; then
                compiler_fault_module=Decimal
                compiler_mode=error
                expected_compiles=1
                output=present
            else
                translator_mode=$mode
            fi
            mkdir -p "$test_dir/Other/Coq/Init"
            printf 'stale output\n' > "$test_dir/Other/Coq/Init/Decimal.v"
            run_make 2 "-j$jobs" RocqFromImports.pass
            assert_calls translate Other/Coq/Init/Decimal 1
            assert_calls compile Decimal "$expected_compiles"
            assert_calls translate RocqFromImports 0
            assert_calls compile RocqFromImports 0
            assert_output Other/Coq/Init/Decimal.v "$output"
            assert_output RocqFromImports.v absent

            translator_mode=success
            compiler_mode=success
            run_make 0 "-j$jobs" RocqFromImports.pass
            assert_calls translate Other/Coq/Init/Decimal 2
            assert_calls compile Decimal "$((expected_compiles + 1))"
            assert_calls translate RocqFromImports 1
            assert_calls compile RocqFromImports 1
            assert_output Other/Coq/Init/Decimal.v present
            assert_output RocqFromImports.v present
            passed
        done
    done
done

# No target argument: exercise the actual default main -> make -k all entry point.
for suite_name in shared rocq-tests base; do
    for outcome in failure success; do
        new_case "$suite_name" "default-main-$outcome"
        pass_modules=Control
        if [[ "$suite" != base ]]; then pass_modules+=' Renamed'; fi
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
            if [[ "$suite" != base ]]; then
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
        if [[ "$suite" != base ]]; then
            assert_calls translate Renamed 1
            assert_calls compile Renamed 1
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

# Direct translating targets must create deps, without going through vfiles.
for suite_name in rocq9 base-src8; do
    new_case "$suite_name" base-direct-target
    if [[ "$suite" == rocq9 ]]; then
        run_make 0 -j2 -C base-src ../base/GHC/Base.v
        output_dir=base
        dependency_file=base-src/deps/GHC.Base.mk
        dependency_target=../base/GHC/Base.v
    else
        run_make 0 -j2 ../../base/GHC/Base.v
        output_dir=../../base
        dependency_file=deps/GHC.Base.mk
        dependency_target=../../base/GHC/Base.v
        assert_contains tools.log 'translate:GHC/Base <-p> <Base_preamble.v> <--midamble> <Base_midamble.v> <-e> <edits> <-N> <-I> <gen-files> <-I> <ghc-internal/include> <--iface-dir> <../../base> <--dependency-dir> <deps> <-o> <../../base>'
    fi
    assert_output "$output_dir/GHC/Base.v" present
    assert_output "$output_dir/GHC/Base.h2ci" present
    assert_contains "$dependency_file" "$dependency_target:"
    assert_calls translate GHC/Base 1
    passed
done

# A fresh coq entry point must create OUT before lndir copies a manual module.
for jobs in 1 2; do
    new_case base-src8 "coq-fresh-manual-j$jobs"
    mkdir -p "$test_dir/manual/GHC"
    for suffix in v h2ci; do
        printf 'generated %s\n' "$generation" > "$test_dir/manual/GHC/Prim.$suffix"
    done
    run_make 0 "-j$jobs" HANDMOD=GHC/Prim coq
    assert_output ../../base/GHC/Prim.v present
    assert_output ../../base/GHC/Prim.h2ci present
    assert_calls manual Prim 1
    assert_calls coq_makefile base 1
    assert_calls compile Prim 1
    assert_calls compile Base 1
    assert_calls compile Bool 1
    passed
done

# The 8.20 entry point uses the same completion rules and preserves successful
# sources across a partial failure, including when a previous marker exists.
for jobs in 1 2; do
    for marker in missing existing; do
        new_case base-src8 "vfiles-retry-j$jobs-$marker"
        base_translations=2
        if [[ "$marker" == existing ]]; then
            run_make 0 "-j$jobs" vfiles
            rm "$test_dir/../../base/GHC/Base.v"
            base_translations=3
        fi
        translator_mode=partial
        fault_module=GHC/Base
        run_make 2 "-j$jobs" vfiles
        assert_output ../../base/_CoqProject absent
        assert_output ../../base/GHC/Base.v absent
        assert_output ../../base/Data/Bool.v present
        assert_calls coq_makefile base 0

        translator_mode=success
        run_make 0 "-j$jobs" vfiles
        assert_base_project ../../base/_CoqProject
        assert_output ../../base/GHC/Base.v present
        assert_calls translate GHC/Base "$base_translations"
        assert_calls translate Data/Bool 1

        run_make 0 "-j$jobs" coq
        assert_calls translate GHC/Base "$base_translations"
        assert_calls translate Data/Bool 1
        assert_calls coq_makefile base 1
        assert_calls compile Base 1
        assert_calls compile Bool 1
        passed
    done
done

# A failed vfiles request must not publish (or retain) a completion marker.
# Retrying the same command must finish the tree before top-level compilation.
for jobs in 1 2; do
    for entry in direct top; do
        for marker in missing existing; do
            new_case rocq9 "vfiles-retry-j$jobs-$entry-$marker"
            command=("-j$jobs")
            if [[ "$entry" == direct ]]; then command+=(-C base-src); fi
            command+=(vfiles)
            bool_translations=2
            if [[ "$marker" == existing ]]; then
                run_make 0 "${command[@]}"
                rm "$test_dir/base/Data/Bool.v"
                bool_translations=3
            fi
            translator_mode=partial
            fault_module=Data/Bool
            run_make 2 "${command[@]}"
            assert_output base/_CoqProject absent
            assert_output base/GHC/Base.v present
            assert_output base/Data/Bool.v absent
            assert_calls coq_makefile base 0

            translator_mode=success
            run_make 0 "${command[@]}"
            assert_base_project base/_CoqProject
            assert_output base/Data/Bool.v present
            assert_calls translate GHC/Base 1
            assert_calls translate Data/Bool "$bool_translations"

            run_make 0 "-j$jobs" base
            assert_calls translate GHC/Base 1
            assert_calls translate Data/Bool "$bool_translations"
            assert_calls coq_makefile base 1
            assert_calls compile Base 1
            assert_calls compile Bool 1
            passed
        done
    done
done

# A top-level base build must also recover immediately after either vfiles
# entry point fails, without asking the user to rerun generation explicitly.
for jobs in 1 2; do
    for entry in direct top; do
        new_case rocq9 "vfiles-to-base-j$jobs-$entry"
        command=("-j$jobs")
        if [[ "$entry" == direct ]]; then command+=(-C base-src); fi
        translator_mode=partial
        fault_module=Data/Bool
        run_make 2 "${command[@]}" vfiles
        translator_mode=success
        run_make 0 "-j$jobs" base
        assert_base_project base/_CoqProject
        assert_output base/GHC/Base.v present
        assert_output base/Data/Bool.v present
        assert_calls translate GHC/Base 1
        assert_calls translate Data/Bool 2
        assert_calls coq_makefile base 1
        assert_calls compile Base 1
        assert_calls compile Bool 1
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

# Clean must remove translator interfaces and every compiler side product,
# including nested helper outputs, while preserving source fixtures for a retry.
for suite_name in shared rocq-tests; do
    new_case "$suite_name" clean-rebuild
    pass_modules='Probe Renamed RocqFromImports'
    run_make 0 -j2
    for stem in Probe Renamed RocqFromImports Other/Coq/Init/Decimal; do
        for suffix in v h2ci vo vok vos glob; do
            [[ -f "$test_dir/$stem.$suffix" ]] || fail "$suite/$name: missing pre-clean artifact $stem.$suffix"
        done
    done
    for file in .Probe.aux .Renamed.aux .RocqFromImports.aux Other/Coq/Init/.Decimal.aux; do
        [[ -f "$test_dir/$file" ]] || fail "$suite/$name: missing pre-clean artifact $file"
    done
    run_make 0 clean
    for stem in Probe Renamed RocqFromImports Other/Coq/Init/Decimal; do
        for suffix in v h2ci vo vok vos glob; do assert_output "$stem.$suffix" absent; done
    done
    for file in .Probe.aux .Renamed.aux .RocqFromImports.aux Other/Coq/Init/.Decimal.aux; do
        assert_output "$file" absent
    done
    [[ -f "$test_dir/$fixture_source/Probe.hs" && -f "$test_dir/$fixture_source/Other/Coq/Init/Decimal.hs" ]] ||
        fail "$suite/$name: clean removed a source fixture"
    generation=second
    run_make 0 -j2
    for stem in Probe Renamed RocqFromImports Other/Coq/Init/Decimal; do
        assert_output "$stem.v" present
        assert_output "$stem.h2ci" present
        assert_calls translate "$stem" 2
    done
    assert_calls compile Probe 2
    assert_calls compile Renamed 2
    assert_calls compile Decimal 2
    assert_calls compile RocqFromImports 2
    passed
done

# The manual-copy path bypasses the translator, including its From-prefix rewrite.
new_case rocq9 manual-from-prefix
mkdir -p "$test_dir/../base-src/manual/GHC"
ln -s "$workspace/examples/base-src/manual/GHC/Enum.v" "$test_dir/../base-src/manual/GHC/Enum.v"
run_make 0 -C base-src HANDMOD=GHC/Enum ../base/GHC/Enum.v
assert_contains base/GHC/Enum.v 'From Stdlib Require Import ssreflect Lia.'
assert_calls translate GHC/Enum 0
passed

printf 'Passed %d harness checks.\n' "$checks"
