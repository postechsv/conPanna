#!/usr/bin/env bash
# Hardcoded walkthrough for union(P,Q) = singleton(wait(N)).
# Run from the repository root: bash scripts/certify-demo.sh
# Every command below can also be copied into a terminal and run individually.
# Parsing/certification logic stays in certifier.py; this is only a walkthrough.
# JSON artifacts are saved for the coordinator, never displayed in this demo.
# Stage times include preparation, process startup and displayed output.
set -euo pipefail

# STAGE 1: Prepare the fixed constructor module and native unify command.
# This Python command only writes files; it does not launch Maude.
printf '\n================ STAGE 1: Native unification ================\n'
printf 'Input: constructor model and equations.\nOutput: proposed unifiers; these are not yet certified.\n'
stage_started_ns=$(date +%s%N)
python3 -B certifier.py --prepare-native \
  --request examples/certification-request.json \
  --out .lake/build/certifier/inspection > /dev/null
printf '\n--- Native query ---\n'
cat .lake/build/certifier/inspection/01-native-query.maude
printf '\n--- Constructor module ---\n'
cat .lake/build/certifier/inspection/ctor.maude

# Run the displayed query. Expect TWO unifiers: P empty or Q empty.
# The subshell keeps memory/CPU limits local to this Maude call.
printf '\n--- Native Maude output ---\n'
(
  ulimit -d 786432
  ulimit -t 25
  timeout 30s maude -no-banner -no-advise -no-wrap \
    .lake/build/certifier/inspection/01-native.maude
) 2>&1 | tee .lake/build/certifier/inspection/01-native.stdout
awk -v start="$stage_started_ns" -v end="$(date +%s%N)" \
  'BEGIN { printf "Stage 1 time: %.3f s (wall-clock)\n", (end-start)/1000000000 }'

# STAGE 2: Parse the saved answers and prepare the second Maude command.
# This Python command does not launch Maude either.
printf '\n================ STAGE 2: Targeted certification ============\n'
printf 'Parse and freeze the native answers as Sigma.\nThe second call constructs soundness/completeness evidence for the SAME equations\nand that fixed Sigma; it does not rerun native unify.\n'
stage_started_ns=$(date +%s%N)
python3 -B certifier.py \
  --parse-native .lake/build/certifier/inspection/01-native.stdout \
  --out .lake/build/certifier/inspection > /dev/null
printf '\n--- Wrapper module ---\n'
cat .lake/build/certifier/inspection/wrapper.maude
printf '\n--- Actual certification command (encoded Maude terms) ---\n'
cat .lake/build/certifier/inspection/02-target-query.maude

# Execute certify(signature, scope, identity, equations, proposedAnswers).
printf '\n--- Targeted Maude output ---\n'
(
  ulimit -d 786432
  ulimit -t 25
  timeout 30s maude -no-banner -no-advise -no-wrap \
    .lake/build/certifier/inspection/02-target.maude
) 2>&1 | tee .lake/build/certifier/inspection/02-target.stdout \
  | sed '/^result State: result(/c\result State: [certificate evidence saved in 02-target.stdout]'
awk -v start="$stage_started_ns" -v end="$(date +%s%N)" \
  'BEGIN { printf "Stage 2 time: %.3f s (wall-clock)\n", (end-start)/1000000000 }'

# STAGE 3: Compile the saved evidence. No Maude or Lean process is launched.
printf '\n================ STAGE 3: Proof assembly ====================\n'
printf 'Input: Maude rule evidence. Output: applications of Lean proof rules.\nPython only assembles the proof; this script does NOT launch Lean or verify it.\nThe current Lean session must kernel-check it against its original problem.\n'
stage_started_ns=$(date +%s%N)
python3 -B certifier.py \
  --compile-trace .lake/build/certifier/inspection/02-target.stdout \
  --out .lake/build/certifier/inspection > /dev/null
printf 'Decoded evidence saved: .lake/build/certifier/inspection/03-trace.json\n'
printf 'Lean-ready proof saved: .lake/build/certifier/inspection/04-proof.json\n'
awk -v start="$stage_started_ns" -v end="$(date +%s%N)" \
  'BEGIN { printf "Stage 3 time: %.3f s (wall-clock)\n", (end-start)/1000000000 }'

printf '\n================ FINISHED ==================================\n'
printf 'Proof assembled, NOT kernel-checked here.\nAll artifacts: .lake/build/certifier/inspection/\nFull reply: .lake/build/certifier/inspection/result.json\n'
