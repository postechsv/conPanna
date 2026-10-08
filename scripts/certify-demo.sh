#!/usr/bin/env bash
# Hardcoded walkthrough for union(P,Q) = singleton(wait(N)).
# Run from the repository root: bash scripts/certify-demo.sh
# Every command below can also be copied into a terminal and run individually.
# Parsing/certification logic stays in certifier/certifier.py.
# JSON artifacts are saved for the coordinator, never displayed in this demo.
# Stage times include preparation, process startup and displayed output.
set -euo pipefail

# STAGE 1: Prepare the fixed constructor module and native unify command.
# This Python command only writes files; it does not launch Maude.
printf '\n================ STAGE 1: Native unification ================\n'
printf 'Input: constructor model and equations.\nOutput: proposed unifiers; these are not yet certified.\n'
stage_started_ns=$(date +%s%N)
python3 -B certifier/certifier.py --prepare-native \
  --ctor certifier/examples/bakery.maude \
  --unify 'unify in BAKERY-DEMO-NATIVE : union(P:Bag,Q:Bag) =? singleton(wait(N:Ticket)) .' \
  > /dev/null
printf '\n--- Native query ---\n'
cat certifier/.cache/01-native-query.maude
printf '\n--- Constructor module ---\n'
cat certifier/.cache/ctor.maude

# Run the displayed query. Expect TWO unifiers: P empty or Q empty.
# The subshell keeps memory/CPU limits local to this Maude call.
printf '\n--- Native Maude output ---\n'
(
  cd certifier/.cache
  ulimit -d 786432
  ulimit -t 25
  timeout 30s maude -no-banner -no-advise -no-wrap \
    01-native.maude
) 2>&1 | tee certifier/.cache/01-native.stdout
awk -v start="$stage_started_ns" -v end="$(date +%s%N)" \
  'BEGIN { printf "Stage 1 time: %.3f s (wall-clock)\n", (end-start)/1000000000 }'

# STAGE 2: Parse the saved answers and prepare the second Maude command.
# This Python command does not launch Maude either.
printf '\n================ STAGE 2: Targeted certification ============\n'
printf 'Parse and freeze the native answers as Sigma.\nThe second call constructs soundness/completeness evidence for the SAME equations\nand that fixed Sigma; it does not rerun native unify.\n'
stage_started_ns=$(date +%s%N)
python3 -B certifier/certifier.py \
  --parse-native certifier/.cache/01-native.stdout > /dev/null
printf '\n--- Wrapper module ---\n'
cat certifier/.cache/wrapper.maude
printf '\n--- Actual certification command (encoded Maude terms) ---\n'
cat certifier/.cache/02-target-query.maude

# Execute certify(signature, scope, identity, equations, proposedAnswers).
printf '\n--- Targeted Maude output ---\n'
(
  cd certifier/.cache
  ulimit -d 786432
  ulimit -t 25
  timeout 30s maude -no-banner -no-advise -no-wrap \
    02-target.maude
) 2>&1 | tee certifier/.cache/02-target.stdout \
  | sed '/^result State: result(/c\result State: [certificate evidence saved in 02-target.stdout]'
awk -v start="$stage_started_ns" -v end="$(date +%s%N)" \
  'BEGIN { printf "Stage 2 time: %.3f s (wall-clock)\n", (end-start)/1000000000 }'

# STAGE 3: Compile the saved evidence. No Maude or Lean process is launched.
printf '\n================ STAGE 3: Proof assembly ====================\n'
printf 'Input: Maude rule evidence. Output: applications of Lean proof rules.\nPython only assembles the proof; this script does NOT launch Lean or verify it.\nThe current Lean session must kernel-check it against its original problem.\n'
stage_started_ns=$(date +%s%N)
python3 -B certifier/certifier.py \
  --compile-trace certifier/.cache/02-target.stdout > /dev/null
printf 'Decoded evidence saved: certifier/.cache/03-trace.json\n'
printf 'Lean-ready proof saved: certifier/.cache/04-proof.json\n'
awk -v start="$stage_started_ns" -v end="$(date +%s%N)" \
  'BEGIN { printf "Stage 3 time: %.3f s (wall-clock)\n", (end-start)/1000000000 }'

printf '\n================ FINISHED ==================================\n'
printf 'Proof assembled, NOT kernel-checked here.\nAll artifacts: certifier/.cache/\nFull reply: certifier/.cache/result.json\n'
