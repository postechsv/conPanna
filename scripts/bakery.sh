#!/usr/bin/env bash
# Re-check the Bakery certificates from scratch (not the cached build) and print the result.
#   scripts/bakery.sh          run the check, then print the result
#   scripts/bakery.sh result   print the result of the last run
# The check runs under a 5 GB memory limit (this machine has 7 GB).

ROOT=/home/byhoson/workspace/conPanna
FILE=examples/Bakery/cert.lean
LOG=/home/byhoson/workspace/conPanna/scripts/logs/bakery.log

print_result() {
  if [ ! -f "$LOG" ]; then
    echo "no result yet: run scripts/bakery.sh"
    exit 1
  fi
  status=$(sed -n 's/^# exit //p' "$LOG")
  secs=$(sed -n 's/^# time //p' "$LOG")
  when=$(sed -n 's/^# date //p' "$LOG")
  proofs=$(grep -c "certify_comp" "$ROOT/$FILE")
  errors=$(grep -c "error:" "$LOG")
  echo "Bakery ($FILE), run at $when"
  echo "  certify_comp proofs: $proofs"
  echo "  errors:              $errors"
  echo "  time:                ${secs}s"
  if [ "$status" = "0" ] && [ "$errors" = "0" ]; then
    echo "  result:              PASS"
  else
    echo "  result:              FAIL (exit $status)"
    grep -A3 "error:" "$LOG" | head -40
  fi
}

if [ "$1" = "result" ]; then
  print_result
  exit
fi

mkdir -p /home/byhoson/workspace/conPanna/scripts/logs
cd "$ROOT" || exit 1
start=$(date +%s)
systemd-run --user --scope -q -p MemoryMax=5G -p MemorySwapMax=0 \
  lake env lean "$FILE" > "$LOG" 2>&1
status=$?
{
  echo "# exit $status"
  echo "# time $(( $(date +%s) - start ))"
  echo "# date $(date '+%Y-%m-%d %H:%M:%S')"
} >> "$LOG"
print_result
