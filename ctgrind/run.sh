#!/bin/sh
# Constant-time check of the compiled code with valgrind memcheck.
#   1. The constant-time operations must produce no memcheck errors.
#   2. The positive control (variable-time reference code) must produce errors.
set -eu
cd "$(dirname "$0")"
lake build ctgrind
BIN=./.lake/build/bin/ctgrind

echo "== Constant-time operations"
if valgrind --error-exitcode=42 --track-origins=yes --num-callers=30 "$BIN"; then
  echo "PASS: no secret-dependent branches or memory accesses found"
else
  echo "FAIL: memcheck reported secret-dependent behaviour (see above)"
  exit 1
fi

echo "== Positive control (must fail)"
set +e
valgrind --error-exitcode=42 -q "$BIN" --control > control.log 2>&1
status=$?
set -e
errors=$(grep -c "depends on uninitialised\|Use of uninitialised" control.log || true)
if [ "$status" -eq 42 ] && [ "$errors" -gt 0 ]; then
  echo "PASS: memcheck flagged the variable-time code ($errors reports, see control.log)"
else
  echo "FAIL: the check did not detect the variable-time code (exit $status)"
  exit 1
fi
