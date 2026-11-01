#!/bin/sh
# Run from v2/lean. Rebuild imports before asking Lean about theorem assumptions.
set -eu
lake build --wfail
lake env lean CheckAxioms.lean
