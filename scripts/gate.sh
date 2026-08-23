#!/usr/bin/env bash
# The package gate — proof-map §6. Run from anywhere; exits non-zero on any failure.
set -euo pipefail
cd "$(dirname "$0")/.."

# 1. Every module builds; no errors, no warnings.
lake build

# 2. No forbidden tokens under the library or in Main.
if grep -rn "sorry\|native_decide\|axiom\|unsafe\|set_option" EffectNatsSubstrate/ Main.lean; then
  echo "gate: forbidden token found" >&2
  exit 1
fi

# 3. Every public theorem rests on at most propext, Classical.choice, Quot.sound.
lake env lean scripts/Axioms.lean

# 4. The exporter is deterministic: two runs, same bytes (Foldable law 4).
COMMIT="$(git rev-parse HEAD)"
lake build effect_nats_traces
lake exe effect_nats_traces -- --foldable-commit "$COMMIT" > /tmp/gate-traces-a.json
lake exe effect_nats_traces -- --foldable-commit "$COMMIT" > /tmp/gate-traces-b.json
cmp /tmp/gate-traces-a.json /tmp/gate-traces-b.json
lake exe effect_nats_traces -- --subscriber --foldable-commit "$COMMIT" > /tmp/gate-sub-a.json
lake exe effect_nats_traces -- --subscriber --foldable-commit "$COMMIT" > /tmp/gate-sub-b.json
cmp /tmp/gate-sub-a.json /tmp/gate-sub-b.json

echo "gate: ok"
