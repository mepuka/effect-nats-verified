# Assurance review — Stage A r3.1 at `e43d8e4`

- **Date:** 2026-08-23
- **Reviewed commit:** `e43d8e4f64061f95f90cc82e50ae13eaab58d49e`
- **Parent:** `cd5743a48bb51b7492e8b8a2e9a543d35d52ca5b`
- **Primary delta:** full five-axis review of the frozen Stage A r3.1 subscriber surface after
  proof cleanup, schema-2 replay, free-running sampling, and the r3.2 discriminator addition
- **Method:** `lean-assurance-review`; adversarial intent/model, theorem, proof-trust,
  implementation/refinement, and external-observation passes; fresh local gates
- **Mutation:** none to the reviewed model, proofs, fixtures, implementation, or briefs. This
  review is the only new file. Foldable citations are repository-relative at the reviewed commit;
  citations prefixed `ens:` are relative to `mepuka/effect-nats` at `e561092`, whose relevant
  implementation and r3.1 harness files are byte-identical to the harness merge `23566bd`.

## Headline verdict

**Accept snapshot r3.1 as a kernel-checked proof of the stated Stage A transition system, and
accept the schema-2 results as bounded compatibility evidence for the pinned memory and live
interpreters; do not describe the chain as a verified implementation refinement.**

Lean 4.33.0 accepts every frozen r3.1 statement over the project-defined `ReachableSub` system,
with logical dependencies contained in the package policy set. The three hypotheses introduced
during proof development are justified at their declared level: `SubShape` and strict stored
sequences are reachable-model invariants, while `ReachableSub` supplies the open/bounded facts used
by `lagged_iff` (`formal/effect_nats_substrate/docs/signature-snapshot.md:290-384`,
`:400-424`). The schema-2 harness then supplies a different kind of evidence: exact event and
final-history replay on memory for eight generated r3.1 traces; exact event and final-history
replay on `nats-server v2.14.5` for those traces under the documented live barrier; and 25 seeded
per-trace executions on each interpreter whose per-subscriber chunk histories belonged to the
generated prefix-closed acceptance sets (`ens:docs/research/lean-trace-live-findings.md:71-156`).

That is the strongest supported claim. It does not establish:

- a forward simulation, trace inclusion, or equivalence from either TypeScript interpreter to
  the Lean LTS;
- Stage A assumption A4, the per-subscriber independence assumption, or atomicity boundary E3;
- terminal progress of the free-running executions at the reviewed effect-nats pin;
- live `subscriberCount`, arbitrary scheduling without the `flush()` convention, clustered or
  persistent JetStream behavior, failure recovery, authorization, or other server versions;
- `PullWindow`, `Blocked`, T14′ liveness, acknowledgments, redelivery, or durable consumers;
- that random properties or replay tests are proofs, or that the memory interpreter is a server
  oracle.

## 1. Proof and trust verdict

### 1.1 Obligation chain

```text
source intent / Q1–Q3 / A4
       │
       ├── Subscriber + SelectReplay + Next ──> apply / ReachableSub
       │                                              │
       ├── SubInv + SubShape ──> per-label preservation
       │                                              │
       │                         reachableSub_core ───┤
       │                         stateInv_reachable ──┤
       │                         reachableSub_all ────┤
       │                                              v
       ├── SA1–SA7 + SA5h ───────────────> frozen r3.1 theorems
       │
       ├── SubTraces + SubPlacements ────> finite traces / chunk-history sets
       │                                              │
       └── deterministic schema-2 export ─────────────┤
                                                      v
                     gated replay + free-run samples + memory properties
```

The model encodes whole operations and whole pulls. `pullStep` drains an open/closing buffer in
one transition and needs at most one later transition to expose a stored failure
(`formal/effect_nats_substrate/EffectNatsSubstrate/Next.lean:73-87`). `SubPlacements` therefore
enumerates zero, one, or two pulls at every gap, preserves chunk boundaries, and proves that gated
histories are included while W1 and W2 each generate an excluded history
(`formal/effect_nats_substrate/EffectNatsSubstrate/SubPlacements.lean:35-74`, `:92-138`). Within
that model, the two-pull fuel is adequate; it is not a scheduler model.

The invariant proof follows the documented discipline. Per-label preservation feeds one bootstrap
induction for `stateInv_reachable`, capacity is a projection, and later reachable-state predicates
consume `reachableSub_all` (`formal/effect_nats_substrate/EffectNatsSubstrate/SubReachable.lean:198-226`;
`formal/effect_nats_substrate/docs/stage-a-proof-map.md:61-70`). SA7's public reachable theorem is
now a corollary of an explicit-premise lemma requiring exactly an open subscriber and the capacity
bound (`formal/effect_nats_substrate/EffectNatsSubstrate/SubStatements.lean:467-521`).

The three proof-discovered hypotheses do not conceal failed proof obligations:

- `register_observed` needs `SubShape` because an arbitrary list may already contain `nextId`;
  the shape is proved for reachable model states
  (`formal/effect_nats_substrate/EffectNatsSubstrate/SubStatements.lean:51-66`;
  `formal/effect_nats_substrate/docs/signature-snapshot.md:402-405`).
- `selectReplay_lastPerSubject` needs strictly increasing stored sequences; reachable core storage
  supplies that property (`formal/effect_nats_substrate/EffectNatsSubstrate/SubStatements.lean:68-104`;
  `formal/effect_nats_substrate/docs/signature-snapshot.md:406-409`).
- `lagged_iff` needs reachability because arbitrary closing or over-full subscribers falsify the
  bare statement; the approved amendment and its counterexamples are recorded
  (`formal/effect_nats_substrate/docs/signature-snapshot.md:417-424`).

### 1.2 Fresh gates

The package contents are byte-identical between reviewed commit `e43d8e4` and dispatch commit
`de6141b`. A clean build was run with the committed gate under Git Bash because the WSL `bash.exe`
does not inherit the Windows Elan path. Literal successful output was:

```text
$ lake --version
Lake version 5.0.0-src+d8b1897 (Lean version 4.33.0)

$ lake clean
$ bash scripts/gate.sh
Build completed successfully (27 jobs).
...
Build completed successfully (54 jobs).
gate: ok
```

The gate runs the build, forbidden-token sweep, axiom probe, and both deterministic exporter modes
(`formal/effect_nats_substrate/scripts/gate.sh:1-28`). The committed forbidden sweep produced no
output. An expanded mechanism search found no use of `sorry`, `sorryAx`, `admit`, `native_decide`,
`bv_decide`, custom `axiom`, `unsafe`, `extern`, `implemented_by`, or `set_option`; its sole textual
`admit` hit was the English phrase “admit decision” in an r4 invariant docstring, not a command.
`Main.lean` alone imports `Lean.Data.Json`; the library root imports every module, and the manifest
has no dependencies (`formal/effect_nats_substrate/Main.lean:1-27`;
`formal/effect_nats_substrate/lake-manifest.json:1-6`).

The axiom probe executed 186 `#print axioms` commands. Every frozen r3.1 theorem and the three
`SubPlacements` theorems is present in that probe
(`formal/effect_nats_substrate/scripts/Axioms.lean:100-181`). Literal summary and representative
Lean output:

```text
AXIOM_PROBE_DECLARATIONS=186
UNEXPECTED_AXIOM_LINES=0
'EffectNatsSubstrate.afterOp' depends on axioms: [propext]
'EffectNatsSubstrate.all_sub_negatives' depends on axioms: [propext, Classical.choice, Quot.sound]
'EffectNatsSubstrate.all_sub_traces' depends on axioms: [propext, Classical.choice, Quot.sound]
...
'EffectNatsSubstrate.RtScenario.counterexample_wrong_witness' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

Both exporter modes were executed twice by the gate with the same `--foldable-commit` value and
compared byte-for-byte. The literal hash receipt was:

```text
sequential A  D36F8F6DCD40BC5AD7C87AAC928C6E2326F638BACE2AFA8D91FF143A4CB5FB6C
sequential B  D36F8F6DCD40BC5AD7C87AAC928C6E2326F638BACE2AFA8D91FF143A4CB5FB6C
subscriber A  29C587DAE5B4699A8EB088F96087554A6BCBAFC5D250ACBF1127CDC165E05F85
subscriber B  29C587DAE5B4699A8EB088F96087554A6BCBAFC5D250ACBF1127CDC165E05F85
SEQ_CMP=True
SUB_CMP=True
```

The effect-nats client gate was run read-only in the owner's checkout at `602aac5`; the relevant
source, r3.1 fixture, harness, and findings paths have no diff from reviewed effect-nats commit
`e561092`. Literal output:

```text
$ nats-server --version
nats-server: v2.14.5
$ bun --version
1.3.14
$ bun run test:client
Test Files  20 passed (20)
Tests       186 passed (186)
```

At `e561092`, CI installs with `bun install --frozen-lockfile` and runs formatting, lint,
typecheck, and tests (`ens:.github/workflows/ci.yml:41-59`); the stale `packages/agents` path at
the earlier harness merge is already corrected in the reviewed effect-nats pin
(`ens:package.json:5-17`).

### 1.3 Proof-jury verdict

| Question | Verdict |
|---|---|
| Frozen r3.1 declarations accepted as stated | **PASS** |
| Intent obligations represented with their declared hypotheses | **PASS, conditional on Q1–Q3 and A4** |
| W1/W2 and negative witnesses discriminate the named wrong models/cases | **PASS within the finite model** |
| Standard-axiom and forbidden-mechanism policy for in-scope declarations | **PASS** |
| Schema-2 replay establishes recorded-history compatibility | **PASS for the pinned eight-trace/version boundary** |
| TypeScript-to-Lean refinement or A4 | **NOT ESTABLISHED** |

## 2. Findings

### F1 — A4 and runtime-step atomicity remain outside the r3.1 proof

**Class / severity / status:** `implementation-gap`, **major**, confirmed.

**Evidence:** the slice explicitly models whole pulls between whole operations while the program
can schedule pulls between `Queue.size`, `Queue.fail`, and `Queue.offer`; observational equivalence
to a whole-label sequence is assumption A4
(`research/2026-08-22-subscriber-stage-a.md:89-113`). The memory implementation confirms those
are separate effects inside fan-out (`ens:src/internal/JetStreamMemory.ts:178-203`). Stage B states
that free-running tests can find a bad history but cannot prove absence, and names E3—the atomicity
of each modeled runtime step—as outside both Lean and the live harness
(`research/2026-08-23-subscriber-stage-b.md:27-50`, `:336-350`). At the reviewed Foldable pin the
r4 theorem names are frozen but explicitly unproved
(`formal/effect_nats_substrate/docs/signature-snapshot.md:3-6`, `:528-571`).

**Correction:** read every r3.1 implementation-facing theorem as “provided Q1–Q3, A4, and E3.”
Prove the r4 queue laws, runtime invariant, commutations, `A4Inclusion`, and `A4Complete`; retain E3
as an explicit external trust assumption unless a lower-level runtime relation discharges it.

### F2 — per-subscriber placement soundness is still an assumption

**Class / severity / status:** `model-mismatch`, **major**, confirmed.

**Evidence:** `SubPlacements` computes one subscriber's pulls while every other label stays fixed
and calls cross-subscriber independence a theorem candidate
(`formal/effect_nats_substrate/EffectNatsSubstrate/SubPlacements.lean:20-30`). The slice gives a
credible locality argument—pull/unsubscribe update one subscriber and fan-out maps each subscriber
from the message and core alone—but labels no theorem for it
(`research/2026-08-22-subscriber-stage-a.md:567-582`). The local transition definitions support
that argument (`formal/effect_nats_substrate/EffectNatsSubstrate/Next.lean:105-114`, `:148-169`),
but `gated_in_outcomes` only decides the finite named traces; it is not the general independence
statement (`formal/effect_nats_substrate/EffectNatsSubstrate/SubPlacements.lean:110-124`). The r4
ledger assigns this gap to the not-yet-proved commutation theorem
(`research/2026-08-23-subscriber-stage-b.md:336-345`).

**Correction:** describe `freeRunning.outcomes[id]` as a per-subscriber acceptance set conditional
on the independence assumption. Discharge it with the r4 cross-subscriber commutation result before
using marginal membership as a theorem about joint fan-out executions.

### F3 — reviewed free-running evidence checks prefix membership, not terminal progress

**Class / severity / status:** `observational-gap`, **major**, confirmed.

**Evidence:** the effect-nats implementation at `23566bd` waits for 16 stable yields, interrupts
surviving fibers, and checks only membership in `freeRunning.outcomes`
(`ens:test/LeanSubscriberFreeRun.ts:177-193`, `:241-250`, `:256-305`). The generated acceptance set
is prefix-closed because taking no further pull is itself a placement; the later Foldable model
therefore adds `terminalPlacementsOf` specifically to distinguish a terminal quiescent history
from a prefix (`formal/effect_nats_substrate/EffectNatsSubstrate/SubPlacements.lean:97-108`;
`research/2026-08-22-subscriber-stage-a.md:556-573`). The reviewed effect-nats fixture is the
eight-trace r3.1 artifact produced at `0c11860` and contains no terminal set
(`ens:test/fixtures/lean/subscriber-traces.json:1267-1271`).

**Correction:** the pin-level claim is exactly “25 sampled histories per trace belonged to the
prefix-closed model set,” not “25 executions progressed to a terminal model placement.” Treat the
post-pin `terminalOutcomes` follow-up as stronger new evidence only after it is merged and pinned;
it does not retroactively strengthen `23566bd`.

### F4 — live exactness has an explicit observation and timing boundary

**Class / severity / status:** `observational-gap`, **minor**, confirmed.

**Evidence:** live replay uses a fresh server/connection/domain and calls `flush()` before each
modeled pull so prior callbacks arrive before a chunk is observed
(`ens:test/JetStreamLive.test.ts:14-47`;
`ens:test/LeanSubscriberReplay.ts:435-467`). The findings document explains that this prevents an
artificial one-entry chunk and records the exact versions
(`ens:docs/research/lean-trace-live-findings.md:76-94`). NATS `flush()` is a PING/PONG server round
trip, not proof of subscriber processing (`ens:docs/research/nats-js-reference.md:43-51`). Live
`subscriberCount` has no seam and thirteen non-empty assertions are explicitly skipped; memory
asserts them (`ens:docs/research/lean-trace-live-findings.md:96-125`).

**Correction:** say “event and final-history compatibility on `nats-server v2.14.5`, clients
3.4.0, Bun 1.3.14, and Effect rc.111, under the fresh-server and pre-pull flush convention.” Do not
include live subscriber counts or general scheduling in “exact.”

### F5 — eight exact live histories do not generalize to the live adapter

**Class / severity / status:** `implementation-gap`, **major**, confirmed.

**Evidence:** the reviewed findings correctly say the eight r3.1 registrations did not exercise
replay larger than capacity and therefore did not refute ADR-0008's replay-through-queue difference
(`ens:docs/research/lean-trace-live-findings.md:96-105`). The live adapter uses a bounded queue and
can fail it with `ConsumerLagged` during callback admission
(`ens:src/internal/JetStreamLive.ts:484-546`). Foldable r3.2 consequently adds the ninth
`saReplayLag` discriminator without changing any r3.1 statement
(`formal/effect_nats_substrate/docs/signature-snapshot.md:55-64`). The r3.1 fixture at the reviewed
effect-nats pin still contains exactly eight traces.

**Correction:** retain “all eight recorded r3.1 live histories matched” and reject “the live
adapter implements the r3.1 LTS.” The r3.2 trace is a deliberate differential boundary test, not a
model failure and not evidence of equivalence.

### F6 — the package-wide axiom-gate claim and theorem-count metadata are too strong

**Class / severity / status:** `proof-debt`, **minor**, confirmed.

**Evidence:** the snapshot says the package contains 230 non-private theorems
(`formal/effect_nats_substrate/docs/signature-snapshot.md:3-6`). A fresh declaration count over the
imported library found 242 public `theorem` declarations and one private theorem. The gate says it
checks every public theorem, but `scripts/Axioms.lean` describes its actual scope as proof-map §6
plus frozen-signature declarations (`formal/effect_nats_substrate/scripts/gate.sh:15-16`;
`formal/effect_nats_substrate/scripts/Axioms.lean:1-5`). It contains 186 commands, many for
definitions, and omits non-frozen public helpers such as `dropOldest_sublist`
(`formal/effect_nats_substrate/EffectNatsSubstrate/Proofs.lean:29`). Every in-scope r3.1 and
`SubPlacements` theorem is present, so this does not weaken the r3.1 proof verdict.

**Correction:** define the counting policy, update the header count, and either generate an axiom
probe for every public theorem or narrow the gate comment and package rule to the frozen public
surface. Keep the existing in-scope probe as a required subset.

### F7 — package CI retains one mutable action tag

**Class / severity / status:** `external-trust`, **minor**, confirmed.

**Evidence:** the prior unpinned `leanprover/lean-action@v1` gap is fixed: the workflow pins that
action to a full commit and invokes the complete package gate. `actions/checkout`, however, remains
the mutable `@v5` tag
(`formal/effect_nats_substrate/.github/workflows/lean_action_ci.yml:8-16`). The fresh local gate
does not depend on GitHub Actions, so this is a reproducibility risk, not contrary evidence about
the reviewed proof.

**Correction:** pin `actions/checkout` by full commit SHA and retain the release label as a comment,
matching the Lean action convention.

## 3. Referee and literature synthesis

Only two prior-art conclusions change the verdict. First, the history-variable treatment is a
legitimate conservative extension: `applyH_erase`, one-step lifting, reachable lifting, and the
global visible-history theorem make the ghost ledger proof-only rather than executable state
(`research/2026-08-22-subscriber-stage-a.md:352-382`). That supports acceptance of SA5h but supplies
no runtime refinement by itself.

Second, open-system and refinement literature changes the required next artifact, not the current
proof. A4 concerns internal publisher/consumer interleavings, so the proper assurance link is a
weak simulation or trace-inclusion argument over a finer queue/fan-out LTS. Stage B adopts exactly
that separation and states why empirical free-running runs can refute but cannot prove the link
(`research/2026-08-23-subscriber-stage-b.md:27-63`). No durable-consumer, session-type, or liveness
result transfers to this local queue slice without additional state, roles, fairness, and a proved
relation.

## 4. Evidence bundle

```text
proved       : every frozen Stage A r3.1 theorem at e43d8e4; gated_in_outcomes,
               w1_outside_outcomes, w2_outside_outcomes; clean Lean 4.33.0 build;
               in-scope axioms ⊆ {propext, Classical.choice, Quot.sound}
modelChecked : eight r3.1 traces plus the r3.2 ninth trace by kernel decide; named negatives;
               W1/W2 chunk-history exclusions; finite pull-placement enumeration
tested       : gated replay of eight r3.1 traces on memory and nats-server v2.14.5;
               gate self-check; 25 seeds × 8 traces × 2 interpreters with prefix membership;
               six memory properties × 200 generated runs; 186/186 fresh client tests
measured     : no performance, probability, scheduler-distribution, or deployment measurement
monitored    : no production assumption or deployment behavior is monitored by this evidence
assumed      : Q1–Q3 at r3.1; A4; per-subscriber independence; E3; declared carrier restrictions;
               fresh-server isolation; pre-pull flush convention; pinned runtime/server behavior
unknown      : universal interpreter→model refinement; joint fan-out interleavings; terminal
               progress at the reviewed effect-nats pin; live subscriberCount; other versions,
               clustering, persistence, failures, auth; PullWindow/Blocked and liveness
```

The six property names are `visible_sequences_strict`, `publish_visible (room)`,
`publish_visible (full) / lagged_iff`, `op_visible_frame`, `delete_ends`, and
`register_observed / selectReplay_mem`; each requests 200 runs
(`ens:test/JetStreamMemory.subscriber.properties.test.ts:120-225`, `:228-369`, `:412-458`). They
exercise one active subscriber at a time. Fan-out appears in fixtures, but neither these properties
nor per-subscriber acceptance-set membership proves correlated multi-subscriber scheduling.

The gated protocol itself matches the brief: chunk-level consumption arms a pending gate only
after `CaughtUp`, records `ConsumerLagged`/`StreamNotFound` fiber exits as `Failed`, releases once
per labeled pull, waits for exact event growth, and re-arms unless terminal
(`ens:test/LeanSubscriberReplay.ts:182-233`, `:282-337`, `:375-490`). The self-check queues two
messages behind one gate and observes one two-entry chunk after one release
(`ens:test/LeanSubscriberReplay.ts:508-575`). This validates the harness convention; it is not a
refinement theorem.

## 5. Per-axis and end-to-end verdict

| Axis | Verdict | Reason |
|---|---|---|
| Intent → formal model | **PASS WITH DECLARED ASSUMPTIONS** | obligations and restrictions match the corrected slice; A4 and independence remain explicit |
| Model → theorem | **PASS** | frozen statements have the intended strength; necessary hypotheses are logged; W1/W2 discriminate chunk behavior |
| Proof trust | **PASS IN SCOPE / MINOR GATE DEBT** | clean kernel build and allowed axioms for every in-scope theorem; package-wide inventory wording is broader than its probe |
| Implementation/refinement | **COMPATIBILITY ONLY** | finite gated replay and properties pass; no simulation/refinement relation; E3 remains external |
| External/deployment | **BOUNDED EVIDENCE** | one server/client stack under a flush convention; counts and deployment concerns are outside observation |
| End to end | **CONDITIONAL ACCEPTANCE** | “proved model + pinned compatibility evidence” is supported; “verified implementation” is not |

## 6. Recommended order of work

1. Prove the frozen Stage B1 queue laws, runtime invariant, commutation results,
   `A4Inclusion`, and `A4Complete`; rerun this review over the resulting r4 proof surface.
2. State the implementation relation explicitly: observables, simulation direction, quiescent
   points, source-step mapping, carrier validation, and what remains trusted as E3.
3. Merge and pin the terminal-outcome follow-up, then report terminal membership separately from
   prefix membership; preserve the r3.1 versus r3.2 evidence boundary.
4. Generate the package-wide axiom inventory (or narrow its contract), correct the theorem count,
   and pin the remaining CI action.
5. Extend properties or executable schedules only where they attack a named refinement premise;
   do not substitute larger random counts for the Stage B proof.
6. Keep `PullWindow`, `Blocked`, liveness/fairness, durability, acknowledgments, and recovery in
   later slices with their own models and assurance reviews.

## Correction log (append-only)

Correct pass of 2026-08-23 over F1–F7 by the Claude lane, each re-verified against the tree at Foldable `e43d8e4` (the review's pin) and at `main` (precedence tree > pass > document). Owner of every entry: the Claude lane.

- [claude | — | F1] DEFERRED to r4 (in flight) — the correction *is* the stage-B1 program: `A4Inclusion`, `A4Complete`, the queue laws, `RtInv`, commutation are frozen (snapshot r4) and being proved by the prover lane; E3 stays a named external-trust assumption (slice document §2.4), with E5 added at Pass B.
- [claude | research/2026-08-22-subscriber-stage-a.md §14, EffectNatsSubstrate/SubPlacements.lean docstring | F2] APPLIED — `freeRunning.outcomes[id]` described as a per-subscriber acceptance set conditional on the independence assumption, to be discharged by the abstract independence lemmas (P4a) and `RtCommute` (SB2); no theorem about joint executions is read off marginal membership.
- [claude | — | F3] APPLIED (post-pin) — the prefix-closure limitation at `23566bd` is as stated; the terminal-outcomes follow-up is merged at effect-nats `0876c41` (`terminalOutcomes` asserted for uninterrupted runs) and does not retroactively strengthen the reviewed pin.
- [claude | research/2026-08-23-effect-nats-lanes-plan.md | F4] APPLIED — the plan's status row now states live compatibility with its versions and the fresh-server / pre-pull `flush()` convention, `subscriberCount` excluded; the findings document already carried the boundary.
- [claude | — | F5] no change — no document claims the live adapter implements the r3.1 LTS; the ninth trace `sa-replay-lag` (r3.2) reached the replay-through-queue class on live and is recorded as a class-(a) divergence (effect-nats `0876c41`), a boundary test by design.
- [claude | scripts/AxiomsAll.lean, scripts/gate.sh, docs/signature-snapshot.md header | F6] APPLIED — an exhaustive axiom census enumerates every theorem constant in the `EffectNatsSubstrate` namespace from the environment (956 at this commit; 0 on non-standard axioms) and the gate runs it beside the named frozen-surface probe; counting policy stated (`grep -h '^theorem' EffectNatsSubstrate/*.lean`: 252 at this commit; the reviewer's 242 and the header's earlier 230 were counts under other conventions).
- [claude | .github/workflows/lean_action_ci.yml | F7] APPLIED — `actions/checkout` pinned to `fbc6f3992d24b796d5a048ff273f7fcc4a7b6c09` (`# v5`).
- done — applied 5, rejected 0, deferred 1, no change 1.
