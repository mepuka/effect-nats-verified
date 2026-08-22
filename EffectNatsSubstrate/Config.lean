/-!
# Stream configuration: raw, validated, canonical

The wire/raw → validate → checked-core boundary for `StreamConfig`
(`effect-nats` `src/internal/JetStream.ts:10-16` @ `d06223f`).

The TS field `maxMessagesPerSubject` is a `number`; integrality is a
JSON-decoding obligation that lives with trace ingestion (deferred), so the raw
carrier here is `Int`. Validation rejects negative capacities as a typed
failure instead of letting them disappear through `number → Nat`: the memory
implementation treats a non-positive limit as unlimited
(`src/internal/JetStreamMemory.ts:166`), and the model makes `0 = unlimited`
the only encoding.

`ConfigEq` is the equality `step` uses for create-idempotence: structural, with
**order-sensitive** `subjects`, mirroring `sameConfig`
(`src/internal/JetStreamMemory.ts:44-49`) exactly. `canonicalize` (sorted,
deduplicated subjects) is defined for the future live-replay comparison and is
deliberately *not* used by `step`.
-/

namespace EffectNatsSubstrate

/-- Corpus convention (durable-workflow record, "Public carriers and
identities") asks for distinct identifier types. This slice carries only
stream sequences — consumer sequences, where the distinction becomes semantic,
arrive with the subscriber slice — so transparent abbreviations carry the
names until then. -/
abbrev StreamName := String
abbrev SubjectName := String
abbrev StreamSeq := Nat
/-- Opaque payload token; a payload hash in recorded traces. -/
abbrev PayloadHash := String

structure RawStreamConfig where
  name : StreamName
  subjects : List SubjectName
  maxMessagesPerSubject : Int
  allowRollup : Bool
  deriving Repr, DecidableEq

structure StreamConfig where
  name : StreamName
  subjects : List SubjectName
  /-- `0` means unlimited history. -/
  maxMessagesPerSubject : Nat
  allowRollup : Bool
  deriving Repr, DecidableEq

inductive ConfigError where
  | negativeCapacity (name : String) (value : Int)
  deriving Repr, DecidableEq

def validate (raw : RawStreamConfig) : Except ConfigError StreamConfig :=
  if 0 ≤ raw.maxMessagesPerSubject then
    .ok
      { name := raw.name
        subjects := raw.subjects
        maxMessagesPerSubject := raw.maxMessagesPerSubject.toNat
        allowRollup := raw.allowRollup }
  else
    .error (.negativeCapacity raw.name raw.maxMessagesPerSubject)

/-- Order-sensitive structural equality, the memory model's `sameConfig`. -/
def ConfigEq (a b : StreamConfig) : Prop := a = b

instance : DecidablePred fun p : StreamConfig × StreamConfig => ConfigEq p.1 p.2 :=
  fun p => inferInstanceAs (Decidable (p.1 = p.2))

def canonicalize (c : StreamConfig) : StreamConfig :=
  { c with subjects := (c.subjects.mergeSort (fun a b => decide (a ≤ b))).eraseDups }

/-- Validator soundness: a validated config changes nothing but the capacity
carrier, and the capacity round-trips to the raw value. -/
theorem validate_ok_sound {raw : RawStreamConfig} {c : StreamConfig}
    (h : validate raw = .ok c) :
    c.name = raw.name ∧ c.subjects = raw.subjects ∧ c.allowRollup = raw.allowRollup
      ∧ (c.maxMessagesPerSubject : Int) = raw.maxMessagesPerSubject := by
  unfold validate at h
  split at h
  next hnn =>
    cases h
    exact ⟨rfl, rfl, rfl, Int.toNat_of_nonneg hnn⟩
  next => cases h

/-- Validator completeness on the rejected region: negative capacity is a typed
decoding failure. -/
theorem validate_rejects_negative {raw : RawStreamConfig}
    (h : raw.maxMessagesPerSubject < 0) :
    validate raw = .error (.negativeCapacity raw.name raw.maxMessagesPerSubject) := by
  unfold validate
  rw [if_neg (by omega)]

end EffectNatsSubstrate
