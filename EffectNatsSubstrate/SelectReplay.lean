import EffectNatsSubstrate.Subscriber

/-!
# `selectReplay` — the registration snapshot

Transliteration of `selectReplay` (`src/internal/JetStreamMemory.ts:66-92` @
`872bd7f`): filter the stream's messages by the subscription's filters, then
pick by `StartPosition`. `LastPerSubject` is the implementation's "last message
of each subject, sorted by sequence"; because storage order is sequence order
(`reachable_sequences_strict`), that equals keeping, in storage order, each
matching message that is the last of its subject among the matches — the
form used here so that it reduces by `decide`. The equality with the sorted
`Map` construction is an obligation of the slice document (SA4), not assumed.
-/

namespace EffectNatsSubstrate

/-- `m` is the last message of its subject within `messages`. -/
def isLastOfSubject (messages : List StoredMessage) (m : StoredMessage) : Bool :=
  match lastForSubject messages m.subject with
  | some l => l.sequence == m.sequence
  | none => false

def selectReplay (messages : List StoredMessage) (opts : ConsumeOptions) :
    List StoredMessage :=
  let matching := messages.filter (fun m => matchesAny opts.filters m.subject)
  match opts.start with
  | .allHistory => matching
  | .newOnly => []
  | .fromSequence n => matching.filter (fun m => decide (n ≤ m.sequence))
  | .afterSequence n => matching.filter (fun m => decide (n < m.sequence))
  | .lastPerSubject => matching.filter (fun m => isLastOfSubject matching m)

/-- The consumer-visible prefix a registration materializes: the replay as
entries, then one `CaughtUp` (`:246-252`). -/
def replayObserved (messages : List StoredMessage) (opts : ConsumeOptions) : List Observed :=
  (selectReplay messages opts).map Observed.entry ++ [Observed.caughtUp]

end EffectNatsSubstrate
