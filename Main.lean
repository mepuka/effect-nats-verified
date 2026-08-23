import EffectNatsSubstrate
import Lean.Data.Json

/-!
# Trace exporter

`lake exe effect_nats_traces [--subscriber] [--foldable-commit <hash>]` prints a
JSON fixture for the effect-nats replay harness: by default `allTraces` (schema 1,
the sequential core); with `--subscriber`, `allSubTraces` (schema 2, the stage-A
subscriber traces with their pull labels and free-running acceptance sets —
slice document §14). The output is a pure function
of the package sources and the optional argument: no timestamps, no paths, no
randomness (Foldable law 4). Schema-1 steps with `replay := false` are omitted
and counted; every schema-2 step is realisable.

Encoding contract (read by the harness):

- sequences are decimal **strings** (proposal §3.1); `maxMessagesPerSubject` and
  `timestampMillis` are JSON numbers;
- payloads are opaque tokens, sent as UTF-8 bytes and decoded back;
- headers are `[key, value]` pairs in publish order;
- error tags are the seam's `_tag` names; `compare.ignore` lists the fields the
  harness must not compare (`timestampMillis`: the model carries it as input,
  the interpreters stamp their own clocks).
-/

open Lean EffectNatsSubstrate

namespace Export

def seq (n : Nat) : Json := Json.str (toString n)

def headers (hs : List (String × String)) : Json :=
  Json.arr (hs.map (fun p => Json.arr #[Json.str p.1, Json.str p.2])).toArray

def rawConfig (c : RawStreamConfig) : Json :=
  Json.mkObj
    [ ("name", Json.str c.name)
    , ("subjects", Json.arr (c.subjects.map Json.str).toArray)
    , ("maxMessagesPerSubject", toJson c.maxMessagesPerSubject)
    , ("allowRollup", toJson c.allowRollup) ]

def config (c : StreamConfig) : Json :=
  Json.mkObj
    [ ("name", Json.str c.name)
    , ("subjects", Json.arr (c.subjects.map Json.str).toArray)
    , ("maxMessagesPerSubject", toJson c.maxMessagesPerSubject)
    , ("allowRollup", toJson c.allowRollup) ]

def message (m : StoredMessage) : Json :=
  Json.mkObj
    [ ("subject", Json.str m.subject)
    , ("sequence", seq m.sequence)
    , ("payload", Json.str m.payload)
    , ("headers", headers m.headers)
    , ("timestampMillis", toJson m.timestampMillis) ]

def op : Op → Json
  | .createStream raw => Json.mkObj [("op", "createStream"), ("config", rawConfig raw)]
  | .getStream name => Json.mkObj [("op", "getStream"), ("name", Json.str name)]
  | .deleteStream name => Json.mkObj [("op", "deleteStream"), ("name", Json.str name)]
  | .publish stream subject payload hs expected? now =>
    Json.mkObj
      [ ("op", "publish")
      , ("stream", Json.str stream)
      , ("subject", Json.str subject)
      , ("payload", Json.str payload)
      , ("headers", headers hs)
      , ("expectedLastSubjectSequence", match expected? with
          | some e => seq e
          | none => Json.null)
      , ("timestampMillis", toJson now) ]
  | .lastMessageForSubject stream subject =>
    Json.mkObj
      [ ("op", "lastMessageForSubject")
      , ("stream", Json.str stream)
      , ("subject", Json.str subject) ]

def ret : Ret → Json
  | .unit => Json.mkObj [("_tag", "unit")]
  | .config c => Json.mkObj [("_tag", "config"), ("config", config c)]
  | .sequence n => Json.mkObj [("_tag", "sequence"), ("sequence", seq n)]
  | .message m => Json.mkObj [("_tag", "message"), ("message", message m)]

def error : JSError → Json
  | .invalidConfig (.negativeCapacity name value) =>
    Json.mkObj [("_tag", "InvalidConfig"), ("name", Json.str name), ("value", toJson value)]
  | .streamNotFound stream => Json.mkObj [("_tag", "StreamNotFound"), ("stream", Json.str stream)]
  | .streamConfigConflict stream =>
    Json.mkObj [("_tag", "StreamConfigConflict"), ("stream", Json.str stream)]
  | .subjectNotBound stream subject =>
    Json.mkObj
      [("_tag", "SubjectNotBound"), ("stream", Json.str stream), ("subject", Json.str subject)]
  | .wrongLastSequence stream subject expected actual =>
    Json.mkObj
      [ ("_tag", "WrongLastSequence")
      , ("stream", Json.str stream)
      , ("subject", Json.str subject)
      , ("expected", seq expected)
      , ("actual", seq actual) ]
  | .rollupNotPermitted stream =>
    Json.mkObj [("_tag", "RollupNotPermitted"), ("stream", Json.str stream)]
  | .noMessageForSubject stream subject =>
    Json.mkObj
      [("_tag", "NoMessageForSubject"), ("stream", Json.str stream), ("subject", Json.str subject)]

def expect : Expect → Json
  | .ok r => Json.mkObj [("ok", ret r)]
  | .error e => Json.mkObj [("error", error e)]

def stepJson (t : TraceStep) : Json :=
  Json.mkObj [("op", op t.op), ("expect", expect t.expect)]

def view (v : ViewCheck) : Json :=
  Json.mkObj
    [ ("stream", Json.str v.stream)
    , ("subject", match v.subject with | some s => Json.str s | none => Json.null)
    , ("payloads", Json.arr (v.payloads.map Json.str).toArray) ]

def trace (t : Trace) : Json :=
  let replayed := t.steps.filter (·.replay)
  Json.mkObj
    [ ("name", Json.str t.name)
    , ("mirrors", Json.arr (t.mirrors.map Json.str).toArray)
    , ("steps", Json.arr (replayed.map stepJson).toArray)
    , ("modelOnlySteps", toJson (t.steps.length - replayed.length))
    , ("views", Json.arr (t.views.map view).toArray) ]

def fixture (foldableCommit : Option String) : Json :=
  Json.mkObj
    [ ("schema", toJson (1 : Nat))
    , ("producer", "EffectNatsSubstrate")
    , ("snapshot", "r2.1")
    , ("pin", "d06223f")
    , ("foldableCommit", match foldableCommit with | some c => Json.str c | none => Json.null)
    , ("compare", Json.mkObj [("ignore", Json.arr #[Json.str "timestampMillis"])])
    , ("traces", Json.arr (allTraces.map trace).toArray) ]

/-! ## Schema 2 — the stage-A subscriber traces (slice document §14) -/

def startPosition : StartPosition → Json
  | .allHistory => Json.mkObj [("_tag", "AllHistory")]
  | .lastPerSubject => Json.mkObj [("_tag", "LastPerSubject")]
  | .newOnly => Json.mkObj [("_tag", "NewOnly")]
  | .fromSequence n => Json.mkObj [("_tag", "FromSequence"), ("sequence", seq n)]
  | .afterSequence n => Json.mkObj [("_tag", "AfterSequence"), ("sequence", seq n)]

def policy : Policy → Json
  | .terminateOnLag n => Json.mkObj [("_tag", "TerminateOnLag"), ("messages", toJson n)]

def consumeOptions (o : ConsumeOptions) : Json :=
  Json.mkObj
    [ ("filters", Json.arr (o.filters.map Json.str).toArray)
    , ("start", startPosition o.start)
    , ("buffer", policy o.buffer) ]

/-- The seam's error classes and field names (`src/internal/JetStream.ts:88-90`,
`:130-133`): `lastDeliveredSequence` is the model's `lastDelivered`. -/
def subError : SubError → Json
  | .streamNotFound stream => Json.mkObj [("_tag", "StreamNotFound"), ("stream", Json.str stream)]
  | .consumerLagged stream lastDelivered =>
    Json.mkObj
      [ ("_tag", "ConsumerLagged")
      , ("stream", Json.str stream)
      , ("lastDeliveredSequence", seq lastDelivered) ]

/-- A consumer-visible event with its full message. -/
def observed : Observed → Json
  | .entry m => Json.mkObj [("_tag", "Entry"), ("message", message m)]
  | .caughtUp => Json.mkObj [("_tag", "CaughtUp")]
  | .failed e => Json.mkObj [("_tag", "Failed"), ("error", subError e)]

/-- The same event reduced to what a free-running history compares: the
sequence of an entry, the tag of `CaughtUp`, the error of a failure. -/
def observedSummary : Observed → Json
  | .entry m => Json.mkObj [("_tag", "Entry"), ("sequence", seq m.sequence)]
  | .caughtUp => Json.mkObj [("_tag", "CaughtUp")]
  | .failed e => Json.mkObj [("_tag", "Failed"), ("error", subError e)]

def events (es : List Observed) : Json := Json.arr (es.map observed).toArray

def counts (cs : List (StreamName × Nat)) : Json :=
  Json.arr (cs.map (fun p => Json.arr #[Json.str p.1, toJson p.2])).toArray

def subStep (t : SubTraceStep) : Json :=
  let fields : List (String × Json) :=
    match t.label with
    | .op o e => [("label", "op"), ("op", op o), ("expect", expect e)]
    | .register stream opts l₀ id e =>
      [ ("label", "register"), ("stream", Json.str stream), ("options", consumeOptions opts)
      , ("lastEnqueued", seq l₀), ("id", toJson id), ("expect", expect e)
      , ("events", events t.events) ]
    | .pull id => [("label", "pull"), ("id", toJson id), ("events", events t.events)]
    | .unsubscribe id => [("label", "unsubscribe"), ("id", toJson id)]
  Json.mkObj (fields ++ [("counts", counts t.counts)])

def history (h : History) : Json :=
  Json.arr (h.map (fun chunk => Json.arr (chunk.map observedSummary).toArray)).toArray

def subTrace (t : SubTrace) : Json :=
  Json.mkObj
    [ ("name", Json.str t.name)
    , ("mirrors", Json.arr (t.mirrors.map Json.str).toArray)
    , ("kind", "subscriber")
    , ("steps", Json.arr (t.steps.map subStep).toArray)
    , ("finalObserved", Json.arr (t.finalObserved.map (fun p =>
        Json.mkObj [("id", toJson p.1), ("events", events p.2)])).toArray)
    , ("freeRunning", Json.mkObj
        [ ("outcomes", Json.mkObj ((subIds t).map (fun id =>
            (toString id, Json.arr ((placementsOf t id).map history).toArray)))) ]) ]

def subFixture (foldableCommit : Option String) : Json :=
  Json.mkObj
    [ ("schema", toJson (2 : Nat))
    , ("producer", "EffectNatsSubstrate")
    , ("snapshot", "r3.1")
    , ("pin", "872bd7f")
    , ("foldableCommit", match foldableCommit with | some c => Json.str c | none => Json.null)
    , ("compare", Json.mkObj [("ignore", Json.arr #[Json.str "timestampMillis"])])
    , ("traces", Json.arr (allSubTraces.map subTrace).toArray) ]

end Export

structure Args where
  subscriber : Bool := false
  foldableCommit : Option String := none

def parseArgs : List String → Option Args
  | [] => some {}
  | "--subscriber" :: rest => (parseArgs rest).map (fun a => { a with subscriber := true })
  | "--foldable-commit" :: c :: rest =>
    (parseArgs rest).map (fun a => { a with foldableCommit := some c })
  | _ => none

def main (rawArgs : List String) : IO UInt32 := do
  -- `lake exe effect_nats_traces -- …` forwards the `--` separator; accept both forms.
  let args := match rawArgs with
    | "--" :: rest => rest
    | rest => rest
  match parseArgs args with
  | none =>
    IO.eprintln "usage: effect_nats_traces [--subscriber] [--foldable-commit <hash>]"
    return 2
  | some a =>
    IO.println (if a.subscriber then (Export.subFixture a.foldableCommit).pretty
                else (Export.fixture a.foldableCommit).pretty)
    return 0
