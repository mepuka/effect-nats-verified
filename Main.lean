import EffectNatsSubstrate
import Lean.Data.Json

/-!
# Trace exporter

`lake exe effect_nats_traces [--foldable-commit <hash>]` prints `allTraces` as a
JSON fixture for the effect-nats replay harness. The output is a pure function
of the package sources and the optional argument: no timestamps, no paths, no
randomness (Foldable law 4). Steps with `replay := false` are omitted and
counted.

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

end Export

def main (rawArgs : List String) : IO UInt32 := do
  -- `lake exe effect_nats_traces -- …` forwards the `--` separator; accept both forms.
  let args := match rawArgs with
    | "--" :: rest => rest
    | rest => rest
  let commit := match args with
    | ["--foldable-commit", c] => some c
    | _ => none
  if args ≠ [] && commit.isNone then
    IO.eprintln "usage: effect_nats_traces [--foldable-commit <hash>]"
    return 2
  IO.println (Export.fixture commit).pretty
  return 0
