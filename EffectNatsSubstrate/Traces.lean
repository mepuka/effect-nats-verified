import EffectNatsSubstrate.Step

/-!
# Worked traces

The slice's replay artifact, kernel-checked with `decide` (proposal §3.3):

1. Positive — create → publish → publish under CAS → `lastMessageForSubject`
   returns the second message with sequence 2 (mirrors conformance C3/C4).
2. Rejected — re-create with differing config → `StreamConfigConflict`;
   publish to an unbound subject → `SubjectNotBound`; negative capacity →
   typed decoding failure (mirrors conformance C1/C2).
3. Prune / rollup / CAS — `maxMessagesPerSubject = 2` keeps the two most
   recent messages; rollup leaves only the new message for its subject and
   nothing else changes; rollup is gated by config; a stale CAS reports
   expected/actual (mirrors conformance C5/C6/C3). The conformance suite
   observes storage through `consume`, which this slice does not model; the
   trace inspects `forSubject` of the resulting state instead.

Payloads are opaque tokens (hashes in recorded traces). JSONL ingestion of
recorded test traces is deferred until the observation-ordering question is
answered (proposal §6).
-/

namespace EffectNatsSubstrate

def kvConfigRaw : RawStreamConfig :=
  { name := "KV_b"
    subjects := ["$KV.b.>"]
    maxMessagesPerSubject := 0
    allowRollup := true }

def positiveTraceChecks : Bool :=
  match step emptyState (.createStream kvConfigRaw) with
  | .ok (s1, .unit) =>
    match step s1 (.publish "KV_b" "$KV.b.k" "h1" [] none 100) with
    | .ok (s2, .sequence 1) =>
      match step s2 (.publish "KV_b" "$KV.b.k" "h2" [] (some 1) 200) with
      | .ok (s3, .sequence 2) =>
        match step s3 (.lastMessageForSubject "KV_b" "$KV.b.k") with
        | .ok (_, .message m) =>
          m == { subject := "$KV.b.k", sequence := 2, payload := "h2",
                 headers := [], timestampMillis := 200 }
        | _ => false
      | _ => false
    | _ => false
  | _ => false

theorem positive_trace : positiveTraceChecks = true := by decide

def rejectedTraceChecks : Bool :=
  match step emptyState (.createStream kvConfigRaw) with
  | .ok (s1, _) =>
    (match step s1 (.createStream { kvConfigRaw with maxMessagesPerSubject := 5 }) with
     | .error (.streamConfigConflict name) => name == "KV_b"
     | _ => false)
    && (match step s1 (.publish "KV_b" "$KV.other.k" "h" [] none 0) with
        | .error (.subjectNotBound stream subject) =>
          stream == "KV_b" && subject == "$KV.other.k"
        | _ => false)
    && (match validate { name := "bad", subjects := [], maxMessagesPerSubject := -1,
                         allowRollup := false } with
        | .error (.negativeCapacity name v) => name == "bad" && v == -1
        | _ => false)
  | .error _ => false

theorem rejected_trace : rejectedTraceChecks = true := by decide

def pruneRollupTraceChecks : Bool :=
  -- C5: limit 2; v1 v2 v3 on one subject → the subject view is [v2, v3]; last = v3 @ 3
  (match step emptyState
      (.createStream { name := "KV_p", subjects := ["$KV.p.>"],
                       maxMessagesPerSubject := 2, allowRollup := true }) with
   | .ok (s1, _) =>
     match step s1 (.publish "KV_p" "$KV.p.k" "v1" [] none 1) with
     | .ok (s2, .sequence 1) =>
       match step s2 (.publish "KV_p" "$KV.p.k" "v2" [] none 2) with
       | .ok (s3, .sequence 2) =>
         match step s3 (.publish "KV_p" "$KV.p.k" "v3" [] none 3) with
         | .ok (s4, .sequence 3) =>
           (match lookupStream s4 "KV_p" with
            | some st => (forSubject st.messages "$KV.p.k").map (·.payload) == ["v2", "v3"]
            | none => false)
           && (match step s4 (.lastMessageForSubject "KV_p" "$KV.p.k") with
               | .ok (_, .message m) => m.payload == "v3" && m.sequence == 3
               | _ => false)
           && (match step s4 (.lastMessageForSubject "KV_p" "$KV.p.none") with
               | .error (.noMessageForSubject stream subject) =>
                 stream == "KV_p" && subject == "$KV.p.none"
               | _ => false)
         | _ => false
       | _ => false
     | _ => false
   | _ => false)
  -- C6: rollup on k leaves exactly [purged]; other keeps [keep]; storage order survives
  && (match step emptyState (.createStream kvConfigRaw) with
      | .ok (s1, _) =>
        match step s1 (.publish "KV_b" "$KV.b.k" "v1" [] none 1) with
        | .ok (s2, _) =>
          match step s2 (.publish "KV_b" "$KV.b.other" "keep" [] none 2) with
          | .ok (s3, _) =>
            match step s3 (.publish "KV_b" "$KV.b.k" "purged" [("Nats-Rollup", "sub")] none 3) with
            | .ok (s4, .sequence 3) =>
              match lookupStream s4 "KV_b" with
              | some st =>
                (forSubject st.messages "$KV.b.k").map (·.payload) == ["purged"]
                  && (forSubject st.messages "$KV.b.other").map (·.payload) == ["keep"]
                  && st.messages.map (·.payload) == ["keep", "purged"]
              | none => false
            | _ => false
          | _ => false
        | _ => false
      | _ => false)
  -- C6: rollup is gated by config
  && (match step emptyState
          (.createStream { name := "KV_x", subjects := ["$KV.x.>"],
                           maxMessagesPerSubject := 0, allowRollup := false }) with
      | .ok (s1, _) =>
        match step s1 (.publish "KV_x" "$KV.x.k" "v" [("Nats-Rollup", "sub")] none 1) with
        | .error (.rollupNotPermitted name) => name == "KV_x"
        | _ => false
      | _ => false)
  -- C3: a stale CAS reports expected 0 / actual 1; CAS on 1 after an unrelated publish → 3
  && (match step emptyState (.createStream kvConfigRaw) with
      | .ok (s1, _) =>
        match step s1 (.publish "KV_b" "$KV.b.k" "v1" [] (some 0) 1) with
        | .ok (s2, .sequence 1) =>
          (match step s2 (.publish "KV_b" "$KV.b.k" "v2" [] (some 0) 2) with
           | .error (.wrongLastSequence stream subject expected actual) =>
             stream == "KV_b" && subject == "$KV.b.k" && expected == 0 && actual == 1
           | _ => false)
          && (match step s2 (.publish "KV_b" "$KV.b.other" "x" [] none 3) with
              | .ok (s3, .sequence 2) =>
                match step s3 (.publish "KV_b" "$KV.b.k" "v2" [] (some 1) 4) with
                | .ok (_, .sequence 3) => true
                | _ => false
              | _ => false)
        | _ => false
      | _ => false)

theorem prune_rollup_trace : pruneRollupTraceChecks = true := by decide

end EffectNatsSubstrate
