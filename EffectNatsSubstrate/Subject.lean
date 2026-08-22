/-!
# NATS subject matching

Transliterated from `effect-nats` `src/internal/Subject.ts:6-22` @ `d06223f`:
`*` matches exactly one token, `>` matches one or more trailing tokens, and both
act only as whole tokens — a `>` or `*` embedded in a longer token is a literal
character. A `>` filter token returns immediately on any non-empty remainder,
even when further filter tokens follow (mirroring the TS early return).
-/

namespace EffectNatsSubstrate

/-- Structural token splitter mirroring JS `"…".split(".")` — in particular
`"".split(".") = [""]`. Structural recursion (not `String.splitOn`, whose
well-founded recursion the kernel cannot reduce under `decide`). -/
def splitTokensAux : List Char → List Char → List String
  | [], acc => [String.ofList acc.reverse]
  | c :: cs, acc =>
    if c = '.' then String.ofList acc.reverse :: splitTokensAux cs []
    else splitTokensAux cs (c :: acc)

def splitTokens (s : String) : List String :=
  splitTokensAux s.toList []

def matchTokens : List String → List String → Bool
  | [], subject => subject.isEmpty
  | f :: fs, subject =>
    if f == ">" then !subject.isEmpty
    else
      match subject with
      | [] => false
      | s :: ss => (f == "*" || f == s) && matchTokens fs ss

def subjectMatches (filter subject : String) : Bool :=
  matchTokens (splitTokens filter) (splitTokens subject)

def matchesAny (filters : List String) (subject : String) : Bool :=
  filters.any (fun filter => subjectMatches filter subject)

end EffectNatsSubstrate
