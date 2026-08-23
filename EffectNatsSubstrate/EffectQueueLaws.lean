import EffectNatsSubstrate.EffectQueue

/-!
# The queue component's laws (stage B1, SB1)

Q1–Q3 of the stage-A slice document (§2.4) as theorems of `EffectQueue`
(statements frozen with snapshot r4): a pull takes the whole buffer; a failure
on a non-empty buffer keeps it and the exit is observed on the pull after the
drain; a shutdown discards the buffer; `size` is the buffer length while the
queue is not finished; `offer` admits below capacity on an open queue and is
refused on any other.
-/

namespace EffectNatsSubstrate

open EffectQueue

theorem takeAll_drains (q : EffectQueue) (h : q.status = .opened) (hne : q.buffer ≠ []) :
    q.takeAll = ({ q with buffer := [] }, .chunk q.buffer) := by
  unfold EffectQueue.takeAll
  rw [h]
  simp [List.isEmpty_eq_false_iff.mpr hne]

theorem takeAll_closing (q : EffectQueue) (e : SubError) (h : q.status = .closing e)
    (hne : q.buffer ≠ []) :
    q.takeAll = ({ q with buffer := [], status := .done e }, .chunk q.buffer) := by
  unfold EffectQueue.takeAll
  rw [h]
  simp [List.isEmpty_eq_false_iff.mpr hne]

theorem fail_empty (q : EffectQueue) (e : SubError) (h : q.status = .opened) (hb : q.buffer = []) :
    q.fail e = { q with status := .done e } := by
  unfold EffectQueue.fail
  rw [h]
  simp [hb]

theorem fail_nonempty (q : EffectQueue) (e : SubError) (h : q.status = .opened)
    (hb : q.buffer ≠ []) : q.fail e = { q with status := .closing e } := by
  unfold EffectQueue.fail
  rw [h]
  simp [List.isEmpty_eq_false_iff.mpr hb]

theorem exit_after_drain (q : EffectQueue) (e : SubError) (h : q.status = .done e) :
    q.takeAll = ({ q with status := .shutDown }, .exit e) := by
  unfold EffectQueue.takeAll
  rw [h]

theorem shutdown_clears (q : EffectQueue) : q.shutdown.buffer = [] ∧ q.shutdown.status = .shutDown :=
  ⟨rfl, rfl⟩

theorem size_eq_length (q : EffectQueue) (h : q.status = .opened ∨ ∃ e, q.status = .closing e) :
    q.size = q.buffer.length := by
  unfold EffectQueue.size
  rcases h with h | ⟨e, h⟩ <;> rw [h]

theorem offer_admits (cap : Nat) (q : EffectQueue) (m : StoredMessage) (h : q.status = .opened)
    (hr : q.buffer.length < cap) :
    q.offer cap m = ({ q with buffer := q.buffer ++ [m] }, .accepted) := by
  unfold EffectQueue.offer
  rw [h]
  simp [hr]

theorem offer_refused (cap : Nat) (q : EffectQueue) (m : StoredMessage) (h : q.status ≠ .opened) :
    q.offer cap m = (q, .refused) := by
  unfold EffectQueue.offer
  cases hs : q.status with
  | opened => exact absurd hs h
  | closing e => rfl
  | done e => rfl
  | shutDown => rfl

end EffectNatsSubstrate
