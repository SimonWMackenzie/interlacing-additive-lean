import Paper2.YaoOperationalEntry
import Paper2.YaoMaterializationBounds

/-!
Scratch repair of the selector-read sharing gap in `YaoOperationalCombined`.
One recursive collection returns both selector values and its visit count;
the address decoder consumes those collected values without rereading tape.
The prepared source and payload readers likewise return value and visits in
one call. This is a structural access model, not a binary-machine time proof.
-/

namespace Paper2.YaoOperationalSharedScratch

open Paper2.YaoOperationalEntryScratch
open Paper2.YaoLookup Paper2.YaoLowerBound
open Paper2.YaoLowerBound.Materialization

/-- Each recursive branch calls its input reader once, retaining both its
bit and its visit count. No second pass over the input reader is used to
compute the cost. -/
def collectReads : (b : ℕ) → (Fin b → Option Bool × ℕ) →
    (Fin b → Bool) × ℕ
  | 0, _ => (Fin.elim0, 0)
  | b + 1, reader =>
      let head := reader 0
      let tail := collectReads b (fun i => reader i.succ)
      (Fin.cons (head.1.getD false) tail.1, head.2 + tail.2)

theorem collectReads_value (b : ℕ) (reader : Fin b → Option Bool × ℕ)
    (i : Fin b) :
    (collectReads b reader).1 i = (reader i).1.getD false := by
  induction b with
  | zero => exact Fin.elim0 i
  | succ b ih =>
      induction i using Fin.cases with
      | zero => simp [collectReads]
      | succ j => simpa [collectReads] using ih (fun i => reader i.succ) j

theorem collectReads_visits_le (b T : ℕ) (reader : Fin b → Option Bool × ℕ)
    (hreader : ∀ i, (reader i).2 ≤ T) :
    (collectReads b reader).2 ≤ b * T := by
  induction b with
  | zero => simp [collectReads]
  | succ b ih =>
      have hh := hreader 0
      have ht := ih (fun i => reader i.succ) (fun i => hreader i.succ)
      simp only [collectReads, Nat.succ_mul]
      omega

/-- One recursively collected selector block from the owner's literal tape. -/
def selectorReads {t b lambda : ℕ}
    (bits : SerializedTape t b lambda)
    (z : Fin (selectorCount t b lambda)) (g : Fin (2 ^ (t - 1))) :
    (Fin b → Bool) × ℕ :=
  collectReads b (fun i => readTapeOperational bits (.inl (z, g, i)))

theorem selectorReads_value {t b lambda : ℕ}
    (bits : SerializedTape t b lambda)
    (z : Fin (selectorCount t b lambda)) (g : Fin (2 ^ (t - 1))) :
    (selectorReads bits z g).1 =
      fun i => readTape t b lambda bits (.inl (z, g, i)) := by
  funext i
  rw [selectorReads, collectReads_value, readTapeOperational_value]
  rfl

theorem selectorReads_visits_le {t b lambda : ℕ}
    (bits : SerializedTape t b lambda)
    (z : Fin (selectorCount t b lambda)) (g : Fin (2 ^ (t - 1))) :
    (selectorReads bits z g).2 ≤ b * tapeBitCount t b lambda := by
  exact collectReads_visits_le b (tapeBitCount t b lambda)
    (fun i => readTapeOperational bits (.inl (z, g, i)))
    (fun i => readTapeOperational_visits_le bits (.inl (z, g, i)))

/-- The supplied prepared source is reused. The selector's bits and visits
come from one `collectReads` call, and the payload's bit and visits from one
`readTapeOperational` call. -/
def sharedEntry {v e : ℕ} (t lambda : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (source : List (List (Fin v)))
    (hsource : source = (prepareSource e edges).1)
    (bits : SerializedTape t (paddedEdgeBits e) lambda)
    (vertex : Fin v) (z : Fin (selectorCount t (paddedEdgeBits e) lambda))
    (g : Fin (2 ^ (t - 1))) (a : Fin (paddedEdgeCount e))
    (l : Fin (payloadCount t (paddedEdgeBits e) lambda)) : Bool × ℕ :=
  let selector := selectorReads bits z g
  let address := CappedSampler.bitsTicketEquiv (paddedEdgeBits e) selector.1
  let position := preparedPosition source a.val vertex
  let positionFin : Fin (2 ^ t * 2 ^ t + 1) := ⟨position.1, by
    have hp : position.1 = (positionEval (paddedEdgesEval edges) a vertex).val := by
      dsimp [position]
      rw [hsource]
      exact preparedPosition_eq_positionEval edges a vertex
    rw [hp]
    exact (positionEval (paddedEdgesEval edges) a vertex).isLt⟩
  let payload := readTapeOperational bits (.inr (l, address, positionFin))
  (payload.1.getD false, selector.2 + position.2 + payload.2)

theorem sharedEntry_value {v e : ℕ} (t lambda : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (source : List (List (Fin v)))
    (hsource : source = (prepareSource e edges).1)
    (bits : SerializedTape t (paddedEdgeBits e) lambda)
    (vertex : Fin v) (z : Fin (selectorCount t (paddedEdgeBits e) lambda))
    (g : Fin (2 ^ (t - 1))) (a : Fin (paddedEdgeCount e))
    (l : Fin (payloadCount t (paddedEdgeBits e) lambda)) :
    (sharedEntry t lambda edges source hsource bits vertex z g a l).1 =
      matrixFromTape t lambda edges
        (readTape t (paddedEdgeBits e) lambda bits) (vertex, z) (g, a, l) := by
  simp [sharedEntry, readTapeOperational_value, selectorReads_value,
    hsource, preparedPosition_eq_positionEval, matrixFromTape,
    matrixEval, positionEval]
  rfl

theorem sharedEntry_visits_le {v e : ℕ} (t lambda : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (source : List (List (Fin v)))
    (hsource : source = (prepareSource e edges).1)
    (bits : SerializedTape t (paddedEdgeBits e) lambda)
    (vertex : Fin v) (z : Fin (selectorCount t (paddedEdgeBits e) lambda))
    (g : Fin (2 ^ (t - 1))) (a : Fin (paddedEdgeCount e))
    (l : Fin (payloadCount t (paddedEdgeBits e) lambda)) :
    (sharedEntry t lambda edges source hsource bits vertex z g a l).2 ≤
      (paddedEdgeBits e + 1) * tapeBitCount t (paddedEdgeBits e) lambda +
        e + (2 ^ t * 2 ^ t) := by
  let b := paddedEdgeBits e
  let T := tapeBitCount t b lambda
  let selector := selectorReads bits z g
  let address := CappedSampler.bitsTicketEquiv b selector.1
  let position := preparedPosition source a.val vertex
  let positionFin : Fin (2 ^ t * 2 ^ t + 1) := ⟨position.1, by
    have hp : position.1 = (positionEval (paddedEdgesEval edges) a vertex).val := by
      dsimp [position]
      rw [hsource]
      exact preparedPosition_eq_positionEval edges a vertex
    rw [hp]
    exact (positionEval (paddedEdgesEval edges) a vertex).isLt⟩
  have hselector : selector.2 ≤ b * T := selectorReads_visits_le bits z g
  have hsourceCost : position.2 ≤ e + 2 ^ t * 2 ^ t := by
    dsimp [position]
    rw [hsource]
    exact preparedPosition_source_bound edges a.val vertex
  have hpayload : (readTapeOperational bits (.inr (l, address, positionFin))).2 ≤ T :=
    readTapeOperational_visits_le bits (.inr (l, address, positionFin))
  change selector.2 + position.2 +
      (readTapeOperational bits (.inr (l, address, positionFin))).2 ≤
    (b + 1) * T + e + (2 ^ t * 2 ^ t)
  have hbudget : (b + 1) * T = b * T + T := by ring
  rw [hbudget]
  omega

#print axioms collectReads_value
#print axioms collectReads_visits_le
#print axioms selectorReads_value
#print axioms sharedEntry_value
#print axioms sharedEntry_visits_le

end Paper2.YaoOperationalSharedScratch
