import Paper2.Y0FullEntryController

/-! Lane a-yao-owner-1, Y5 prerequisite: a UNIFORM clock for the ported
controller (map Y5: "the uniform `T` comes from monotone bounds of
`scalarBudget`, `selectorBudget`, `payloadBudget` and the route cap over
`z, g, l < counts` and `p ≤ K`").  The explicit total bound of
`physical_full_entry_controller` is bounded by `controllerUniform t lambda e`,
which depends only on `t, lambda, e` (the tape enters only through its fixed
length `tapeBitCount`).  No machine is built here. -/

namespace Paper2.YaoUniformClock

open EthInapproximability.CurrentPaper
open Paper2.YaoLowerBound
open Paper2.YaoLowerBound.Materialization
open Paper2.YaoLookup
open Paper2.YaoEntryParameterJoin
open Paper2.YaoParameterBank

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem exactTime_mono {r r' w w' c c' : ℕ} (hr : r ≤ r') (hw : w ≤ w') (hc : c ≤ c') :
    MatrixAddressMachine.exactTime r w c ≤ MatrixAddressMachine.exactTime r' w' c' := by
  unfold MatrixAddressMachine.exactTime
  have h1 : r * w ≤ r' * w' := Nat.mul_le_mul hr hw
  nlinarith [h1]

theorem setupBound_mono {z z' d g g' a : ℕ} (hz : z ≤ z') (hg : g ≤ g') :
    MatrixTemplateAddressSetup.bound 0 0 z d g a ≤
      MatrixTemplateAddressSetup.bound 0 0 z' d g' a := by
  unfold MatrixTemplateAddressSetup.bound
  have h1 := exactTime_mono (le_refl 0) (le_refl 0) (le_refl 0)
  have h2 := exactTime_mono hz (le_refl d) hg
  have h3 := exactTime_mono (show z * d + g ≤ z' * d + g' by nlinarith) (le_refl a) (le_refl 0)
  omega

theorem scalarBudget_mono (t lambda e : ℕ) {z z' g g' l l' p p' : ℕ}
    (hz : z ≤ z') (hg : g ≤ g') (hl : l ≤ l') (hp : p ≤ p') :
    scalarBudget t lambda e z g l p ≤ scalarBudget t lambda e z' g' l' p' := by
  unfold scalarBudget
  have h1 := setupBound_mono (d := fixedQ t) (a := paddedEdgeBits e) hz hg
  have h2 := exactTime_mono hl (le_refl (paddedEdgeCount e * fixedK t)) hp
  have h3 := exactTime_mono
    (le_refl (selectorCount t (paddedEdgeBits e) lambda * fixedQ t))
    (le_refl (paddedEdgeBits e))
    (show l * (paddedEdgeCount e * fixedK t) + p ≤ l' * (paddedEdgeCount e * fixedK t) + p' by
      have := Nat.mul_le_mul_right (paddedEdgeCount e * fixedK t) hl
      omega)
  omega

/-- The route cap of the controller statement. -/
def routeCap (t lambda e z g l p : ℕ) : ℕ :=
  2*((z * fixedQ t + g) * paddedEdgeBits e + paddedEdgeBits e +
    Paper2.YaoEntryParameterJoin.payloadBaseValue t lambda e l p + fixedK t + paddedEdgeCount e)+10

theorem routeCap_mono (t lambda e : ℕ) {z z' g g' l l' p p' : ℕ}
    (hz : z ≤ z') (hg : g ≤ g') (hl : l ≤ l') (hp : p ≤ p') :
    routeCap t lambda e z g l p ≤ routeCap t lambda e z' g' l' p' := by
  unfold routeCap Paper2.YaoEntryParameterJoin.payloadBaseValue
  have h1 : (z * fixedQ t + g) * paddedEdgeBits e ≤ (z' * fixedQ t + g') * paddedEdgeBits e :=
    Nat.mul_le_mul_right _ (by nlinarith)
  have h2 : l * (paddedEdgeCount e * fixedK t) ≤ l' * (paddedEdgeCount e * fixedK t) :=
    Nat.mul_le_mul_right _ hl
  omega

theorem selectorOffset_add_le (t b lambda : ℕ) (z : Fin (selectorCount t b lambda))
    (g : Fin (2 ^ (t - 1))) :
    Paper2.YaoPreservedFlatSlice.selectorOffset t b lambda z g + b ≤ tapeBitCount t b lambda := by
  unfold Paper2.YaoPreservedFlatSlice.selectorOffset
  have hz := z.isLt
  have hg := g.isLt
  have h1 : z.val * 2 ^ (t - 1) + g.val + 1 ≤ selectorCount t b lambda * 2 ^ (t - 1) := by
    have : (z.val + 1) * 2 ^ (t - 1) ≤ selectorCount t b lambda * 2 ^ (t - 1) :=
      Nat.mul_le_mul_right _ hz
    nlinarith
  have h2 : (z.val * 2 ^ (t - 1) + g.val) * b + b ≤ selectorCount t b lambda * 2 ^ (t - 1) * b := by
    have := Nat.mul_le_mul_right b h1
    nlinarith
  unfold tapeBitCount
  omega

theorem payloadBase_add_le (t b lambda : ℕ) (l : Fin (payloadCount t b lambda))
    (p : Fin (2 ^ t * 2 ^ t + 1)) :
    Paper2.YaoPayloadLoop.payloadBase t b lambda l p +
      2 ^ b * Paper2.YaoPayloadLoop.payloadStride t ≤
      tapeBitCount t b lambda + (2 ^ t * 2 ^ t + 1) := by
  unfold Paper2.YaoPayloadLoop.payloadBase Paper2.YaoPayloadLoop.payloadStride tapeBitCount
  have hl := l.isLt
  have hp := p.isLt
  have h1 : l.val * 2 ^ b * (2 ^ t * 2 ^ t + 1) + 2 ^ b * (2 ^ t * 2 ^ t + 1) ≤
      payloadCount t b lambda * 2 ^ b * (2 ^ t * 2 ^ t + 1) := by
    have : (l.val + 1) * (2 ^ b * (2 ^ t * 2 ^ t + 1)) ≤
        payloadCount t b lambda * (2 ^ b * (2 ^ t * 2 ^ t + 1)) := Nat.mul_le_mul_right _ hl
    nlinarith
  omega

/-- Tape-uniform selector budget. -/
def selectorUniform (t b lambda : ℕ) : ℕ :=
  b * (3 * tapeBitCount t b lambda + 3 * tapeBitCount t b lambda + 10) + 1

theorem selectorBudget_le (t b lambda : ℕ) (bits : SerializedTape t b lambda)
    (z : Fin (selectorCount t b lambda)) (g : Fin (2 ^ (t - 1))) :
    Paper2.YaoEntryComposition.selectorBudget t b lambda bits z g ≤ selectorUniform t b lambda := by
  unfold Paper2.YaoEntryComposition.selectorBudget selectorUniform
  rw [bits.property]
  have h := selectorOffset_add_le t b lambda z g
  have : 3 * (Paper2.YaoPreservedFlatSlice.selectorOffset t b lambda z g + b) +
      3 * tapeBitCount t b lambda + 10 ≤
      3 * tapeBitCount t b lambda + 3 * tapeBitCount t b lambda + 10 := by omega
  exact Nat.add_le_add_right (Nat.mul_le_mul_left b this) 1

/-- Tape-uniform payload budget. -/
def payloadUniform (t b lambda : ℕ) : ℕ :=
  (2 ^ b) * (3 * (tapeBitCount t b lambda + (2 ^ t * 2 ^ t + 1)) +
    3 * tapeBitCount t b lambda + 2 * (2 ^ t * 2 ^ t + 1) + 12) + 1 + ((2 ^ b) + 1)

theorem payloadBudget_le (t b lambda : ℕ) (bits : SerializedTape t b lambda)
    (l : Fin (payloadCount t b lambda)) (p : Fin (2 ^ t * 2 ^ t + 1)) :
    Paper2.YaoEntryComposition.payloadBudget t b lambda bits l p ≤ payloadUniform t b lambda := by
  unfold Paper2.YaoEntryComposition.payloadBudget payloadUniform
  rw [bits.property]
  have h := payloadBase_add_le t b lambda l p
  have hs : Paper2.YaoPayloadLoop.payloadStride t = 2 ^ t * 2 ^ t + 1 := rfl
  have : 3 * (Paper2.YaoPayloadLoop.payloadBase t b lambda l p +
      2 ^ b * Paper2.YaoPayloadLoop.payloadStride t) + 3 * tapeBitCount t b lambda +
      2 * Paper2.YaoPayloadLoop.payloadStride t + 12 ≤
      3 * (tapeBitCount t b lambda + (2 ^ t * 2 ^ t + 1)) + 3 * tapeBitCount t b lambda +
      2 * (2 ^ t * 2 ^ t + 1) + 12 := by rw [hs] at h ⊢; omega
  have := Nat.mul_le_mul_left (2 ^ b) this
  omega

/-- The uniform controller clock: depends only on `t, lambda, e`. -/
noncomputable def controllerUniform (t lambda e : ℕ) : ℕ :=
  (2 * tapeBitCount t (paddedEdgeBits e) lambda + 2) +
  scalarBudget t lambda e (selectorCount t (paddedEdgeBits e) lambda) (2 ^ (t - 1))
    (payloadCount t (paddedEdgeBits e) lambda) (2 ^ t * 2 ^ t) +
  routeCap t lambda e (selectorCount t (paddedEdgeBits e) lambda) (2 ^ (t - 1))
    (payloadCount t (paddedEdgeBits e) lambda) (2 ^ t * 2 ^ t) +
  (selectorUniform t (paddedEdgeBits e) lambda + payloadUniform t (paddedEdgeBits e) lambda +
    (6 * paddedEdgeCount e + 3 * paddedEdgeBits e + 6)) + 3

/-- The explicit total bound of `physical_full_entry_controller` (copied
literally from its statement) is at most `controllerUniform t lambda e`, for
every source, tape, vertex and typed index. -/
theorem controller_bound_le_uniform {v e : ℕ} (t lambda : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (bits : SerializedTape t (paddedEdgeBits e) lambda)
    (vertex : Fin v)
    (z : Fin (selectorCount t (paddedEdgeBits e) lambda))
    (g : Fin (2 ^ (t - 1))) (a : Fin (paddedEdgeCount e))
    (l : Fin (payloadCount t (paddedEdgeBits e) lambda)) :
    (2*tapeBitCount t (paddedEdgeBits e) lambda+2) +
        scalarBudget t lambda e z.val g.val l.val
          (positionEval (paddedEdgesEval edges) a vertex).val +
        (2*((z.val * fixedQ t + g.val) * paddedEdgeBits e +
          paddedEdgeBits e + Paper2.YaoEntryParameterJoin.payloadBaseValue t lambda e l.val
            (positionEval (paddedEdgesEval edges) a vertex).val +
          fixedK t + paddedEdgeCount e)+10) +
        (Paper2.YaoEntryComposition.selectorBudget t (paddedEdgeBits e) lambda bits z g +
          Paper2.YaoEntryComposition.payloadBudget t (paddedEdgeBits e) lambda bits l
            (positionEval (paddedEdgesEval edges) a vertex) +
          (6*paddedEdgeCount e + 3*paddedEdgeBits e + 6)) + 3 ≤
      controllerUniform t lambda e := by
  have hp := (positionEval (paddedEdgesEval edges) a vertex).isLt
  have h1 := scalarBudget_mono t lambda e (le_of_lt z.isLt) (le_of_lt g.isLt) (le_of_lt l.isLt)
    (show (positionEval (paddedEdgesEval edges) a vertex).val ≤ 2 ^ t * 2 ^ t by omega)
  have h2 := routeCap_mono t lambda e (le_of_lt z.isLt) (le_of_lt g.isLt) (le_of_lt l.isLt)
    (show (positionEval (paddedEdgesEval edges) a vertex).val ≤ 2 ^ t * 2 ^ t by omega)
  have h3 := selectorBudget_le t (paddedEdgeBits e) lambda bits z g
  have h4 := payloadBudget_le t (paddedEdgeBits e) lambda bits l
    (positionEval (paddedEdgesEval edges) a vertex)
  unfold routeCap at h2
  unfold controllerUniform routeCap
  omega

#print axioms scalarBudget_mono
#print axioms selectorBudget_le
#print axioms payloadBudget_le
#print axioms controller_bound_le_uniform

end Paper2.YaoUniformClock
