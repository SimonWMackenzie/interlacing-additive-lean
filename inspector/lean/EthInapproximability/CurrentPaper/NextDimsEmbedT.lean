import EthInapproximability.CurrentPaper.NextDimsMachineT
import EthInapproximability.CurrentPaper.MatrixWeightedFullBankBridge

/-! Lane owner:b-weighted-level-7, unit 2, segment 2c, piece 5 (the `t`-input variant of
`NextDimsEmbed`, for `NextDimsMachineT`: cell 8 holds `t = bins p * familySize p`, which is
the admitted persistent writer 16 `stagePrefixRows = s * L`, see `stagePrefixRows_eq`).

* `rows_identity`, `cols_identity`: the words left in cells 9 and 10 by
  `NextDimsMachine.dimsProgram`, on the inputs `dimsIn p V f`
  (`scale p, bins p, p.edges, p.columns, p.nextDepth, p.sourceConstant, V, p.rows, t`),
  are `EffectiveIteration.nextRows p` and, for `t = bins p * familySize p`,
  `EffectiveIteration.nextColumns p V`.
* `dims_embedded`: the fixed program on ANY global stack `K` through ANY embedding
  `ι : DS 65 ↪ K` whose nine input cells alias the cells holding the words (read in
  place, restored); exactly two global cells change (`ι (cell 9)`, `ι (cell 10)`).
Transport by the frozen `WeightedRawWords.region_run`. -/

namespace EthInapproximability.CurrentPaper.NextDimsEmbedT

open Turing BitMachineEncoding BitMachineStackEmbedding NextDimsStages NextDimsMachineT

noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

/-- The inputs of the level-`j+1` recompute read off a level-`j` parameter record. -/
def dimsIn (p : Parameters.Input) (V t : ℕ) : DimIn :=
  ⟨Parameters.scale p, Parameters.bins p, p.edges, p.columns, p.nextDepth, p.sourceConstant,
    V, p.rows, t⟩

theorem swap3 (b w : ℕ) : 1 + (b + w) = w + b + 1 := by omega
theorem swapsum (a v t : ℕ) : a + (v + t) = t + v + a := by omega

theorem rows_identity (p : Parameters.Input) (V t : ℕ) :
    rowsOut (dimsIn p V t) = EffectiveIteration.nextRows p := by
  simp only [rowsOut, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, dimsIn, Nat.add_zero]
  unfold EffectiveIteration.nextRows EffectiveIteration.protectedColumnCount Parameters.firstLength
    Parameters.firstWidth Parameters.firstExponent Parameters.secondWidth Parameters.secondExponent
    Parameters.outerWidth Parameters.outerExponent Parameters.restorationWidth
    Parameters.restorationExponent Parameters.restorationTarget
  simp only [Parameters.outerWidth, Parameters.outerExponent, sq]
  rw [swap3, Nat.add_comm 1 (Parameters.bins p)]

theorem cols_identity (p : Parameters.Input) (V : ℕ) :
    colsOut (dimsIn p V (Parameters.bins p * EffectiveIteration.familySize p)) = EffectiveIteration.nextColumns p V := by
  simp only [colsOut, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, dimsIn, Nat.add_zero]
  unfold EffectiveIteration.nextColumns EffectiveIteration.protectedRowCount
    Parameters.outerWidth Parameters.outerExponent Parameters.restorationWidth
    Parameters.restorationExponent Parameters.restorationTarget
  simp only [Parameters.outerWidth, Parameters.outerExponent, sq]
  rw [swapsum]

#print axioms rows_identity
#print axioms cols_identity

/-- The embedded recompute program on a global stack. -/
def dimsOn {K : Type} [DecidableEq K] (ι : DS 65 ↪ K) :=
  fun l => stackStmt ι (dimsProgram l)

theorem Sfin_other (x : DimIn) (k : Fin 65) (h9 : k ≠ 9) (h10 : k ≠ 10) : Sfin x k = S0 x k := by
  unfold Sfin
  rw [Function.update_of_ne h10, Function.update_of_ne h9]

theorem Sfin_nine (x : DimIn) : Sfin x 9 = rowsOut x := rfl
theorem Sfin_ten (x : DimIn) : Sfin x 10 = colsOut x := rfl

/-- The exit bank, pointwise. -/
theorem final_bank {K : Type} [DecidableEq K] (ι : DS 65 ↪ K) (G : K → List Bool) (x : DimIn)
    (hG : ∀ y, G (ι y) = U (S0 x) y) :
    bank ι G (U (Sfin x)) =
      Function.update (Function.update G (ι (cell 9)) (List.replicate (rowsOut x) true))
        (ι (cell 10)) (List.replicate (colsOut x) true) := by
  funext y
  by_cases hy : ∃ k, ι k = y
  · obtain ⟨k, rfl⟩ := hy
    rw [bank_at]
    by_cases h10 : k = cell 10
    · subst h10
      rw [Function.update_self, U_cell, Sfin_ten]
    · rw [Function.update_of_ne (fun e => h10 (ι.injective e))]
      by_cases h9 : k = cell 9
      · subst h9
        rw [Function.update_self, U_cell, Sfin_nine]
      · rw [Function.update_of_ne (fun e => h9 (ι.injective e)), hG k]
        rcases k with j | j
        · have hj9 : j ≠ 9 := fun e => h9 (by rw [e])
          have hj10 : j ≠ 10 := fun e => h10 (by rw [e])
          rw [U_cell, U_cell, Sfin_other x j hj9 hj10]
        · rw [U_log, U_log]
  · rw [bank_outside _ _ _ _ hy, Function.update_of_ne (fun e => hy ⟨cell 10, e.symm⟩),
      Function.update_of_ne (fun e => hy ⟨cell 9, e.symm⟩)]

#print axioms final_bank

theorem dims_embedded {K : Type} [DecidableEq K] (ι : DS 65 ↪ K) (G : K → List Bool) (x : DimIn)
    (hG : ∀ y, G (ι y) = U (S0 x) y) :
    ∃ t ≤ dimsBound x,
      ((advance (dimsOn ι))^[t])
          (⟨some dimsStart, dimsCtrl, G⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, dimsCtrl,
          Function.update (Function.update G (ι (cell 9)) (List.replicate (rowsOut x) true))
            (ι (cell 10)) (List.replicate (colsOut x) true)⟩ := by
  obtain ⟨t, ht, r⟩ := dims_run x
  have h := WeightedRawWords.region_run ι dimsProgram
    ⟨some dimsStart, dimsCtrl, U (S0 x)⟩ ⟨none, dimsCtrl, U (Sfin x)⟩
    t r G (fun k => (hG k).symm)
  dsimp only at h
  rw [final_bank ι G x hG] at h
  exact ⟨t, ht, h⟩

#print axioms dims_embedded

/-- Level form: on the inputs of a parameter record `p` with `t = bins p * familySize p` the embedded
program leaves `nextRows p` and `nextColumns p V`. -/
theorem next_dims_embedded {K : Type} [DecidableEq K] (ι : DS 65 ↪ K) (G : K → List Bool)
    (p : Parameters.Input) (V : ℕ)
    (hG : ∀ y, G (ι y) = U (S0 (dimsIn p V (Parameters.bins p * EffectiveIteration.familySize p))) y) :
    ∃ t ≤ dimsBound (dimsIn p V (Parameters.bins p * EffectiveIteration.familySize p)),
      ((advance (dimsOn ι))^[t])
          (⟨some dimsStart, dimsCtrl, G⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, dimsCtrl,
          Function.update (Function.update G (ι (cell 9))
              (List.replicate (EffectiveIteration.nextRows p) true))
            (ι (cell 10)) (List.replicate (EffectiveIteration.nextColumns p V) true)⟩ := by
  have h := dims_embedded ι G _ hG
  rw [rows_identity, cols_identity] at h
  exact h

#print axioms next_dims_embedded

section Persistent

open EthInapproximability.ParameterizedNP
open GuardedSourceGraph

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The admitted persistent writer fields of the level controller input `actualD` are the
dims-machine inputs of the SAME level parameters (definitional). -/
theorem actualD_inputs (G : EndpointGraph V E) (c b y i : ℕ) (M : Iteration.Matrix) :
    (ProtectedFullBankBridgeScratch.actualD G c b y i M).stagePrefixRows =
        Parameters.bins (Iteration.parameters G c b y i M) *
          EffectiveIteration.familySize (Iteration.parameters G c b y i M) ∧
      (ProtectedFullBankBridgeScratch.actualD G c b y i M).s =
        Parameters.bins (Iteration.parameters G c b y i M) ∧
      (ProtectedFullBankBridgeScratch.actualD G c b y i M).rx = (Iteration.parameters G c b y i M).rows ∧
      (ProtectedFullBankBridgeScratch.actualD G c b y i M).cy = (Iteration.parameters G c b y i M).columns ∧
      (ProtectedFullBankBridgeScratch.actualD G c b y i M).nv =
        4 * Parameters.bins (Iteration.parameters G c b y i M) * Fintype.card V :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

#print axioms actualD_inputs

/-- Run-parameter form (level `i` of the iteration started at `init`). -/
theorem actualD_run_inputs (G : EndpointGraph V E) (c b : ℕ) (init : Iteration.State) (i : ℕ) :
    (ProtectedFullBankBridgeScratch.actualD G c b (Iteration.run G c b init i).budget i
        (Iteration.run G c b init i).matrix).stagePrefixRows =
        Parameters.bins (EffectiveIteration.runParameters G c b init i) *
          EffectiveIteration.familySize (EffectiveIteration.runParameters G c b init i) ∧
      (ProtectedFullBankBridgeScratch.actualD G c b (Iteration.run G c b init i).budget i
        (Iteration.run G c b init i).matrix).s =
        Parameters.bins (EffectiveIteration.runParameters G c b init i) ∧
      (ProtectedFullBankBridgeScratch.actualD G c b (Iteration.run G c b init i).budget i
        (Iteration.run G c b init i).matrix).rx = (EffectiveIteration.runParameters G c b init i).rows ∧
      (ProtectedFullBankBridgeScratch.actualD G c b (Iteration.run G c b init i).budget i
        (Iteration.run G c b init i).matrix).cy = (EffectiveIteration.runParameters G c b init i).columns :=
  ⟨rfl, rfl, rfl, rfl⟩

#print axioms actualD_run_inputs

end Persistent

end
end EthInapproximability.CurrentPaper.NextDimsEmbedT
