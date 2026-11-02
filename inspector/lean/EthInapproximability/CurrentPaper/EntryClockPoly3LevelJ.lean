import EthInapproximability.CurrentPaper.EntryClockPolyLevelJ
import EthInapproximability.CurrentPaper.EntryWriter22J

/-!
# Lane owner:b-entry-clock-3, segment 2: the level-j writer-22 clock

The six identifications listed by lane entry-clock-2, against the ADMITTED level-j definitions
of lane entry-levelj-1 (`EntryWriter22J.writerBound_j` and its pieces, gate WAVE13B_B36), with
the admitted instance pieces of `EntryClockPolyPieces` at the admitted level instance
`EntryClockPoly.instL`:

* `boundA_j = boundAI (instL ..)`, `labBound_j T = labI (instL ..) + T + 1`,
  the `wordB` copy `= wordI (instL ..)`, `tailBoundJ = writerI (instL ..)`,
  `clearBoundJ = clearI (instL ..)`, the cell-55 copy `= ((2 |rowMajor Mx.entry| + 2) + 0) + 1`;
* `boundV_j ≤ bvG ⟨V, E, G, sv_j ..⟩` (the level-0 proof of `boundV_le`, cell by cell, at `sv_j`);
* `writerBound_j_split`: `writerBound_j .. T = cell55 + restI (instL ..) + boundV_j .. + T + 7`;
* `writerBound_j_le`: ONE absolute `C` with
  `writerBound_j G c b yb lv Mx T ≤ (|enc G| + 1)^C + 2^(C p) + T` under the level naming premise
  `oneLevelBound (stepParameters G c b yb lv Mx) ≤ p` (admitted `levelj_shape_le`);
* `writerBound_j_poly`: the same with the family clock `T` under a stated polynomial premise.
-/

namespace EthInapproximability.CurrentPaper.EntryClockPoly3

open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EthInapproximability.ParameterizedNP.GuardedSourceSlab
open EntryClockPoly

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem boundA_j_eq (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix) :
    EntryPrepCopyJ.boundA_j G c b yb lv Mx = boundAI (instL G c b yb lv Mx) := by
  unfold EntryPrepCopyJ.boundA_j EntryPrepCopyJ.copyCost_j boundAI copyCostI
  dsimp only [instL, EntryLevelJBank.wJ, EntryLevelWords.levelWords, TemplateEntry.actualWords,
    EntryTailJ.d0J, ProtectedFullBankBridgeScratch.actualD,
    MatrixWeightedEntrySemantic.actualInput, EntryTailJ.c0J]

theorem labBound_j_eq (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix) (T : ℕ) :
    EntryPrepVecJ.labBound_j G c b yb lv Mx T = labI (instL G c b yb lv Mx) + T + 1 := by
  unfold EntryPrepVecJ.labBound_j labI
  dsimp only [instL, EntryLevelJBank.wJ, EntryLevelWords.levelWords, TemplateEntry.actualWords]

theorem wordB_j_eq (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix) :
    ((2 * (EntryLevelJBank.wJ G c b yb lv Mx).wordB + 2) + 0) + 1 = wordI (instL G c b yb lv Mx) := by
  unfold wordI
  dsimp only [instL, EntryLevelJBank.wJ, EntryLevelWords.levelWords, TemplateEntry.actualWords]

theorem tailBoundJ_eq (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix) :
    EntryTailJ.tailBoundJ G c b yb lv Mx = writerI (instL G c b yb lv Mx) := by
  unfold EntryTailJ.tailBoundJ writerI
  dsimp only [instL]

theorem clearBoundJ_eq (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix) :
    EntryTailJ.clearBoundJ G c b yb lv Mx = clearI (instL G c b yb lv Mx) := by
  unfold EntryTailJ.clearBoundJ clearI
  dsimp only [instL, EntryTailJ.bnkJ, EntryTailJ.r0J, EntryTailJ.c0J, wI,
    EntryLevelWords.levelWords, EntryLevelJBank.word22J, ProtectedFullBankBridgeScratch.actualD,
    MatrixWeightedEntrySemantic.actualInput]

theorem cell55_eq (Mx : Iteration.Matrix) :
    ((2 * (EntryLevelJBank.matWord Mx).length + 2) + 0) + 1 =
      ((2 * (rowMajor Mx.entry).length + 2) + 0) + 1 := rfl

theorem lenB_j_le (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix)
    (z : VectorsFromGraphQ.Z2) :
    EntryPrepVecJ.lenB_j G c b yb lv Mx z ≤
      BzG G (EntryPrepVecJ.sv_j G c b yb lv Mx) + BQG G (EntryPrepVecJ.sv_j G c b yb lv Mx) := by
  rcases z with z | j
  · have := exitZ_len G (EntryPrepVecJ.sv_j G c b yb lv Mx) z
    show (VectorsProducer.exitBank G (EntryPrepVecJ.sv_j G c b yb lv Mx) [] z).length ≤ _
    omega
  · have := qa_len G (EntryPrepVecJ.sv_j G c b yb lv Mx) j
    show (VectorsFromGraphQ.Qa G (EntryPrepVecJ.sv_j G c b yb lv Mx) j).length +
      EntryPrepVec.growQ (EntryPrepVecJ.sv_j G c b yb lv Mx) (Fintype.card E) ≤ _
    unfold BQG
    omega

theorem boundV_j_le (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix) :
    EntryPrepVecJ.boundV_j G c b yb lv Mx ≤ bvG ⟨V, E, G, EntryPrepVecJ.sv_j G c b yb lv Mx⟩ := by
  have hsum := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin EntryPrepVec.nZ))
    (fun i => EntryPrepVecJ.lenB_j G c b yb lv Mx ((Fintype.equivFin EntryPrepVec.Z2).symm i))
    (BzG G (EntryPrepVecJ.sv_j G c b yb lv Mx) + BQG G (EntryPrepVecJ.sv_j G c b yb lv Mx))
    (fun i _ => lenB_j_le G c b yb lv Mx _)
  simp only [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  unfold EntryPrepVecJ.boundV_j bvG
  simp only [MatrixMaterialization.rowMajor_length, rowsNG]
  dsimp only [ellG]
  omega

/-- The literal level-j writer clock splits into the admitted instance pieces. -/
theorem writerBound_j_split (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix) (T : ℕ) :
    EntryWriter22J.writerBound_j G c b yb lv Mx T =
      (((2 * (rowMajor Mx.entry).length + 2) + 0) + 1) + restI (instL G c b yb lv Mx) +
        EntryPrepVecJ.boundV_j G c b yb lv Mx + T + 7 := by
  have h1 := boundA_j_eq G c b yb lv Mx
  have h2 := labBound_j_eq G c b yb lv Mx T
  have h3 := wordB_j_eq G c b yb lv Mx
  have h4 := clearBoundJ_eq G c b yb lv Mx
  have h5 := tailBoundJ_eq G c b yb lv Mx
  have h6 := cell55_eq Mx
  unfold EntryWriter22J.writerBound_j EntryPrepVecJ.prepBound_j restI
  omega

/-- **Segment 2.** ONE absolute `C`: the level-j writer clock is `(|enc G|+1)^C + 2^(C p) + T`. -/
theorem writerBound_j_le : ∃ C : ℕ, ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix) (p T : ℕ),
    EffectiveIteration.oneLevelBound (Iteration.stepParameters G c b yb lv Mx) ≤ p →
    EntryWriter22J.writerBound_j G c b yb lv Mx T ≤ (ellG G + 1) ^ C + 2 ^ (C * p) + T := by
  obtain ⟨C, hC⟩ := levelj_shape_le
  refine ⟨C, fun {V E} _ _ _ _ G c b yb lv Mx p T hname => ?_⟩
  have hs := hC G c b yb lv Mx p T hname
  have hv := boundV_j_le G c b yb lv Mx
  have e : (instL G c b yb lv Mx).s = EntryPrepVecJ.sv_j G c b yb lv Mx := rfl
  rw [e] at hs
  rw [writerBound_j_split]
  omega

/-- The same with the level-j family clock under a stated polynomial premise. -/
theorem writerBound_j_poly (C0 : ℕ) : ∃ C : ℕ, ∀ {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix)
    (p T : ℕ),
    EffectiveIteration.oneLevelBound (Iteration.stepParameters G c b yb lv Mx) ≤ p →
    T ≤ (ellG G + 1) ^ C0 + 2 ^ (C0 * p) →
    EntryWriter22J.writerBound_j G c b yb lv Mx T ≤ (ellG G + 1) ^ C + 2 ^ (C * p) := by
  obtain ⟨C, hC⟩ := writerBound_j_le
  refine ⟨max C C0 + 1, fun {V E} _ _ _ _ G c b yb lv Mx p T hname hT => ?_⟩
  have h := hC G c b yb lv Mx p T hname
  have hp : 1 ≤ p := by
    have h128 := (EffectiveIteration.parameter_size_bounds (Iteration.stepParameters G c b yb lv Mx)).1
    rw [EffectiveIteration.oneLevelBound, ← EffectiveIteration.nextScale_identity] at hname
    have : 1 ≤ Parameters.balanceOrder (Iteration.stepParameters G c b yb lv Mx) ^ 4 :=
      Nat.one_le_pow _ _ (by omega)
    omega
  have hX : 2 ≤ ellG G + 1 := by have := ell_two G; omega
  have hm := merge2' (ellG G + 1) p C C0 hX hp
  omega
where
  merge2' (X p A B : ℕ) (hX : 2 ≤ X) (hp : 1 ≤ p) :
      X ^ A + 2 ^ (A * p) + (X ^ B + 2 ^ (B * p)) ≤
        X ^ (max A B + 1) + 2 ^ ((max A B + 1) * p) := by
    have hX1 : 1 ≤ X := by omega
    have a1 : X ^ A ≤ X ^ max A B := Nat.pow_le_pow_right hX1 (le_max_left _ _)
    have a2 : X ^ B ≤ X ^ max A B := Nat.pow_le_pow_right hX1 (le_max_right _ _)
    have b1 : 2 ^ (A * p) ≤ 2 ^ (max A B * p) :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (le_max_left _ _))
    have b2 : 2 ^ (B * p) ≤ 2 ^ (max A B * p) :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (le_max_right _ _))
    have eX : X ^ (max A B + 1) = X ^ max A B * X := pow_succ _ _
    have e2 : 2 ^ ((max A B + 1) * p) = 2 ^ (max A B * p) * 2 ^ p := by
      rw [show (max A B + 1) * p = max A B * p + p by ring, pow_add]
    have h2p : 2 ≤ 2 ^ p := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) hp
    have c1 : 2 * X ^ max A B ≤ X ^ max A B * X := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hX
    have c2 : 2 * 2 ^ (max A B * p) ≤ 2 ^ (max A B * p) * 2 ^ p := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ h2p
    rw [eX, e2]
    omega

#print axioms boundA_j_eq
#print axioms labBound_j_eq
#print axioms wordB_j_eq
#print axioms tailBoundJ_eq
#print axioms clearBoundJ_eq
#print axioms boundV_j_le
#print axioms writerBound_j_split
#print axioms writerBound_j_le
#print axioms writerBound_j_poly

end EthInapproximability.CurrentPaper.EntryClockPoly3
