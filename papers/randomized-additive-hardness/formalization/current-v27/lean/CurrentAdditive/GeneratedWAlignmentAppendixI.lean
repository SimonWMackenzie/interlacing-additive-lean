import CurrentAdditive.GeneratedWAlignmentActualStage
import CurrentAdditive.GeneratedWProfileAtSchedule

/-! All clauses of Appendix I's internal-interlace theorem on one literal
stage: exact cost, the three-rung weak profile, and full near-full strength. -/

namespace CurrentAdditive.IndexedSemanticIteration

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity
open CurrentAdditive.DeterministicParameters
open CurrentAdditive.DeterministicAdmissibility
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open CurrentAdditive.IndexedStagePresentation

universe u

variable {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V]
  [Nonempty V]
  (L : ℕ) [Nonempty (Fin (4*s L))] [Nonempty (Fin (s L-3))]
  [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (s L)] [NeZero (w L)]

/-- The complete internal-interlace conclusion at the one actual generated
source call, with the graph's genuine NO gap as hypothesis. -/
theorem actual_stage_W_alignment
    (T : Schedule V E L)
    (R : Stage.{u} (N L)) (i : StepInputs L R T)
    (G : Graph V E)
    (Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ)
    (hloopless : ∀ e, G e false ≠ G e true)
    (hincident : ∀ v, ∃ e b, G e b = v)
    (hdegree : ∀ v, Paper2.SourceItems.degree G v ≤ Δ)
    (hgap : ∀ colour : V → Fin 3,
      (γ : ℝ) * Fintype.card E ≤
      ((Finset.univ.filter (fun e =>
        colour (G e false) = colour (G e true))).card : ℝ))
    (d : ℕ) (hd : 3 ≤ d) (hD : D R.matrix = d)
    (hp : RestrictionProfile R.matrix R.rowLaw.toFiniteLaw
      R.colLaw.toFiniteLaw (ρ L : ℝ) (d : ℤ))
    (hadm : Admissible L Δ (Fintype.card V) (Fintype.card E)
      sourceC128Ceil γ) :
    let activity := Paper2.SourceConstruction.activity T.order G
      (by have hs := s_ge_64 L (by have := T.large; omega : 24 ≤ L); omega)
      T.rep T.repetition
    let Wactual := Sources.W i.src i.streams R.matrix activity i.tail
    D Wactual = d+2*((L+3)/4)+6*L+1 ∧
    RestrictionProfile Wactual i.streams.law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin (w L))).prod
        (Sources.columnLaw i.src)).toFiniteLaw)
      (θ L : ℝ) ((d+2*((L+3)/4)+6*L : ℕ) : ℤ) ∧
    ∀ (B : Set (Fin (w L) × Sources.Column i.src))
      (A : Set (i.streams.metadataStream.Label ×
        (i.streams.baseStream.Label × i.streams.selectorStream.Label))),
      1 - (δU L Δ γ : ℝ) ≤
        (indexedFirstRowLaw i.src (w_pos L)).prob (· ∈ B) →
      (θ L : ℝ) ≤ i.streams.law.toFiniteLaw.prob (· ∈ A) →
      d+2*((L+3)/4)+6*L+1 ≤
        Paper2.Compression.restrictionD Wactual A B := by
  classical
  have hfull := actual_stage_W_full L T R i G Δ γ hΔ hγ
    hloopless hincident hdegree hgap d hd hD hp hadm
  have hxR : (w L : ℝ) * (x L : ℝ) ≤ 1/10000 := by
    have hr : (((w L : ℚ) * x L : ℚ) : ℝ) ≤
        ((1/10000 : ℚ) : ℝ) := Rat.cast_le.mpr hadm.w_x
    simpa [Rat.cast_mul, Rat.cast_div] using hr
  have hprofile := generated_W_profile_at_schedule
    (G := Fin (4*s L)) (V := V) (Aux := Fin (s L-3))
    L T.large i.src (actualItemLaw (V := V) L) i.streams
    R.matrix
    (Paper2.SourceConstruction.activity T.order G
      (by have hs := s_ge_64 L (by have := T.large; omega : 24 ≤ L); omega)
      T.rep T.repetition)
    i.tail d hd hD hp hadm.exception_theta hxR
  dsimp only at hfull ⊢
  refine ⟨hfull.1, ?_, hfull.2⟩
  convert hprofile using 1
  congr 1
  omega

#print axioms actual_stage_W_alignment

end CurrentAdditive.IndexedSemanticIteration
