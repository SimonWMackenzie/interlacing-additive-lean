import CurrentAdditive.GeneratedWAlignmentFullV1
import CurrentAdditive.IndexedSemanticIteration
import CurrentAdditive.GeneratedNExactNearFull

/-! Bind full indexed-W alignment to one literal stage, source triple,
item law, graph activity, and public schedule. -/

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

/-- The full cost and all original-law near-full restrictions for the
actual internal W of one indexed source call. -/
theorem actual_stage_W_full
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
    D (Sources.W i.src i.streams R.matrix activity i.tail) =
        d+2*((L+3)/4)+6*L+1 ∧
    ∀ (B : Set (Fin (w L) × Sources.Column i.src))
      (A : Set (i.streams.metadataStream.Label ×
        (i.streams.baseStream.Label × i.streams.selectorStream.Label))),
      1 - (δU L Δ γ : ℝ) ≤
        (indexedFirstRowLaw i.src (w_pos L)).prob (· ∈ B) →
      (θ L : ℝ) ≤ i.streams.law.toFiniteLaw.prob (· ∈ A) →
      d+2*((L+3)/4)+6*L+1 ≤
        Paper2.Compression.restrictionD
          (Sources.W i.src i.streams R.matrix activity i.tail) A B := by
  classical
  have hN := generated_N_exact_near_full L Δ sourceC128Ceil γ
    T.large hΔ hγ i.src R.matrix T.order G hloopless hincident
    T.rep T.repetition hdegree hgap i.tail d hd hD hp hadm
  have hN' :
      let activity := Paper2.SourceConstruction.activity T.order G
        (by have hs := s_ge_64 L (by have := T.large; omega : 24 ≤ L); omega)
        T.rep T.repetition
      D (Sources.N i.src R.matrix activity i.tail) =
        d+(L+3)/4+4*L+(L+3)/4+1 ∧
      ∀ (U : Set (Sources.Column i.src))
        (Vrows : Set (Sources.Row (I :=
          Paper2.SourceConstruction.Items (s L) V) i.src)),
        1 - (η L Δ γ : ℝ) ≤
          (Sources.columnLaw i.src).toFiniteLaw.prob (· ∈ U) →
        1 - (η L Δ γ : ℝ) ≤
          (Sources.rowLaw i.src (actualItemLaw (V := V) L)).toFiniteLaw.prob
            (· ∈ Vrows) →
        d+(L+3)/4+4*L+(L+3)/4+1 ≤
          Paper2.Compression.restrictionD
            (Sources.N i.src R.matrix activity i.tail) U Vrows := by
    simpa only [actualItemLaw] using hN
  have hW := indexed_W_full_from_N L Δ (Fintype.card V)
    (Fintype.card E) d γ T.large hΔ hγ hd i.src
    (actualItemLaw (V := V) L) i.streams R.matrix
    (Paper2.SourceConstruction.activity T.order G
      (by have hs := s_ge_64 L (by have := T.large; omega : 24 ≤ L); omega)
      T.rep T.repetition) i.tail hD hp hadm hN'
  simpa only using hW

#print axioms actual_stage_W_full

end CurrentAdditive.IndexedSemanticIteration
