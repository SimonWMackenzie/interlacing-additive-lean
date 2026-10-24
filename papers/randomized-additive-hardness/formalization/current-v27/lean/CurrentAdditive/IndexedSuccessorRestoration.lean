import CurrentAdditive.IndexedSemanticIteration
import CurrentAdditive.RestoreSuccessor

/-!
Restore the actual final indexed successor from the exact/full near-full
alignment of its own internal matrix W.  The full-W cost and near-full
restriction theorem are explicit pending inputs; the weak W profile, all
scalar guards, and the output-law transport are proved here.
-/

namespace CurrentAdditive.IndexedSemanticIteration

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity
open CurrentAdditive.DeterministicParameters
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.IndexedStagePresentation

universe u

variable {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V]
  (L : ℕ) [Nonempty V] [Nonempty (Fin (4*s L))]
  [Nonempty (Fin (s L-3))]
  [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (s L)]
  [NeZero (w L)] [NeZero (Q L)]

theorem next_restored_from_full_W
    (T : Schedule V E L)
    (inputs : ∀ R : Stage.{u} (N L), StepInputs L R T)
    (G : Graph V E) (R : Stage.{u} (N L))
    (Δ Caux : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ)
    (hadm : Admissible L Δ (Fintype.card V) (Fintype.card E) Caux γ)
    (d : ℕ) (hd : 3 ≤ d) (hD : D R.matrix = d)
    (hp : RestrictionProfile R.matrix R.rowLaw.toFiniteLaw
      R.colLaw.toFiniteLaw (ρ L : ℝ) (d : ℤ))
    (hWcost : let i := inputs R
      D (Sources.W i.src i.streams R.matrix
        (Paper2.SourceConstruction.activity T.order G
          (by have hh := s_ge_64 L (by have := T.large; omega : 24 ≤ L); omega)
          T.rep T.repetition) i.tail) =
        d + 2*((L+3)/4) + 6*L + 1)
    (hWnear : let i := inputs R
      ∀ A : Set (i.streams.metadataStream.Label ×
          (i.streams.baseStream.Label × i.streams.selectorStream.Label)),
      ∀ B : Set (Fin (w L) × Sources.Column i.src),
      (θ L : ℝ) ≤ i.streams.law.toFiniteLaw.prob (· ∈ A) →
      1 - (δU L Δ γ : ℝ) ≤
        (((PositiveRationalLaw.uniform (Fin (w L))).prod
          (Sources.columnLaw i.src)).toFiniteLaw).prob (· ∈ B) →
      d + 2*((L+3)/4) + 6*L + 1 ≤
        Paper2.Compression.restrictionD
          (Sources.W i.src i.streams R.matrix
            (Paper2.SourceConstruction.activity T.order G
              (by have hh := s_ge_64 L (by have := T.large; omega : 24 ≤ L); omega)
              T.rep T.repetition) i.tail) A B) :
    D (next L T inputs G R).matrix = d + h L + 1 ∧
    RestrictionProfile (next L T inputs G R).matrix
      (next L T inputs G R).rowLaw.toFiniteLaw
      (next L T inputs G R).colLaw.toFiniteLaw
      (ρ L : ℝ) ((d + h L + 1 : ℕ) : ℤ) := by
  let i := inputs R
  let activity := Paper2.SourceConstruction.activity T.order G
    (by have hh := s_ge_64 L (by have := T.large; omega : 24 ≤ L); omega)
    T.rep T.repetition
  let C := d + 2*((L+3)/4) + 6*L + 1
  have hC : 3 ≤ C := by dsimp [C]; omega
  have hθpos : (0 : ℝ) < (θ L : ℝ) := by
    exact_mod_cast theta_pos L
  have hφpos : (0 : ℝ) < (ρ L : ℝ) := by
    have hn : (0 : ℚ) < (N L : ℚ) := by exact_mod_cast N_pos L
    unfold ρ
    exact_mod_cast (one_div_pos.mpr hn)
  have hφ1 : (ρ L : ℝ) ≤ 1 := by
    have hn : (1 : ℚ) ≤ (N L : ℚ) := by exact_mod_cast N_pos L
    have hq : ρ L ≤ 1 := by
      unfold ρ
      exact (div_le_iff₀ (by positivity : (0 : ℚ) < (N L : ℚ))).2
        (by simpa using hn)
    exact_mod_cast hq
  have hδpos : (0 : ℝ) < (δU L Δ γ : ℝ) := by
    exact_mod_cast deltaU_pos L Δ γ hΔ hγ
  have hδ1 : (δU L Δ γ : ℝ) ≤ 1 / 64 := by
    have hh : δU L Δ γ ≤ (1 / 64 : ℚ) :=
      (fixed_eta_guards L Δ γ hΔ hγ).2.2
    have hr : ((δU L Δ γ : ℚ) : ℝ) ≤ ((1 / 64 : ℚ) : ℝ) :=
      Rat.cast_le.mpr hh
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hr
  have hQnat : 128 *
      (CurrentAdditive.conditioningExceptionCountR 1024
        (ρ L : ℝ) ((δU L Δ γ : ℝ) / 2) + 1) ≤ Q L := by
    simpa only [CurrentAdditive.conditioningExceptionCountR,
      CurrentAdditive.conditioningExceptionCount,
      CurrentAdditive.conditioningEpsilonR,
      CurrentAdditive.conditioningEpsilon,
      Rat.cast_div, Rat.cast_ofNat] using hadm.exception_rho
  have hQ : (128 : ℝ) *
      ((CurrentAdditive.conditioningExceptionCountR 1024
        (ρ L : ℝ) ((δU L Δ γ : ℝ) / 2) : ℝ) + 1) ≤
        (Q L : ℝ) := by exact_mod_cast hQnat
  have hθ : (Q L : ℝ) * (θ L : ℝ) ≤ 1 / 20 := by
    have hqr := congrArg (fun q : ℚ => (q : ℝ)) (Q_theta L)
    push_cast at hqr
    rw [hqr]
    norm_num
  have hxR : (w L : ℝ) * (x L : ℝ) ≤ 1/10000 := by
    have hr : (((w L : ℚ) * x L : ℚ) : ℝ) ≤
        ((1/10000 : ℚ) : ℝ) := Rat.cast_le.mpr hadm.w_x
    simpa [Rat.cast_mul, Rat.cast_div] using hr
  have hWprofile := next_W_weak_profile L T inputs G R d hd hD hp
    hadm.exception_theta hxR
  have restore_for_width :
      ∀ (q : ℕ) [NeZero q]
        (finalQ : CodeSource 8192 q (Fin (w L) × Sources.Column i.src)
          ((PositiveRationalLaw.uniform (Fin (w L))).prod
            (Sources.columnLaw i.src))),
        q = 2^(6*L) →
        (128 : ℝ) * ((CurrentAdditive.conditioningExceptionCountR 1024
          (ρ L : ℝ) ((δU L Δ γ : ℝ)/2) : ℝ) + 1) ≤ (q : ℝ) →
        (q : ℝ) * (θ L : ℝ) ≤ 1/20 →
        D (Sources.successor i.src i.streams finalQ R.matrix activity i.tail) =
          C + 6*L ∧
        RestrictionProfile
          (Sources.successor i.src i.streams finalQ R.matrix activity i.tail)
          finalQ.law.toFiniteLaw
          (((PositiveRationalLaw.uniform (Fin q)).prod
            i.streams.law).toFiniteLaw)
          (ρ L : ℝ) ((C+6*L : ℕ) : ℤ) := by
    intro q instQ finalQ hpow hQq hθq
    subst q
    exact Sources.final_restored_profile i.src i.streams finalQ
      R.matrix activity i.tail (θ L : ℝ) (ρ L : ℝ) (δU L Δ γ : ℝ)
      hC (by simpa only [C, i, activity] using hWcost)
      hθpos hφpos hφ1 hδpos hδ1 hQq hθq
      (by simpa only [C, i, activity] using hWnear)
      (by simpa only [C, i, activity] using hWprofile)
  have hrest := restore_for_width (Q L) i.final (Q_eq_pow L) hQ hθ
  have hsum : C + 6*L = d + h L + 1 := by
    dsimp [C, h]
    omega
  simpa only [next, successorStage_matrix, C, i, activity,
    hsum] using hrest

#print axioms next_restored_from_full_W

end CurrentAdditive.IndexedSemanticIteration
