import CurrentAdditive.RestoreSelection
import CurrentAdditive.DeterministicFullBoostTV
import Paper2.SourceProjection

/-! v27 Appendix H `det:restore`, for the actual indexed restricted
interlace and its transpose. The only source is the generated `CodeSource`
with 8192-wise exact marginals; retained seed events stay on its original
labels throughout conditioning. -/

namespace CurrentAdditive.DeterministicRestoration

open Paper2 Paper2.SourceProjection
open Workspace.Types.CommComplexity
open CurrentAdditive.ArbitraryPrefix
open CurrentAdditive.DeterministicIndexedMatrix

theorem generated_restore_profile
    {X Z : Type*} [Fintype X] [Fintype Z]
    [DecidableEq X] [DecidableEq Z]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (r C : ℕ) (θ φ δ : ℝ)
    (src : CodeSource 8192 (2 ^ r) Z ν)
    (hC : 3 ≤ C) (hθpos : 0 < θ)
    (hφpos : 0 < φ) (hφ1 : φ ≤ 1)
    (hδpos : 0 < δ) (hδ1 : δ ≤ 1 / 64)
    (hQ : (128 : ℝ) *
      ((CurrentAdditive.conditioningExceptionCountR 1024 φ (δ / 2) : ℝ) + 1) ≤
        ((2 ^ r : ℕ) : ℝ))
    (hθ : ((2 ^ r : ℕ) : ℝ) * θ ≤ 1 / 20)
    (hnear : ∀ A : Set X, ∀ B : Set Z,
      θ ≤ μ.toFiniteLaw.prob (· ∈ A) →
      1 - δ ≤ ν.toFiniteLaw.prob (· ∈ B) →
      C ≤ Paper2.Compression.restrictionD F A B)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw θ
      (((C - 1 : ℕ) : ℤ))) :
    RestrictionProfile
      (fun (seed : src.Label) (a : Fin (2 ^ r) × X) =>
        F a.2 (src.decode seed a.1))
      src.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin (2 ^ r))).prod μ).toFiniteLaw
      φ ((C + r : ℕ) : ℤ) := by
  classical
  intro j W U hW hU
  have hr : 7 ≤ r := width_exponent_seven r
    (CurrentAdditive.conditioningExceptionCountR 1024 φ (δ / 2)) hQ
  have hj : j.val + 1 ≤ r := by have := j.isLt; omega
  obtain ⟨E, pick, hE, hOut, hRows, hTV⟩ :=
    restore_selected_blocks μ ν r src U W j θ φ δ
      hθpos hφpos hδpos hQ hθ hU hW
  let Good : Finset (Fin (2 ^ r)) := Finset.univ.image pick
  let Rows : Fin (2 ^ r) → Set X := fun i => {x | (i,x) ∈ U}
  let a : ℕ := r - j.val
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hcount : 2 ^ (a - 1) + 1 ≤ Good.card := by
    have hcard : Good.card = 2 ^ (r - j.val - 1) + 1 := by
      simp [Good, Finset.card_image_of_injective _ pick.injective]
    have hexp : a - 1 = r - j.val - 1 := rfl
    rw [hexp, hcard]
  have hOutside : ∀ i ∈ Good, i ∉ E := by
    intro i hi
    obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hi
    exact hOut h
  have hrow : ∀ i ∈ Good,
      (2 : ℝ)^a * θ ≤ μ.toFiniteLaw.prob (· ∈ Rows i) := by
    intro i hi
    obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hi
    simpa only [a, Nat.cast_pow, Nat.cast_ofNat, Rows] using hRows h
  have hscale : (2 : ℝ)^a * θ ≤ 1 := by
    have hpow : 2 ^ a ≤ 2 ^ r :=
      Nat.pow_le_pow_right (by norm_num) (by dsimp [a]; omega)
    have hpowR : (((2 ^ a : ℕ) : ℝ)) ≤ ((2 ^ r : ℕ) : ℝ) := by
      exact_mod_cast hpow
    have hmul := mul_le_mul_of_nonneg_right hpowR hθpos.le
    have hmul' : (2 : ℝ)^a * θ ≤ (2 : ℝ)^r * θ := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using hmul
    have hθ' : (2 : ℝ)^r * θ ≤ 1 / 20 := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using hθ
    linarith
  let ε := CurrentAdditive.conditioningEpsilonR 1024 φ (δ / 2)
  have hεpos : 0 < ε :=
    CurrentAdditive.conditioningEpsilonR_pos (by omega) hφpos (by linarith)
  have hεδ : ε ≤ δ := by
    have hmin : ε ≤ δ / 2 := min_le_left _ _
    linarith
  have hεcap : ε ≤ (2 : ℝ)^(-20 : ℤ) / 1024 *
      φ^((1 : ℝ)/256) :=
    codeSource_epsilon_cap φ (δ / 2)
  have hεshort : ε ≤ 1/1000 := by
    have hp : φ^((1 : ℝ)/256) ≤ 1 :=
      Real.rpow_le_one hφpos.le hφ1 (by norm_num)
    have hc : (0 : ℝ) ≤ (2 : ℝ)^(-20 : ℤ) / 1024 := by positivity
    have hh := mul_le_mul_of_nonneg_left hp hc
    have hn : (2 : ℝ)^(-20 : ℤ) / 1024 ≤ 1/1000 := by norm_num
    linarith
  have hfull := CurrentAdditive.FullBoost.fullboost_of_tv
    μ ν F src.law.toFiniteLaw src.decode src.exactLaw
    Good E Rows W C a θ φ δ ε hC hθpos hscale
    (by simpa only [if_neg (by omega : a ≠ 0)] using hcount)
    hOutside hrow hφpos hφ1 hW hnear hprofile
    hεδ hεpos hεshort hεcap hTV
  have hsub : Set.MapsTo id (rowRectangle Good Rows) U := by
    intro ix hix
    change ix.1 ∈ Good ∧ ix.2 ∈ Rows ix.1 at hix
    exact hix.2
  have hlarge : C + a ≤ Paper2.Compression.restrictionD
      (fun ix seed => F ix.2 (src.decode seed ix.1)) U W :=
    hfull.trans (Paper2.SourceProjection.restrictionD_map_le
      (fun ix seed => F ix.2 (src.decode seed ix.1)) id id
      U W (rowRectangle Good Rows) W hsub (fun _ h => h))
  have htrans := Paper2.SourceProjection.restrictionD_transpose
    (fun ix seed => F ix.2 (src.decode seed ix.1)) U W
  rw [htrans]
  have haEq : a = r - j.val := rfl
  omega

/-- The exact Appendix H restored cost and three-level restriction profile
on the generated indexed source.  `r` is the public number of selector bits,
so its width is the power of two `Q = 2^r`. -/
theorem generated_restore
    {X Z : Type*} [Fintype X] [Fintype Z]
    [DecidableEq X] [DecidableEq Z]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (r C : ℕ) (θ φ δ : ℝ)
    (src : CodeSource 8192 (2 ^ r) Z ν)
    (hC : 3 ≤ C) (hD : D F = C)
    (hθpos : 0 < θ) (hφpos : 0 < φ) (hφ1 : φ ≤ 1)
    (hδpos : 0 < δ) (hδ1 : δ ≤ 1 / 64)
    (hQ : (128 : ℝ) *
      ((CurrentAdditive.conditioningExceptionCountR 1024 φ (δ / 2) : ℝ) + 1) ≤
        ((2 ^ r : ℕ) : ℝ))
    (hθ : ((2 ^ r : ℕ) : ℝ) * θ ≤ 1 / 20)
    (hnear : ∀ A : Set X, ∀ B : Set Z,
      θ ≤ μ.toFiniteLaw.prob (· ∈ A) →
      1 - δ ≤ ν.toFiniteLaw.prob (· ∈ B) →
      C ≤ Paper2.Compression.restrictionD F A B)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw θ
      (((C - 1 : ℕ) : ℤ))) :
    D (fun (seed : src.Label) (a : Fin (2 ^ r) × X) =>
        F a.2 (src.decode seed a.1)) = C + r ∧
      RestrictionProfile
        (fun (seed : src.Label) (a : Fin (2 ^ r) × X) =>
          F a.2 (src.decode seed a.1))
        src.law.toFiniteLaw
        ((PositiveRationalLaw.uniform (Fin (2 ^ r))).prod μ).toFiniteLaw
        φ ((C + r : ℕ) : ℤ) := by
  have hp := generated_restore_profile μ ν F r C θ φ δ src hC
    hθpos hφpos hφ1 hδpos hδ1 hQ hθ hnear hprofile
  exact ⟨generated_restore_cost_of_profile μ ν F r C φ src hD hφ1 hp,
    hp⟩

#print axioms generated_restore_profile
#print axioms generated_restore

end CurrentAdditive.DeterministicRestoration
