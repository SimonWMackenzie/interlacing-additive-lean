import CurrentAdditive.V38IndexedTwoTag
import CurrentAdditive.V38Fin2Exact
import CurrentAdditive.GeneratedCollisionExact

/-! v39/v38 selected indexed collision bound. The older selected-gamma
eight-wise theorem is reused only for its unchanged law/decoder statement;
the cost proof here uses exactly the current two-threshold profile. -/

namespace CurrentAdditive.V38IndexedTwoTag

open Paper2 Paper2.SourceMatrix Paper2.SourceProjection
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open CurrentAdditive.ArbitraryPrefix
open Workspace.Types.Protocol

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

theorem marked_protocol_cost
    (hD : 8 ≤ D) (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (d a : ℕ) (ρ : ℝ) (hd : 2 ≤ d) (hρ : 0 < ρ)
    (hs : s = 2 ^ a) (hq : q₁ + 3 = s + 1)
    (hscale : 2 * (s : ℝ) * ρ ≤ 1)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile R
      μX.toFiniteLaw μY.toFiniteLaw ρ (d : ℤ))
    (bin : Fin s) (α : Fin q₂) (K : Set src.inner.Label)
    (Base : Fin 3 → Set X) (S : Finset src.gamma.Label)
    (i₁ i₂ i₀ : I) (p p' : Fin s) (hpp : p ≠ p')
    (h₁ : activity i₁ α = some p) (h₂ : activity i₂ α = some p')
    (h₀ : activity i₀ α = none)
    (U : Set (Column src)) (V : Set (Row (I := I) src))
    (hK : ∀ z ∈ K, Sum.inl (bin, z) ∈ V)
    (hBase : ∀ t u, u ∈ Base t → Sum.inr (SourceProjectionDiagonal.collisionItem i₁ i₂ i₀ t, u) ∈ V)
    (hS : ∀ γ ∈ S, Sum.inr (α, γ) ∈ U)
    (hhead : ∀ r : Fin q₁, 2 * (s : ℝ) * ρ ≤ μX.toFiniteLaw.prob
      (fun u => (r, u) ∈ (fun z => src.inner.decode z α) '' K))
    (hrow : ∀ t : Fin 3, 2 * (s : ℝ) * ρ ≤ μX.toFiniteLaw.prob (· ∈ Base t))
    (hSmass : (1/2 : ℝ) < SourceSupportStep.mass src.gamma.law.toFiniteLaw S)
    (P : Protocol V U Bool)
    (hP : P.Computes (fun v u => matrix src R activity ξ₀ u.val v.val)) :
    d + a + 1 ≤ P.cost := by
  classical
  let Rows : Fin (q₁+3) → Set X := fun i u =>
    match finSumFinEquiv.symm i with
    | .inl r => (r,u) ∈ (fun z => src.inner.decode z α) '' K
    | .inr t => u ∈ Base t
  have hp : (2 : ℝ) ^ (a+1) = 2 * (s : ℝ) := by
    rw [hs, pow_succ]
    push_cast
    ring
  have hrow' : ∀ i ∈ (Finset.univ : Finset (Fin (q₁+3))),
      (2 : ℝ) ^ (a+1) * ρ ≤ μX.toFiniteLaw.prob (· ∈ Rows i) := by
    intro i _
    rw [hp]
    change 2 * (s : ℝ) * ρ ≤ μX.toFiniteLaw.prob
      (fun u => match finSumFinEquiv.symm i with
      | .inl r => (r,u) ∈ (fun z => src.inner.decode z α) '' K
      | .inr t => u ∈ Base t)
    cases he : finSumFinEquiv.symm i with
    | inl r => simpa only [he] using hhead r
    | inr t => simpa only [he] using hrow t
  have hc : 2 ^ ((a+1)-1) + 1 ≤
      (Finset.univ : Finset (Fin (q₁+3))).card := by
    simp only [Nat.add_sub_cancel_right, Finset.card_univ, Fintype.card_fin]
    omega
  have hmass : (9/25 : ℝ) ≤ src.gamma.law.toFiniteLaw.prob (· ∈ (S : Set _)) := by
    change (1/2 : ℝ) < src.gamma.law.toFiniteLaw.prob (· ∈ (S : Set _)) at hSmass
    linarith
  have hscale' : (2 : ℝ) ^ (a+1) * ρ ≤ 1 := by rw [hp]; exact hscale
  have hl := V38Fin2Exact.exactboost μX μY R src.gamma.law.toFiniteLaw
    (selectedGamma src p p') (selected_gamma_dwise src hD p p' hpp)
    Finset.univ Rows (S : Set _) d (a+1) ρ (by omega) hd hρ hscale'
    hprofile hc hrow' hmass
  have heq : rowRectangle (Finset.univ : Finset (Fin (q₁+3))) Rows =
      indexedWitnessRows src α K Base := by
    ext z
    simp only [rowRectangle, Set.mem_setOf_eq, Finset.mem_univ, true_and]
    rfl
  rw [heq] at hl
  have hm := witness_source_cost_le src R activity ξ₀ bin α K Base i₁ i₂ i₀
    p p' h₁ h₂ h₀ (S : Set _) U V hK hBase hS
  have hu : Workspace.Types.CommComplexity.D
      (fun (v : V) (u : U) => matrix src R activity ξ₀ u.val v.val) ≤ P.cost :=
    Nat.sInf_le ⟨P, rfl, hP⟩
  have he := restrictionD_transpose (matrix src R activity ξ₀) U V
  have hu' : Compression.restrictionD (fun v c => matrix src R activity ξ₀ c v)
      V U ≤ P.cost := hu
  have hfinal := hl.trans (hm.trans (he ▸ hu'))
  omega

end CurrentAdditive.V38IndexedTwoTag

#print axioms CurrentAdditive.V38IndexedTwoTag.marked_protocol_cost
