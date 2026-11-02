import CurrentAdditive.V39FullIidRestoration

namespace CurrentAdditive.V42FullIidRestoration

/-- A finite family admits a strictly smaller positive threshold with
exactly the same qualifying indices. -/
theorem finite_threshold_lowering {I : Type*} [Fintype I]
    (f : I → ℝ) (θ : ℝ) (hθ : 0 < θ) :
    ∃ θ' : ℝ, 0 < θ' ∧ θ' < θ ∧ ∀ i, (θ' ≤ f i ↔ θ ≤ f i) := by
  classical
  have aux : ∀ s : Finset I, ∃ θ' : ℝ, 0 < θ' ∧ θ' < θ ∧
      ∀ i ∈ s, θ' ≤ f i → θ ≤ f i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        refine ⟨θ / 2, by linarith, by linarith, ?_⟩
        simp
    | @insert i s hi ih =>
        obtain ⟨t, ht0, htθ, ht⟩ := ih
        by_cases hfi : θ ≤ f i
        · refine ⟨t, ht0, htθ, ?_⟩
          intro k hk hkf
          rcases Finset.mem_insert.mp hk with rfl | hks
          · exact hfi
          · exact ht k hks hkf
        · have hfiθ : f i < θ := lt_of_not_ge hfi
          have hmax : max (f i) t < θ := max_lt hfiθ htθ
          refine ⟨(max (f i) t + θ) / 2, ?_, by linarith, ?_⟩
          · have := le_max_right (f i) t
            linarith
          · intro k hk hkf
            rcases Finset.mem_insert.mp hk with rfl | hks
            · have := le_max_left (f k) t
              linarith
            · apply ht k hks
              have := le_max_right (f i) t
              linarith
  obtain ⟨t, ht0, htθ, ht⟩ := aux Finset.univ
  refine ⟨t, ht0, htθ, ?_⟩
  intro i
  exact ⟨ht i (Finset.mem_univ i), fun hi => htθ.le.trans hi⟩

open Paper2

/-- A finite input carrier has only finitely many possible retained row
weights. Lowering a positive threshold slightly preserves all eligible
sets, without any restriction on the real-valued finite law. -/
theorem finiteLaw_threshold_lowering {X : Type*} [Fintype X]
    (μ : FiniteLaw X) (θ : ℝ) (hθ : 0 < θ) :
    ∃ θ' : ℝ, 0 < θ' ∧ θ' < θ ∧
      ∀ U : Set X, (θ' ≤ μ.prob (· ∈ U) ↔ θ ≤ μ.prob (· ∈ U)) := by
  classical
  exact finite_threshold_lowering (fun U : Set X => μ.prob (· ∈ U)) θ hθ

#print axioms finite_threshold_lowering
#print axioms finiteLaw_threshold_lowering




open Workspace.Types.CommComplexity
open CurrentAdditive.V39FullIidRestoration

variable {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

/-- Source v42 `cl:bridge`, including its non-strict scale boundary.
The only changed input is an analysis threshold with the same eligible
row sets; the restored Boolean matrix and both output laws are unchanged. -/
theorem rational_profile (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (C r b : ℕ) (θ δ : ℝ)
    (hC : 3 ≤ C) (hb : 1 ≤ b)
    (hθ : 0 < θ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 64)
    (hQ : 80 * (b : ℝ) ≤ (2 : ℝ) ^ r * δ)
    (hscale : (2 : ℝ) ^ r * θ ≤ 1 / 20)
    (hnear : RestrictionLowerBound F μ.toFiniteLaw ν.toFiniteLaw θ (1 - δ) (C : ℤ))
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile F μ.toFiniteLaw ν.toFiniteLaw θ ((C : ℤ) - 1)) :
    V38RestrictionProfiles.TwoThresholdProfile (restored F r) (ν.toFiniteLaw.iid (2 ^ r))
      ((FiniteLaw.uniformFin (2 ^ r) (Nat.two_pow_pos r)).prod μ.toFiniteLaw)
      ((2 : ℝ) ^ (-(b : ℝ))) ((C + r : ℕ) : ℤ) := by
  obtain ⟨t, ht0, htθ, hevents⟩ := finiteLaw_threshold_lowering μ.toFiniteLaw θ hθ
  have hstrict : (2 : ℝ) ^ r * t < 1 / 20 :=
    (mul_lt_mul_of_pos_left htθ (pow_pos (by norm_num : (0 : ℝ) < 2) r)).trans_le hscale
  apply CurrentAdditive.V39FullIidRestoration.rational_profile μ ν F C r b t δ
    hC hb ht0 hδ hδ1 hQ hstrict
  · intro U V hU hV
    exact hnear U V ((hevents U).mp hU) hV
  · intro j U V hU hV
    exact hprofile j U V ((hevents U).mp hU) hV

/-- The exact-cost and regenerated two-threshold conclusions of v42
`cl:bridge` for the original positive rational weights, at `Qθ ≤ 1/20`.
No third-threshold profile or altered restored matrix is used. -/
theorem rational_restoration (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (r b : ℕ) (θ δ : ℝ)
    (hC : 3 ≤ D F) (hb : 1 ≤ b)
    (hθ : 0 < θ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 64)
    (hQ : 80 * (b : ℝ) ≤ (2 : ℝ) ^ r * δ)
    (hscale : (2 : ℝ) ^ r * θ ≤ 1 / 20)
    (hnear : RestrictionLowerBound F μ.toFiniteLaw ν.toFiniteLaw
      θ (1 - δ) (D F : ℤ))
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile F μ.toFiniteLaw ν.toFiniteLaw θ ((D F : ℤ) - 1)) :
    D (restored F r) = D F + r ∧
      V38RestrictionProfiles.TwoThresholdProfile (restored F r) (ν.toFiniteLaw.iid (2 ^ r))
        ((FiniteLaw.uniformFin (2 ^ r) (Nat.two_pow_pos r)).prod μ.toFiniteLaw)
        ((2 : ℝ) ^ (-(b : ℝ))) ((D F + r : ℕ) : ℤ) := by
  have hp := rational_profile μ ν F (D F) r b θ δ hC hb hθ hδ hδ1 hQ hscale
    hnear hprofile
  refine ⟨le_antisymm (CurrentAdditive.V39FullIidRestoration.upper F r (D F) le_rfl) ?_, hp⟩
  exact CurrentAdditive.V39FullIidRestoration.profile_full_lower (restored F r) _ _ _ _
    (Paper2.RestorationBridge.dyadic_threshold_lt_one b hb).le hp

/-- The upper bound is independent of both profile assumptions. -/
theorem upper (F : X → Y → Bool) (r U : ℕ) (hU : D F ≤ U) :
    D (restored F r) ≤ U + r :=
  CurrentAdditive.V39FullIidRestoration.upper F r U hU

/-- These are the full original tuple carrier and block carrier. -/
theorem restored_cardinalities (F : X → Y → Bool) (r : ℕ) :
    Fintype.card (Fin (2 ^ r) → Y) = (Fintype.card Y) ^ (2 ^ r) ∧
      Fintype.card (Fin (2 ^ r) × X) = 2 ^ r * Fintype.card X :=
  CurrentAdditive.V39FullIidRestoration.restored_cardinalities F r

#print axioms rational_profile
#print axioms rational_restoration
#print axioms upper
#print axioms restored_cardinalities

end CurrentAdditive.V42FullIidRestoration
