import Paper2.SourceProjection
import Paper2.StrongSeed
import Paper2.InterlaceProtocol
import Paper2.SourcePopulation

/-!
# The restriction profile of the first source interlace

Frozen v12 Section 4, `src:profiles`, first paragraph.  The numerical
conditions are displayed separately from the matrix argument: they concern
only public parameters and are discharged by the public schedule.  In
particular, none of them assumes a communication lower bound.
-/

namespace Paper2.SourceProfilesInner

open scoped BigOperators
open Workspace.Types.CommComplexity
open SourceMatrix SourceProjection

/-- Numerical conditions for one application of the strong interlacing
bound, including the number of qualifying selector positions. -/
structure RungGuards (q a : ℕ) (θ x β : ℝ) : Prop where
  exponent : 4 ≤ a
  threshold_pos : 0 < θ
  scale_lt : (2 : ℝ) ^ a * θ < 1
  word_floor : (2 : ℝ) ^ (-((2 : ℝ) ^ a / 1024)) ≤ x
  population : (q : ℝ) * (β - (2 : ℝ) ^ a * θ) ≥
    (StrongSeed.copies a : ℝ) * (1 - (2 : ℝ) ^ a * θ)

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The finite-set strong bound expressed on the actual retained subtypes. -/
theorem strong_member_sets
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (H a : ℕ) (hH : 3 ≤ H) (ha : 4 ≤ a)
    (θ : ℝ) (hθ : 0 < θ) (hscale : (2 : ℝ) ^ a * θ ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw θ (H : ℤ))
    (U : Set (Fin (StrongSeed.copies a) × X))
    (W : Set (Fin (StrongSeed.copies a) → Y))
    (hU : ∀ i, (2 : ℝ) ^ a * θ ≤ μ.toFiniteLaw.prob (fun z => (i, z) ∈ U))
    (hW : (2 : ℝ) ^ (-((2 : ℝ) ^ a / 1024)) ≤
      (ν.toFiniteLaw.iid (StrongSeed.copies a)).prob (· ∈ W)) :
    H + a ≤ Compression.restrictionD (fullInterlace F (StrongSeed.copies a)) U W := by
  classical
  have h := StrongSeed.rational_member μ ν F H a hH ha θ hθ hscale hprofile
    U.toFinset W.toFinset (by simpa using hU) (by simpa using hW)
  apply h.trans
  let rows : U.toFinset → U := fun z => ⟨z.val, Set.mem_toFinset.mp z.property⟩
  let cols : W.toFinset → W := fun z => ⟨z.val, Set.mem_toFinset.mp z.property⟩
  exact Workspace.ProofLemmas.SublemmaPrecompNoIncrease
    (fun (r : U) (z : W) => fullInterlace F (StrongSeed.copies a) r.val z.val)
    rows cols

/-- Announcing the selected head coordinate gives the matching upper bound;
the unused tail coordinates require no communication. -/
theorem inner_upper (R : X → Y → Bool) (q₁ s a : ℕ)
    (hq : 0 < q₁) (hwidth : q₁ ≤ 2 ^ a) :
    D (M₁ (q₁ := q₁) (s := s) R) ≤ D R + a := by
  have h := indexedInterlace_D_le R hq (head (q₁ := q₁) (s := s))
  have hlog : Nat.clog 2 q₁ ≤ a := (Nat.clog_le_iff_le_pow (by decide)).2 hwidth
  exact h.trans (by omega)

/-- The restricted protocol is obtained by local inclusion of each input. -/
theorem restrictionD_le (F : X → Y → Bool) (U : Set X) (V : Set Y) :
    Compression.restrictionD F U V ≤ D F := by
  classical
  exact Workspace.ProofLemmas.SublemmaPrecompNoIncrease F
    (fun x : U => x.val) (fun y : V => y.val)

/-- Uniform block mass supplies the exact number of distinct original
positions required by the strong bound. -/
theorem select_blocks (μ : PositiveRationalLaw X) (q a : ℕ) [NeZero q]
    (θ x β : ℝ) (hg : RungGuards q a θ x β)
    (U : Set (Fin q × X))
    (hU : β ≤ ((PositiveRationalLaw.uniform (Fin q)).prod μ).toFiniteLaw.prob (· ∈ U)) :
    ∃ e : Fin (StrongSeed.copies a) ↪ Fin q,
      ∀ i, (2 : ℝ) ^ a * θ ≤ μ.toFiniteLaw.prob (fun z => (e i, z) ∈ U) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have htotal : (q : ℝ) * β ≤ ∑ i : Fin q,
      μ.toFiniteLaw.prob (fun z => (i, z) ∈ U) := by
    rw [inner_block_average μ U] at hU
    have h := mul_le_mul_of_nonneg_left hU hq.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul] using h
  exact SourcePopulation.exists_selection_of_budget
    (fun i : Fin q => μ.toFiniteLaw.prob (fun z => (i, z) ∈ U)) β
    ((2 : ℝ) ^ a * θ) (fun _ => μ.toFiniteLaw.prob_le_one _) hg.scale_lt
    (by simpa only [Fintype.card_fin] using htotal) (StrongSeed.copies a)
    (by simpa only [Fintype.card_fin] using hg.population)

/-- One rung of the first source profile. Selection uses genuine retained
row blocks; every projected word has an original surviving representative. -/
theorem inner_rung (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (q₁ s d a : ℕ) [NeZero q₁]
    (hd : 3 ≤ d) (ρ x β : ℝ) (hg : RungGuards q₁ a ρ x β)
    (hp : RestrictionProfile R μ.toFiniteLaw ν.toFiniteLaw ρ (d : ℤ)) :
    RestrictionLowerBound (fun γ r => M₁ (q₁ := q₁) (s := s) R r γ)
      (ν.iid (q₁ + s + 1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw x β (d + a) := by
  intro W U hW hU
  obtain ⟨e, he⟩ := select_blocks μ q₁ a ρ x β hg U hU
  let A : Set (Fin (StrongSeed.copies a) × X) := {r | (e r.1, r.2) ∈ U}
  have hwords := hg.word_floor.trans (hW.trans (head_projection_mass ν e e.injective W))
  rw [PositiveRationalLaw.toFiniteLaw_iid] at hwords
  have hlower := strong_member_sets μ ν R d a hd hg.exponent ρ hg.threshold_pos
    hg.scale_lt.le hp A (headProjection e '' W) he hwords
  have hmap := M₁_projection_D_le R e U W A (fun _ h => h)
  have hnat := hlower.trans hmap
  rw [restrictionD_transpose (M₁ R)]
  exact_mod_cast hnat

/-- The three source rungs assembled into the precise integer-valued
restriction profile of the transpose of M₁. -/
theorem inner_profile (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (q₁ s d a : ℕ) [NeZero q₁]
    (hd : 3 ≤ d) (ha : 2 ≤ a) (ρ x : ℝ)
    (hg : ∀ j : Fin 3, RungGuards q₁ (a - j.val) ρ x
      ((3 / 5 : ℝ) * (1 / 2 : ℝ) ^ j.val))
    (hp : RestrictionProfile R μ.toFiniteLaw ν.toFiniteLaw ρ (d : ℤ)) :
    RestrictionProfile (fun γ r => M₁ (q₁ := q₁) (s := s) R r γ)
      (ν.iid (q₁ + s + 1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw x ((d + a : ℕ) : ℤ) := by
  intro j
  have hj : j.val ≤ a := by omega
  have heq : (d : ℤ) + (a - j.val : ℕ) = ((d + a : ℕ) : ℤ) - j.val := by omega
  rw [← heq]
  exact inner_rung μ ν R q₁ s d (a - j.val) hd ρ x _ (hg j) hp

/-- The first source matrix has the exact claimed cost once the public
width and the three numerical rungs are instantiated. -/
theorem inner_exact (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (q₁ s d a : ℕ) [NeZero q₁]
    (hd : 3 ≤ d) (ha : 2 ≤ a) (ρ x : ℝ) (hx : x ≤ 1)
    (hg : ∀ j : Fin 3, RungGuards q₁ (a - j.val) ρ x
      ((3 / 5 : ℝ) * (1 / 2 : ℝ) ^ j.val))
    (hp : RestrictionProfile R μ.toFiniteLaw ν.toFiniteLaw ρ (d : ℤ))
    (hD : D R = d) (hwidth : q₁ ≤ 2 ^ a) :
    D (M₁ (q₁ := q₁) (s := s) R) = d + a := by
  apply Nat.le_antisymm
  · simpa only [hD] using inner_upper R q₁ s a (NeZero.pos q₁) hwidth
  · have hp' := inner_profile μ ν R q₁ s d a hd ha ρ x hg hp
    have hl := hp' ⟨0, by decide⟩ Set.univ Set.univ
      (by simpa using hx) (by norm_num)
    have hm := restrictionD_le
      (fun γ r => M₁ (q₁ := q₁) (s := s) R r γ) Set.univ Set.univ
    rw [transpose_D] at hm
    have hl' : ((d + a : ℕ) : ℤ) ≤
        (Compression.restrictionD
          (fun γ r => M₁ (q₁ := q₁) (s := s) R r γ) Set.univ Set.univ : ℤ) := by
      simpa using hl
    exact_mod_cast hl'.trans (Int.ofNat_le.mpr hm)

end Paper2.SourceProfilesInner

#print axioms Paper2.SourceProfilesInner.strong_member_sets
#print axioms Paper2.SourceProfilesInner.inner_upper
#print axioms Paper2.SourceProfilesInner.inner_profile
#print axioms Paper2.SourceProfilesInner.inner_exact
