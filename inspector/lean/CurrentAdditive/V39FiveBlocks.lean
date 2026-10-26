import CurrentAdditive.V38ThreeMiddle

/-!
# Five-block base with exactly the current two restriction thresholds

Selected source v39 (mathematics identical to v38):
* `sections/amplifier.tex`, `def:profile`, lines 16--28;
* `appendices/interlacing.tex`, `lem:small-blocks`, lines 88--131;
* `appendices/moments.tex`, proof of `det:exact`, lines 152--190;
* `appendices/interlacing.tex`, five-block induction base, lines 254--256.

The intermediate bound at column mass 9/50 charges one actual first message.
The final bound at 9/25 charges another. Projection masses always use the
original product law, and cost transfer uses actual surviving representatives.
-/

namespace Paper2.V38SmallBlocks

open Workspace.Types.CommComplexity

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem five_bool_triple (f : Fin 5 → Bool) :
    ∃ (t : Bool) (e : Fin 3 → Fin 5),
      Function.Injective e ∧ ∀ k, f (e k) = t := by
  classical
  let S : Bool → Finset (Fin 5) := fun t => Finset.univ.filter (fun i => f i = t)
  have hsplit : (S false).card + (S true).card = 5 := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin 5))) (p := fun i => f i = false)
    have hnot : (fun i : Fin 5 => ¬ f i = false) = (fun i => f i = true) := by
      funext i
      apply propext
      cases f i <;> simp
    simpa [S, hnot] using h
  have hheavy : ∃ t, 3 ≤ (S t).card := by
    by_cases h : 3 ≤ (S false).card
    · exact ⟨false, h⟩
    · exact ⟨true, by omega⟩
  obtain ⟨t, ht⟩ := hheavy
  obtain ⟨J, hJS, hJ⟩ := Finset.exists_subset_card_eq ht
  refine ⟨t, J.orderEmbOfFin hJ, (J.orderEmbOfFin hJ).injective, ?_⟩
  intro k
  exact (Finset.mem_filter.mp (hJS (J.orderEmbOfFin_mem hJ k))).2

theorem three_middle_selected (F : X → Y → Bool)
    (μ : FiniteLaw X) (ν : PositiveRationalLaw Y) (θ : ℝ) (H : ℕ)
    (hH : 2 ≤ H) (hθ : 0 < θ)
    (hp : V38RestrictionProfiles.TwoThresholdProfile F μ ν.toFiniteLaw θ (H : ℤ))
    (p : ℕ) (U : Set (Fin p × X)) (V : Set (Fin p → Y))
    (e : Fin 3 → Fin p)
    (hrow : ∀ i : Fin 3, 4 * θ ≤ μ.prob (fun x => (e i, x) ∈ U))
    (hcol : (9 / 50 : ℝ) ≤ (ν.toFiniteLaw.iid 3).prob
      (· ∈ (fun z : Fin p → Y => fun i : Fin 3 => z (e i)) '' V)) :
    H + 1 ≤ Compression.restrictionD (fullInterlace F p) U V := by
  have hthree := three_block_middle F μ ν θ H hH hθ hp
    {s : Fin 3 × X | (e s.1, s.2) ∈ U}
    ((fun z : Fin p → Y => fun i : Fin 3 => z (e i)) '' V) hrow hcol
  exact hthree.trans (projected_blocks_cost_le F p 3 U V e)

theorem three_high_selected (F : X → Y → Bool)
    (μ : FiniteLaw X) (ν : PositiveRationalLaw Y) (θ : ℝ) (H : ℕ)
    (hH : 2 ≤ H) (hθ : 0 < θ)
    (hp : V38RestrictionProfiles.TwoThresholdProfile F μ ν.toFiniteLaw θ (H : ℤ))
    (p : ℕ) (U : Set (Fin p × X)) (V : Set (Fin p → Y))
    (e : Fin 3 → Fin p)
    (hrow : ∀ i : Fin 3, 4 * θ ≤ μ.prob (fun x => (e i, x) ∈ U))
    (hcol : (9 / 25 : ℝ) ≤ (ν.toFiniteLaw.iid 3).prob
      (· ∈ (fun z : Fin p → Y => fun i : Fin 3 => z (e i)) '' V)) :
    H + 2 ≤ Compression.restrictionD (fullInterlace F p) U V := by
  have hthree := three_block_high F μ ν θ H hH hθ hp
    {s : Fin 3 × X | (e s.1, s.2) ∈ U}
    ((fun z : Fin p → Y => fun i : Fin 3 => z (e i)) '' V) hrow hcol
  exact hthree.trans (projected_blocks_cost_le F p 3 U V e)

theorem five_to_two_high (F : X → Y → Bool)
    (μ : FiniteLaw X) (ν : PositiveRationalLaw Y) (θ : ℝ) (H : ℕ)
    (hH : 2 ≤ H) (hθ : 0 < θ)
    (hp : V38RestrictionProfiles.TwoThresholdProfile F μ ν.toFiniteLaw θ (H : ℤ))
    (U : Set (Fin 5 × X)) (V : Set (Fin 5 → Y))
    (hrow : ∀ i : Fin 5, 2 * θ ≤ μ.prob (fun x => (i, x) ∈ U))
    (hcol : (9 / 100 : ℝ) ≤ (ν.toFiniteLaw.iid 5).prob (· ∈ V)) :
    H + 1 ≤ Compression.restrictionD (fullInterlace F 5) U V := by
  obtain ⟨J, hJ, hm⟩ := rational_projected_mass ν 5 2 (by omega) (by omega) V
  let e : Fin 2 → Fin 5 := J.orderEmbOfFin hJ
  have hpow : (9 / 100 : ℝ) ^ ((2 : ℝ) / 5) ≤
      ((ν.toFiniteLaw.iid 5).prob (· ∈ V)) ^ ((2 : ℝ) / 5) :=
    Real.rpow_le_rpow (by norm_num) hcol (by norm_num)
  have hproj : (9 / 25 : ℝ) ≤ (ν.toFiniteLaw.iid 2).prob
      (· ∈ (fun z : Fin 5 → Y => fun i : Fin 2 => z (e i)) '' V) :=
    (five_pair_numeric.trans hpow).trans hm
  exact two_high_selected F μ ν.toFiniteLaw θ H hH hθ hp 5 U V e
    (fun i => hrow (e i)) hproj

theorem five_block_middle (F : X → Y → Bool)
    (μ : FiniteLaw X) (ν : PositiveRationalLaw Y) (θ : ℝ) (H : ℕ)
    (hH : 2 ≤ H) (hθ : 0 < θ)
    (hp : V38RestrictionProfiles.TwoThresholdProfile F μ ν.toFiniteLaw θ (H : ℤ))
    (U : Set (Fin 5 × X)) (V : Set (Fin 5 → Y))
    (hrow : ∀ i : Fin 5, 8 * θ ≤ μ.prob (fun x => (i, x) ∈ U))
    (hcol : (9 / 50 : ℝ) ≤ (ν.toFiniteLaw.iid 5).prob (· ∈ V)) :
    H + 2 ≤ Compression.restrictionD (fullInterlace F 5) U V := by
  have hlow := five_to_two_high F μ ν θ H hH hθ hp U V
    (by intro i; have h := hrow i; linarith) (by linarith)
  have hpos : 1 ≤ Compression.restrictionD (fullInterlace F 5) U V := by omega
  rcases firstMessage_rectangle (fullInterlace F 5) U V hpos with
    ⟨a, ha⟩ | ⟨b, hb⟩
  · have hchoice : ∀ i : Fin 5, ∃ t : Bool,
        4 * θ ≤ μ.prob (fun x => (i, x) ∈ childSet U a t) := by
      intro i
      exact row_child_mass_general μ 5 U a (4 * θ) i (by have h := hrow i; linarith)
    let t : Fin 5 → Bool := fun i => Classical.choose (hchoice i)
    have ht : ∀ i : Fin 5,
        4 * θ ≤ μ.prob (fun x => (i, x) ∈ childSet U a (t i)) := by
      intro i
      exact Classical.choose_spec (hchoice i)
    obtain ⟨s, e, he, hs⟩ := five_bool_triple t
    have hrows : ∀ k : Fin 3,
        4 * θ ≤ μ.prob (fun x => (e k, x) ∈ childSet U a s) := by
      intro k
      simpa only [hs k] using ht (e k)
    have hproj : (9 / 50 : ℝ) ≤ (ν.toFiniteLaw.iid 3).prob
        (· ∈ (fun z : Fin 5 → Y => fun k : Fin 3 => z (e k)) '' V) :=
      hcol.trans (SourceProjection.iid_projection_mass ν.toFiniteLaw e he V)
    have hsuffix := three_middle_selected F μ ν θ H hH hθ hp
      5 (childSet U a s) V e hrows hproj
    have hcost := ha s
    omega
  · obtain ⟨t, ht⟩ := exists_heavy_child (ν.toFiniteLaw.iid 5) V b
    have hchildcol : (9 / 100 : ℝ) ≤
        (ν.toFiniteLaw.iid 5).prob (· ∈ childSet V b t) := by linarith
    have hsuffix := five_to_two_high F μ ν θ H hH hθ hp
      U (childSet V b t) (by intro i; have h := hrow i; linarith) hchildcol
    have hcost := hb t
    omega

theorem five_block_high (F : X → Y → Bool)
    (μ : FiniteLaw X) (ν : PositiveRationalLaw Y) (θ : ℝ) (H : ℕ)
    (hH : 2 ≤ H) (hθ : 0 < θ)
    (hp : V38RestrictionProfiles.TwoThresholdProfile F μ ν.toFiniteLaw θ (H : ℤ))
    (U : Set (Fin 5 × X)) (V : Set (Fin 5 → Y))
    (hrow : ∀ i : Fin 5, 8 * θ ≤ μ.prob (fun x => (i, x) ∈ U))
    (hcol : (9 / 25 : ℝ) ≤ (ν.toFiniteLaw.iid 5).prob (· ∈ V)) :
    H + 3 ≤ Compression.restrictionD (fullInterlace F 5) U V := by
  have hmid := five_block_middle F μ ν θ H hH hθ hp U V hrow (by linarith)
  have hpos : 1 ≤ Compression.restrictionD (fullInterlace F 5) U V := by omega
  rcases firstMessage_rectangle (fullInterlace F 5) U V hpos with
    ⟨a, ha⟩ | ⟨b, hb⟩
  · have hchoice : ∀ i : Fin 5, ∃ t : Bool,
        4 * θ ≤ μ.prob (fun x => (i, x) ∈ childSet U a t) := by
      intro i
      exact row_child_mass_general μ 5 U a (4 * θ) i (by have h := hrow i; linarith)
    let t : Fin 5 → Bool := fun i => Classical.choose (hchoice i)
    have ht : ∀ i : Fin 5,
        4 * θ ≤ μ.prob (fun x => (i, x) ∈ childSet U a (t i)) := by
      intro i
      exact Classical.choose_spec (hchoice i)
    obtain ⟨s, e, he, hs⟩ := five_bool_triple t
    have hrows : ∀ k : Fin 3,
        4 * θ ≤ μ.prob (fun x => (e k, x) ∈ childSet U a s) := by
      intro k
      simpa only [hs k] using ht (e k)
    have hproj : (9 / 25 : ℝ) ≤ (ν.toFiniteLaw.iid 3).prob
        (· ∈ (fun z : Fin 5 → Y => fun k : Fin 3 => z (e k)) '' V) :=
      hcol.trans (SourceProjection.iid_projection_mass ν.toFiniteLaw e he V)
    have hsuffix := three_high_selected F μ ν θ H hH hθ hp
      5 (childSet U a s) V e hrows hproj
    have hcost := ha s
    omega
  · obtain ⟨t, ht⟩ := exists_heavy_child (ν.toFiniteLaw.iid 5) V b
    have hchildcol : (9 / 50 : ℝ) ≤
        (ν.toFiniteLaw.iid 5).prob (· ∈ childSet V b t) := by linarith
    have hsuffix := five_block_middle F μ ν θ H hH hθ hp
      U (childSet V b t) hrow hchildcol
    have hcost := hb t
    omega

theorem five_block_C_of_profile (F : X → Y → Bool)
    (μ : FiniteLaw X) (ν : PositiveRationalLaw Y) (θ : ℝ) (C : ℕ)
    (hC : 3 ≤ C) (hθ : 0 < θ)
    (hp : V38RestrictionProfiles.TwoThresholdProfile F μ ν.toFiniteLaw θ ((C : ℤ) - 1))
    (U : Set (Fin 5 × X)) (V : Set (Fin 5 → Y))
    (hrow : ∀ i : Fin 5, 8 * θ ≤ μ.prob (fun x => (i, x) ∈ U))
    (hcol : (9 / 25 : ℝ) ≤ (ν.toFiniteLaw.iid 5).prob (· ∈ V)) :
    C + 2 ≤ Compression.restrictionD (fullInterlace F 5) U V := by
  have hp' : V38RestrictionProfiles.TwoThresholdProfile F μ ν.toFiniteLaw θ
      ((C - 1 : ℕ) : ℤ) := by
    simpa only [Nat.cast_sub (by omega : 1 ≤ C), Nat.cast_one] using hp
  have h := five_block_high F μ ν θ (C - 1) (by omega) hθ hp' U V hrow hcol
  omega

#print axioms five_bool_triple
#print axioms three_middle_selected
#print axioms three_high_selected
#print axioms five_to_two_high
#print axioms five_block_middle
#print axioms five_block_high
#print axioms five_block_C_of_profile
#print five_block_high
#print five_block_C_of_profile

end Paper2.V38SmallBlocks
