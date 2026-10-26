import CurrentAdditive.V38ThreeBlocks

namespace Paper2.V38SmallBlocks

open Workspace.Types.CommComplexity

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem row_child_mass_general (μ : FiniteLaw X) (p : ℕ)
    (U : Set (Fin p × X)) (a : U → Bool) (θ : ℝ) (i : Fin p)
    (hrow : 2 * θ ≤ μ.prob (fun x => (i, x) ∈ U)) :
    ∃ t : Bool, θ ≤ μ.prob (fun x => (i, x) ∈ childSet U a t) := by
  let U₀ : Set X := {x | (i, x) ∈ U}
  let a₀ : U₀ → Bool := fun x => a ⟨(i, x.1), x.2⟩
  obtain ⟨t, ht⟩ := exists_heavy_child μ U₀ a₀
  refine ⟨t, ?_⟩
  have heq : childSet U₀ a₀ t = {x : X | (i, x) ∈ childSet U a t} := by
    ext x
    constructor
    · rintro ⟨hx, ha⟩
      exact ⟨hx, ha⟩
    · rintro ⟨hx, ha⟩
      exact ⟨hx, ha⟩
  rw [heq] at ht
  dsimp [U₀] at ht
  linarith

private theorem three_bool_pair (f : Fin 3 → Bool) :
    ∃ (i j : Fin 3), i ≠ j ∧ f i = f j := by
  by_cases h01 : f 0 = f 1
  · exact ⟨0, 1, by decide, h01⟩
  · by_cases h02 : f 0 = f 2
    · exact ⟨0, 2, by decide, h02⟩
    · have h12 : f 1 = f 2 := by
        cases h0 : f 0 <;> cases h1 : f 1 <;> cases h2 : f 2 <;>
          simp_all
      exact ⟨1, 2, by decide, h12⟩

theorem three_block_middle (F : X → Y → Bool)
    (μ : FiniteLaw X) (ν : PositiveRationalLaw Y) (θ : ℝ) (H : ℕ)
    (hH : 2 ≤ H) (hθ : 0 < θ)
    (hp : V38RestrictionProfiles.TwoThresholdProfile F μ ν.toFiniteLaw θ (H : ℤ))
    (U : Set (Fin 3 × X)) (V : Set (Fin 3 → Y))
    (hrow : ∀ i : Fin 3, 4 * θ ≤ μ.prob (fun x => (i, x) ∈ U))
    (hcol : (9 / 50 : ℝ) ≤ (ν.toFiniteLaw.iid 3).prob (· ∈ V)) :
    H + 1 ≤ Compression.restrictionD (fullInterlace F 3) U V := by
  have hlow := three_to_two_low F μ ν θ H hH hθ hp U V
    (by intro i; have h := hrow i; linarith) (by linarith)
  have hpos : 1 ≤ Compression.restrictionD (fullInterlace F 3) U V := by omega
  rcases firstMessage_rectangle (fullInterlace F 3) U V hpos with
    ⟨a, ha⟩ | ⟨b, hb⟩
  · have hchoice : ∀ i : Fin 3, ∃ t : Bool,
        2 * θ ≤ μ.prob (fun x => (i, x) ∈ childSet U a t) := by
      intro i
      exact row_child_mass_general μ 3 U a (2 * θ) i (by have h := hrow i; linarith)
    let t : Fin 3 → Bool := fun i => Classical.choose (hchoice i)
    have ht : ∀ i : Fin 3,
        2 * θ ≤ μ.prob (fun x => (i, x) ∈ childSet U a (t i)) := by
      intro i
      exact Classical.choose_spec (hchoice i)
    obtain ⟨i, j, hij, heq⟩ := three_bool_pair t
    let e : Fin 2 → Fin 3 := fun k => if k = 0 then i else j
    have he : Function.Injective e := by
      intro k l hkl
      fin_cases k <;> fin_cases l <;> simp_all [e]
    have hrows : ∀ k : Fin 2,
        2 * θ ≤ μ.prob (fun x => (e k, x) ∈ childSet U a (t i)) := by
      intro k
      fin_cases k
      · simpa [e] using ht i
      · simpa [e, heq] using ht j
    have hproj : (9 / 50 : ℝ) ≤ (ν.toFiniteLaw.iid 2).prob
        (· ∈ (fun z : Fin 3 → Y => fun k : Fin 2 => z (e k)) '' V) :=
      hcol.trans (SourceProjection.iid_projection_mass ν.toFiniteLaw e he V)
    have hsuffix := two_low_selected F μ ν.toFiniteLaw θ H hH hθ hp
      3 (childSet U a (t i)) V e hrows hproj
    have hcost := ha (t i)
    omega
  · obtain ⟨t, ht⟩ := exists_heavy_child (ν.toFiniteLaw.iid 3) V b
    have hchildcol : (9 / 100 : ℝ) ≤
        (ν.toFiniteLaw.iid 3).prob (· ∈ childSet V b t) := by linarith
    have hsuffix := three_to_two_low F μ ν θ H hH hθ hp
      U (childSet V b t) (by intro i; have h := hrow i; linarith) hchildcol
    have hcost := hb t
    omega

#print axioms three_block_middle

theorem two_high_selected (F : X → Y → Bool)
    (μ : FiniteLaw X) (ν : FiniteLaw Y) (θ : ℝ) (H : ℕ)
    (hH : 2 ≤ H) (hθ : 0 < θ)
    (hp : V38RestrictionProfiles.TwoThresholdProfile F μ ν θ (H : ℤ))
    (p : ℕ) (U : Set (Fin p × X)) (V : Set (Fin p → Y))
    (e : Fin 2 → Fin p)
    (hrow : ∀ i : Fin 2, 2 * θ ≤ μ.prob (fun x => (e i, x) ∈ U))
    (hcol : (9 / 25 : ℝ) ≤ (ν.iid 2).prob
      (· ∈ (fun z : Fin p → Y => fun i : Fin 2 => z (e i)) '' V)) :
    H + 1 ≤ Compression.restrictionD (fullInterlace F p) U V := by
  have htwo := two_block_high F μ ν θ H hH hθ hp
    {s : Fin 2 × X | (e s.1, s.2) ∈ U}
    ((fun z : Fin p → Y => fun i : Fin 2 => z (e i)) '' V)
    hrow hcol
  exact htwo.trans (projected_blocks_cost_le F p 2 U V e)

theorem three_block_high (F : X → Y → Bool)
    (μ : FiniteLaw X) (ν : PositiveRationalLaw Y) (θ : ℝ) (H : ℕ)
    (hH : 2 ≤ H) (hθ : 0 < θ)
    (hp : V38RestrictionProfiles.TwoThresholdProfile F μ ν.toFiniteLaw θ (H : ℤ))
    (U : Set (Fin 3 × X)) (V : Set (Fin 3 → Y))
    (hrow : ∀ i : Fin 3, 4 * θ ≤ μ.prob (fun x => (i, x) ∈ U))
    (hcol : (9 / 25 : ℝ) ≤ (ν.toFiniteLaw.iid 3).prob (· ∈ V)) :
    H + 2 ≤ Compression.restrictionD (fullInterlace F 3) U V := by
  have hmid := three_block_middle F μ ν θ H hH hθ hp U V hrow (by linarith)
  have hpos : 1 ≤ Compression.restrictionD (fullInterlace F 3) U V := by omega
  rcases firstMessage_rectangle (fullInterlace F 3) U V hpos with
    ⟨a, ha⟩ | ⟨b, hb⟩
  · have hchoice : ∀ i : Fin 3, ∃ t : Bool,
        2 * θ ≤ μ.prob (fun x => (i, x) ∈ childSet U a t) := by
      intro i
      exact row_child_mass_general μ 3 U a (2 * θ) i (by have h := hrow i; linarith)
    let t : Fin 3 → Bool := fun i => Classical.choose (hchoice i)
    have ht : ∀ i : Fin 3,
        2 * θ ≤ μ.prob (fun x => (i, x) ∈ childSet U a (t i)) := by
      intro i
      exact Classical.choose_spec (hchoice i)
    obtain ⟨i, j, hij, heq⟩ := three_bool_pair t
    let e : Fin 2 → Fin 3 := fun k => if k = 0 then i else j
    have he : Function.Injective e := by
      intro k l hkl
      fin_cases k <;> fin_cases l <;> simp_all [e]
    have hrows : ∀ k : Fin 2,
        2 * θ ≤ μ.prob (fun x => (e k, x) ∈ childSet U a (t i)) := by
      intro k
      fin_cases k
      · simpa [e] using ht i
      · simpa [e, heq] using ht j
    have hproj : (9 / 25 : ℝ) ≤ (ν.toFiniteLaw.iid 2).prob
        (· ∈ (fun z : Fin 3 → Y => fun k : Fin 2 => z (e k)) '' V) :=
      hcol.trans (SourceProjection.iid_projection_mass ν.toFiniteLaw e he V)
    have hsuffix := two_high_selected F μ ν.toFiniteLaw θ H hH hθ hp
      3 (childSet U a (t i)) V e hrows hproj
    have hcost := ha (t i)
    omega
  · obtain ⟨t, ht⟩ := exists_heavy_child (ν.toFiniteLaw.iid 3) V b
    have hchildcol : (9 / 50 : ℝ) ≤
        (ν.toFiniteLaw.iid 3).prob (· ∈ childSet V b t) := by linarith
    have hsuffix := three_block_middle F μ ν θ H hH hθ hp
      U (childSet V b t) hrow hchildcol
    have hcost := hb t
    omega

#print axioms three_block_high

end Paper2.V38SmallBlocks
