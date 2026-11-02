import Paper2.PairedSelectorMatrix
import Paper2.PairedSelectorCapacityFibre
import Paper2.SourceSupportSchedule

/-!
# Terminal Alice capacities for two selectors

Frozen v12 Section 5, `res:paired`, final paragraph. The selected blocks are
literal tagged coordinates of the original selector pair. The actual Alice
query chooses one joint row event of mass at least 49/128. Bob's retained
word supports stay unchanged. Neither a graph witness nor an assumed
communication lower bound is used in these local capacity calls.
-/

namespace Paper2.PairedSelectorCapacity

open PairedSelectorMatrix Workspace.Types.Protocol

variable {W J : Type*} [Fintype W] [Fintype J] {q n : ℕ}

/-- At least `H+k` bits remain below the genuine Alice message. The scale
premise is exactly the row estimate's premise, not the stronger source
construction's initial-floor bound. -/
theorem alice_power_cost
    (μ : PositiveRationalLaw W) (ν : PositiveRationalLaw J) (R : W → J → Bool)
    (H k : ℕ) {x : ℝ} (hH : 2 ≤ H) (hx : 0 < x) (hk : 2 ≤ k)
    (hscale : (2 : ℝ) ^ k * x ≤ 1)
    (hprofile : RestrictionProfile R μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (e : Fin n → Block q) (he : Function.Injective e)
    (A : Set (Selector q J)) (S : Set (Fin n × W))
    (hn : 2 ^ (k - 1) + 1 ≤ n) (C : Set (Column q W))
    (hS : ∀ a ∈ S, (e a.1, a.2) ∈ C)
    (hrow : ∀ i, (2 : ℝ) ^ k * x ≤ μ.toFiniteLaw.prob (fun w => (i, w) ∈ S))
    (hAmass : (49 / 64 : ℝ) ≤ (selectorLaw ν q).toFiniteLaw.prob (· ∈ A))
    (query : A → Bool) (left right : Protocol A C Bool)
    (hP : (Protocol.aNode query left right).Computes
      (fun a c => matrix R a.val c.val)) :
    H + k + 1 ≤ (Protocol.aNode query left right).cost := by
  classical
  obtain ⟨b, _, hb⟩ := PairedSelectorCapacityFibre.exists_dense_rowFibre
    (selectorLaw ν q).toFiniteLaw A query hAmass
  have hcount : 2 ^ (k - 1) + 1 ≤ (Finset.univ : Finset (Fin n)).card := by
    simpa using hn
  have hl := selected_capacity_power μ ν R H k hH hx hk hscale hprofile
    e he (SourceSupportCapacity.rowFibre A query b) S Finset.univ hcount C hS
    (fun i _ => hrow i) hb
  have hc := SourceSupportCapacity.childProtocol_computes
    (fun a (c : C) => matrix R a c.val) A query left right hP b
  have hu := PairedSelectorCapacityFibre.restrictionD_le_protocol (matrix R)
    (SourceSupportCapacity.rowFibre A query b) C
    (SourceSupportCapacity.childProtocol A query left right b) hc
  have hd := SourceSupportCapacity.childProtocol_cost A query left right b
  omega

/-- Two distinct actual tagged coordinates require the two-copy bound
below the genuine Alice message. -/
theorem alice_two_cost
    (μ : PositiveRationalLaw W) (ν : PositiveRationalLaw J) (R : W → J → Bool)
    (H : ℕ) {x : ℝ} (hH : 2 ≤ H) (hx : 0 < x) (hscale : 2 * x ≤ 1)
    (hprofile : RestrictionProfile R μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (e : Fin n → Block q) (he : Function.Injective e)
    (A : Set (Selector q J)) (S : Set (Fin n × W)) (hn : 2 ≤ n)
    (C : Set (Column q W)) (hS : ∀ a ∈ S, (e a.1, a.2) ∈ C)
    (hrow : ∀ i, 2 * x ≤ μ.toFiniteLaw.prob (fun w => (i, w) ∈ S))
    (hAmass : (49 / 64 : ℝ) ≤ (selectorLaw ν q).toFiniteLaw.prob (· ∈ A))
    (query : A → Bool) (left right : Protocol A C Bool)
    (hP : (Protocol.aNode query left right).Computes
      (fun a c => matrix R a.val c.val)) :
    H + 2 ≤ (Protocol.aNode query left right).cost := by
  classical
  obtain ⟨b, _, hb⟩ := PairedSelectorCapacityFibre.exists_dense_rowFibre
    (selectorLaw ν q).toFiniteLaw A query hAmass
  have hcount : 2 ≤ (Finset.univ : Finset (Fin n)).card := by simpa using hn
  have hl := selected_capacity_two μ ν R H hH hx hscale hprofile
    e he (SourceSupportCapacity.rowFibre A query b) S Finset.univ hcount C hS
    (fun i _ => hrow i) hb
  have hc := SourceSupportCapacity.childProtocol_computes
    (fun a (c : C) => matrix R a c.val) A query left right hP b
  have hu := PairedSelectorCapacityFibre.restrictionD_le_protocol (matrix R)
    (SourceSupportCapacity.rowFibre A query b) C
    (SourceSupportCapacity.childProtocol A query left right b) hc
  have hd := SourceSupportCapacity.childProtocol_cost A query left right b
  omega

/-- The large dyadic excess case. The count refers to tagged blocks,
including foreign blocks that have separated from their original pair. -/
theorem alice_power_contradiction
    (μ : PositiveRationalLaw W) (ν : PositiveRationalLaw J) (R : W → J → Bool)
    (H k : ℕ) {x : ℝ} (hH : 2 ≤ H) (hx : 0 < x) (hk : 2 ≤ k)
    (hscale : (2 : ℝ) ^ k * x ≤ 1)
    (hprofile : RestrictionProfile R μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (e : Fin n → Block q) (he : Function.Injective e)
    (A : Set (Selector q J)) (S : Set (Fin n × W))
    (hn : (3 / 4 : ℝ) * (2 : ℝ) ^ k ≤ (n : ℝ))
    (C : Set (Column q W)) (hS : ∀ a ∈ S, (e a.1, a.2) ∈ C)
    (hrow : ∀ i, 2 * (2 : ℝ) ^ k * x ≤ μ.toFiniteLaw.prob (fun w => (i, w) ∈ S))
    (hAmass : (49 / 64 : ℝ) ≤ (selectorLaw ν q).toFiniteLaw.prob (· ∈ A))
    (query : A → Bool) (left right : Protocol A C Bool)
    (hP : (Protocol.aNode query left right).Computes
      (fun a c => matrix R a.val c.val))
    (hcost : (Protocol.aNode query left right).cost ≤ H + k) : False := by
  have hweak : ∀ i, (2 : ℝ) ^ k * x ≤ μ.toFiniteLaw.prob (fun w => (i, w) ∈ S) := by
    intro i
    have hi := hrow i
    have hp : 0 ≤ (2 : ℝ) ^ k * x := by positivity
    nlinarith
  have hl := alice_power_cost μ ν R H k hH hx hk hscale hprofile e he A S
    (SourceSupportSchedule.power_block_count hk hn) C hS hweak hAmass query left right hP
  omega

/-- Capacity two: integer rounding supplies the two distinct tagged blocks. -/
theorem alice_capacity_two_contradiction
    (μ : PositiveRationalLaw W) (ν : PositiveRationalLaw J) (R : W → J → Bool)
    (H : ℕ) {x : ℝ} (hH : 2 ≤ H) (hx : 0 < x) (hscale : 2 * x ≤ 1)
    (hprofile : RestrictionProfile R μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (e : Fin n → Block q) (he : Function.Injective e)
    (A : Set (Selector q J)) (S : Set (Fin n × W))
    (hn : (3 / 4 : ℝ) * 2 ≤ (n : ℝ))
    (C : Set (Column q W)) (hS : ∀ a ∈ S, (e a.1, a.2) ∈ C)
    (hrow : ∀ i, 4 * x ≤ μ.toFiniteLaw.prob (fun w => (i, w) ∈ S))
    (hAmass : (49 / 64 : ℝ) ≤ (selectorLaw ν q).toFiniteLaw.prob (· ∈ A))
    (query : A → Bool) (left right : Protocol A C Bool)
    (hP : (Protocol.aNode query left right).Computes
      (fun a c => matrix R a.val c.val))
    (hcost : (Protocol.aNode query left right).cost ≤ H + 1) : False := by
  have hl := alice_two_cost μ ν R H hH hx hscale hprofile e he A S
    (SourceSupportSchedule.two_block_count hn) C hS
    (fun i => by have hi := hrow i; linarith) hAmass query left right hP
  omega

/-- Capacity one with two counting units. The remaining one-pair case
uses its two tags at the parent and is a separate theorem. -/
theorem alice_capacity_one_many_contradiction
    (μ : PositiveRationalLaw W) (ν : PositiveRationalLaw J) (R : W → J → Bool)
    (H : ℕ) {x : ℝ} (hH : 2 ≤ H) (hx : 0 < x) (hscale : 2 * x ≤ 1)
    (hprofile : RestrictionProfile R μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (e : Fin n → Block q) (he : Function.Injective e)
    (A : Set (Selector q J)) (S : Set (Fin n × W)) (hn : 2 ≤ n)
    (C : Set (Column q W)) (hS : ∀ a ∈ S, (e a.1, a.2) ∈ C)
    (hrow : ∀ i, 2 * x ≤ μ.toFiniteLaw.prob (fun w => (i, w) ∈ S))
    (hAmass : (49 / 64 : ℝ) ≤ (selectorLaw ν q).toFiniteLaw.prob (· ∈ A))
    (query : A → Bool) (left right : Protocol A C Bool)
    (hP : (Protocol.aNode query left right).Computes
      (fun a c => matrix R a.val c.val))
    (hcost : (Protocol.aNode query left right).cost ≤ H) : False := by
  have hl := alice_two_cost μ ν R H hH hx hscale hprofile e he A S hn C hS hrow
    hAmass query left right hP
  omega

end Paper2.PairedSelectorCapacity

#print axioms Paper2.PairedSelectorCapacity.alice_power_cost
#print axioms Paper2.PairedSelectorCapacity.alice_two_cost
#print axioms Paper2.PairedSelectorCapacity.alice_power_contradiction
#print axioms Paper2.PairedSelectorCapacity.alice_capacity_two_contradiction
#print axioms Paper2.PairedSelectorCapacity.alice_capacity_one_many_contradiction
