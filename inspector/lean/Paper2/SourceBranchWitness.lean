import Paper2.SourceSurvivingCollisionsBranches
import Paper2.SourceProtocolPrefixResidual
import Paper2.SourceSupportCapacityWitness

/-!
# The attached witness on its original prefix branch

Frozen v12 Section 4, `src:near-full`, the surviving-collisions paragraph
and the final capacity-one case. An assigned, nondeficient coordinate
provides the actual template and three item-row families on the complete
prefix branch. A retained word support of mass greater than one half then
requires the extra bit at the parent node. None of these item families is
restricted to Alice's later dense-template child.
-/

namespace Paper2.SourceBranchWitness

open Workspace.Types.Protocol Workspace.Types.CommComplexity
open SourceMatrix SourceDeficiency SourceSurvivingCollisions SourceProtocolPrefix

variable {V E X Y : Type*} [Fintype V] [Nonempty V] [Fintype E]
  [Fintype X] [Fintype Y] {q₁ q₂ a : ℕ} [NeZero q₁] [NeZero q₂]

local instance (a : ℕ) : NeZero (2 ^ a) := ⟨by positivity⟩

set_option maxRecDepth 2048 in
/-- The capacity-one attached witness contradicts a `d+a`-bit protocol
on the actual parent row carrier. The three item sets, their masses, and
all source-position identities are derived from the assigned collision.

The support may be any set of original word labels present in `C`. In the
support recursion it is additionally a subset of the initial diagonal
support, but that stronger inclusion is unnecessary for this contradiction.
No source communication lower bound is an input. -/
theorem branch_witness_contradiction
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (ξ₀ : Tail (2 ^ a) Y)
    (d : ℕ) (ρ : ℝ) (hd : 2 ≤ d) (ha : 1 ≤ a) (hρ : 0 < ρ)
    (hs : 4 ≤ 2 ^ a) (hq₁ : q₁ + 3 = 2 ^ a + 1)
    (hscale : 4 * ((2 ^ a : ℕ) : ℝ) ^ 2 * ρ ≤ 1)
    (hprofile : RestrictionProfile R μ.toFiniteLaw ν.toFiniteLaw ρ (d : ℤ))
    (order : SourceConstruction.Items (2 ^ a) V ≃
      Fin (Fintype.card (SourceConstruction.Items (2 ^ a) V)))
    (edge : E → Bool → V) (r : ℕ)
    (hq₂ : q₂ = SourceItems.sourceQ0 (Fin (4 * 2 ^ a)) E * r)
    (W : Set (RawRow q₁ q₂ (2 ^ a) X (SourceConstruction.Items (2 ^ a) V)))
    (U : Set (TaggedColumn q₁ q₂ (2 ^ a) Y))
    (Praw : Protocol W U Bool) (dom : Fin (2 ^ a) → Fin (2 ^ a))
    (b : Fin (2 ^ a)) (α : Fin q₂)
    (hassigned : α ∈ assignedCoordinates edge r hq₂ μ W (rowCode W Praw a) b)
    (husable : α ∉ branchDeficient μ ν
      (branchTemplates W (rowCode W Praw a) dom b) U (2 * ((2 ^ a : ℕ) : ℝ) * ρ))
    (S : Finset (Word q₁ (2 ^ a) Y))
    (hS : (1 / 2 : ℝ) < (ν.iid (q₁ + 2 ^ a + 1)).toFiniteLaw.prob (· ∈ S))
    (C : Set (TaggedColumn q₁ q₂ (2 ^ a) Y))
    (hC : ∀ word ∈ S, TaggedColumn.diagonal (α, word) ∈ C)
    (Q : Protocol (branchRows W Praw a b) C Bool)
    (hQ : Q.Computes (fun w z => SourceConstruction.matrix order edge
      (by omega) r hq₂ R ξ₀ z.val w.val))
    (hcost : Q.cost ≤ d + a) : False := by
  classical
  have hs₃ : 3 ≤ 2 ^ a := by omega
  let A : Set (Template q₁ q₂ X) := branchTemplates W (rowCode W Praw a) dom b
  obtain ⟨i₁, i₂, i₀, p, p', _, hpp, hi₁, hi₂, hi₀, hm₁, hm₂, hm₀⟩ :=
    assignedCoordinates_items order edge hs₃ r hq₂ μ W (rowCode W Praw a) b α
      hassigned ρ hscale
  let B : Fin 3 → Set X := fun k =>
    {u | Sum.inr (SourceProjectionDiagonal.collisionItem i₁ i₂ i₀ k, u) ∈
      branchRows W Praw a b}
  have hrowsA : ∀ z ∈ A, Sum.inl (dom b, z) ∈ branchRows W Praw a b := by
    intro z hz
    exact hz
  have hrowsB : ∀ k u, u ∈ B k →
      Sum.inr (SourceProjectionDiagonal.collisionItem i₁ i₂ i₀ k, u) ∈
        branchRows W Praw a b := by
    intro k u hu
    exact hu
  have hmassB : ∀ k, 2 * ((2 ^ a : ℕ) : ℝ) * ρ ≤ μ.toFiniteLaw.prob (· ∈ B k) := by
    intro k
    fin_cases k
    · exact hm₁
    · exact hm₂
    · exact hm₀
  have hhead : ∀ j, 2 * ((2 ^ a : ℕ) : ℝ) * ρ ≤ μ.toFiniteLaw.prob
      (fun u => (j, u) ∈ (fun z : Template q₁ q₂ X => z α) '' A) := by
    exact (usable_coordinate_masses μ ν A U (2 * ((2 ^ a : ℕ) : ℝ) * ρ) α husable).1
  have hcap : 2 * ((2 ^ a : ℕ) : ℝ) * ρ ≤ 1 := by
    have hc := row_cap_le_eighth hs ρ hscale
    linarith
  exact SourceSupportCapacityWitness.witness_protocol_contradiction μ ν R
    (SourceConstruction.activity order edge hs₃ r hq₂) ξ₀ d a ρ hd ha hρ rfl hq₁
    hcap hprofile (dom b) α A B (S : Set (Word q₁ (2 ^ a) Y))
    i₁ i₂ i₀ p p' hpp hi₁ hi₂ hi₀ C (branchRows W Praw a b)
    hrowsA hrowsB hC hhead hmassB hS Q hQ hcost

end Paper2.SourceBranchWitness

#print axioms Paper2.SourceBranchWitness.branch_witness_contradiction
