import Paper2.SourceSupportInitial
import Paper2.SourceRemainingConversation
import Paper2.SourceBranchWitness

/-!
# The selected source branch cannot have the short budget

Frozen v12 Section 4, `src:near-full`. This symbolic-width adapter builds
the actual retained support state on the chosen protocol branch. It then
discharges every premise of the remaining-conversation argument, including
the attached-witness continuation using actual source collision items.
Public parameter compilation and selecting this branch are separate inputs.
-/

namespace Paper2.SourceBranchContradiction

open Workspace.Types.Protocol
open SourceMatrix SourceDeficiency SourceSurvivingCollisions SourceProtocolPrefix

variable {V E X Y : Type*} [Fintype V] [Nonempty V] [Fintype E]
  [Fintype X] [Fintype Y] {q₁ q₂ a : ℕ} [NeZero q₁] [NeZero q₂]

local instance (a : ℕ) : NeZero (2 ^ a) := ⟨by positivity⟩

/-- A concrete assigned branch with more than four times as many collision
coordinates as deficient coordinates cannot meet the short branch budget.
No frontier or attachment lower-bound certificate is a premise. -/
theorem branch_contradiction
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (ξ₀ : Tail (2 ^ a) Y)
    (d ell : ℕ) (ρ x : ℝ) (hd : 2 ≤ d) (ha : 1 ≤ a)
    (hρ : 0 < ρ) (hx : 0 < x) (hs : 4 ≤ 2 ^ a)
    (hq₁ : q₁ + 3 = 2 ^ a + 1) (hqPower : q₂ = 2 ^ ell)
    (hscale : 4 * ((2 ^ a : ℕ) : ℝ) ^ 2 * ρ ≤ 1)
    (hfloor : SourceSupportSchedule.floor q₂ x 0 ≤ 1 / 8)
    (baseProfile : RestrictionProfile R μ.toFiniteLaw ν.toFiniteLaw ρ (d : ℤ))
    (innerProfile : RestrictionProfile (fun (γ : Word q₁ (2 ^ a) Y) j => M₁ R j γ)
      (ν.iid (q₁ + 2 ^ a + 1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw x ((d + a : ℕ) : ℤ))
    (order : SourceConstruction.Items (2 ^ a) V ≃
      Fin (Fintype.card (SourceConstruction.Items (2 ^ a) V)))
    (edge : E → Bool → V) (r : ℕ)
    (hqGraph : q₂ = SourceItems.sourceQ0 (Fin (4 * 2 ^ a)) E * r)
    (W : Set (RawRow q₁ q₂ (2 ^ a) X (SourceConstruction.Items (2 ^ a) V)))
    (U : Set (TaggedColumn q₁ q₂ (2 ^ a) Y))
    (Praw : Protocol W U Bool) (dom : Fin (2 ^ a) → Fin (2 ^ a)) (b : Fin (2 ^ a))
    (hAmass : (998 / 1000 : ℝ) <
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob
        (branchTemplates W (rowCode W Praw a) dom b))
    (hKB : 4 * (branchDeficient μ ν (branchTemplates W (rowCode W Praw a) dom b)
        U (2 * ((2 ^ a : ℕ) : ℝ) * ρ)).card <
      (assignedCoordinates edge r hqGraph μ W (rowCode W Praw a) b).card)
    (hBP : (branchProtocol W Praw a b).Computes (fun w z =>
      SourceConstruction.matrix order edge (by omega) r hqGraph R ξ₀ z.val w.val))
    (hBcost : (branchProtocol W Praw a b).cost ≤ d + a + ell) : False := by
  classical
  let code := rowCode W Praw a
  let act := SourceConstruction.activity order edge (show 3 ≤ 2 ^ a by omega) r hqGraph
  let A : Set (Template q₁ q₂ X) := branchTemplates W code dom b
  let B := branchDeficient μ ν A U (2 * ((2 ^ a : ℕ) : ℝ) * ρ)
  let K := assignedCoordinates edge r hqGraph μ W code b
  let rows := branchRows W Praw a b
  let Q := branchProtocol W Praw a b
  have hexcess : 3 * B.card < (K \ B).card :=
    SourceSupportInitial.attachments_excess K B hKB
  have hK : (K \ B).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨α, hα⟩ := hK
  have hmα := (usable_coordinate_masses μ ν A U
    (2 * ((2 ^ a : ℕ) : ℝ) * ρ) α (Finset.mem_sdiff.mp hα).2).2
  have hnonempty := SourceSupportInitial.retained_nonempty_of_mass ν U α (by
    rw [SourceSupportInitial.diagonalSupport_mass]
    linarith)
  obtain ⟨z₀, hz₀⟩ := hnonempty
  let default : U := ⟨z₀, hz₀⟩
  let initial := SourceSupportInitial.sourceInitial μ ν A U
    (2 * ((2 ^ a : ℕ) : ℝ) * ρ) default Q K
  have hinitP : ∀ row : rows, ∀ z ∈ initial.columns,
      initial.protocol.eval row z = N R act ξ₀ z row.val :=
    SourceSupportInitial.extendColumns_computesOn U default Q
      (fun row z => N R act ξ₀ z row.val) hBP
  have hinitcost : initial.protocol.cost ≤ d + a + ell := by
    simpa only [initial, SourceSupportInitial.sourceInitial,
      SourceSupportInitial.initial_cost] using hBcost
  have htemplate : ∀ z ∈ A, Sum.inl (dom b, z) ∈ rows := fun _ hz => hz
  have hfloors := SourceSupportInitial.sourceInitial_floors μ ν A U
    (2 * ((2 ^ a : ℕ) : ℝ) * ρ) (SourceSupportSchedule.floor q₂ x 0)
    (by linarith) default Q K
  apply SourceRemainingConversation.remaining_conversation_contradiction
    μ ν R act ξ₀ (d + a) ell (by omega) hqPower x hx hfloor innerProfile
    (dom b) A rows htemplate hAmass initial hinitP hinitcost
    (SourceSupportInitial.initial_attachments_subset U default Q K B)
    B.card (SourceSupportInitial.initial_coordinates_card U default Q K B)
    (SourceSupportInitial.initial_attachments_excess U default Q K B hKB)
    hfloors.1
    (fun i hi => SourceSupportInitial.sourceInitial_mass μ ν A U
      (2 * ((2 ^ a : ℕ) : ℝ) * ρ) default Q K i
        (SourceSupportInitial.initial_attachments_subset U default Q K B hi))
    (SourceSupportInitial.initial_support_reaches U default Q K B)
  intro α hα S _ hSmass C hC Q' hQ' hQcost
  have hmem : α ∈ K ∧ α ∉ B := Finset.mem_sdiff.mp hα
  exact SourceBranchWitness.branch_witness_contradiction μ ν R ξ₀ d ρ
    hd ha hρ hs hq₁ hscale baseProfile order edge r hqGraph W U Praw dom b α
    hmem.1 hmem.2 S hSmass C hC Q' hQ' hQcost

end Paper2.SourceBranchContradiction

#print axioms Paper2.SourceBranchContradiction.branch_contradiction
