import Paper2.SourceSupportInitialCore
import Paper2.SourceSupportFrontier

/-!
# The actual initial state of the Bob-only conversation

The column map is the literal diagonal tag and every support is its exact
retained fibre. The bad coordinates come from `branchDeficient`; both mass
floors follow from that definition, not from assumed communication bounds.
-/

namespace Paper2.SourceSupportInitial

open Workspace.Types.Protocol SourceMatrix SourceSupportStep SourceSupportFrontier

variable {A X Y I : Type*} [Fintype Y] {q₁ q₂ s : ℕ}

/-- Generic initialization with an explicit actual bad-coordinate set. -/
noncomputable def initial (U : Set (TaggedColumn q₁ q₂ s Y)) (default : U)
    (P : Protocol A U Bool) (assigned B : Finset (Fin q₂)) :
    State A (TaggedColumn q₁ q₂ s Y) (Fin q₂) (Word q₁ s Y) where
  protocol := extendColumns U default P
  columns := U
  coordinates := coordinates B
  attachments := attachments assigned B
  support := diagonalSupport U

theorem initial_attachments_subset (U : Set (TaggedColumn q₁ q₂ s Y)) (default : U)
    (P : Protocol A U Bool) (assigned B : Finset (Fin q₂)) :
    (initial U default P assigned B).attachments ⊆
      (initial U default P assigned B).coordinates :=
  attachments_subset assigned B

theorem initial_coordinates_card (U : Set (TaggedColumn q₁ q₂ s Y)) (default : U)
    (P : Protocol A U Bool) (assigned B : Finset (Fin q₂)) :
    (initial U default P assigned B).coordinates.card + B.card = q₂ :=
  coordinates_card B

theorem initial_attachments_excess (U : Set (TaggedColumn q₁ q₂ s Y)) (default : U)
    (P : Protocol A U Bool) (assigned B : Finset (Fin q₂))
    (hexcess : 4 * B.card < assigned.card) :
    3 * B.card < (initial U default P assigned B).attachments.card :=
  attachments_excess assigned B hexcess

theorem initial_support_reaches (U : Set (TaggedColumn q₁ q₂ s Y)) (default : U)
    (P : Protocol A U Bool) (assigned B : Finset (Fin q₂)) :
    ∀ α ∈ (initial U default P assigned B).coordinates,
      ∀ γ ∈ (initial U default P assigned B).support α,
        TaggedColumn.diagonal (α, γ) ∈ (initial U default P assigned B).columns := by
  intro α _ γ hγ
  exact (mem_diagonalSupport U α γ).mp hγ

theorem initial_eval (U : Set (TaggedColumn q₁ q₂ s Y)) (default : U)
    (P : Protocol A U Bool) (assigned B : Finset (Fin q₂)) (r : A) (c : U) :
    (initial U default P assigned B).protocol.eval r c.val = P.eval r c :=
  extendColumns_eval U default P r c

theorem initial_cost (U : Set (TaggedColumn q₁ q₂ s Y)) (default : U)
    (P : Protocol A U Bool) (assigned B : Finset (Fin q₂)) :
    (initial U default P assigned B).protocol.cost = P.cost :=
  extendColumns_cost U default P

/-- The specialized source state uses exactly the already-defined deficiencies. -/
noncomputable def sourceInitial [Fintype X]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (T : Template q₁ q₂ X → Prop) (U : Set (TaggedColumn q₁ q₂ s Y))
    (xcap : ℝ) (default : U) (P : Protocol A U Bool)
    (assigned : Finset (Fin q₂)) :
    State A (TaggedColumn q₁ q₂ s Y) (Fin q₂) (Word q₁ s Y) :=
  initial U default P assigned (SourceDeficiency.branchDeficient μ ν T U xcap)

theorem sourceInitial_mass [Fintype X]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (T : Template q₁ q₂ X → Prop) (U : Set (TaggedColumn q₁ q₂ s Y))
    (xcap : ℝ) (default : U) (P : Protocol A U Bool) (assigned : Finset (Fin q₂)) :
    ∀ α ∈ (sourceInitial μ ν T U xcap default P assigned).coordinates,
      (3 / 4 : ℝ) ≤ mass (ν.iid (q₁ + s + 1)).toFiniteLaw
        ((sourceInitial μ ν T U xcap default P assigned).support α) :=
  usable_mass μ ν T U xcap

/-- Both inputs to the recursive mass invariant come from the same actual
`3/4` initial floor. This also covers an empty assigned set. -/
theorem sourceInitial_floors [Fintype X]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (T : Template q₁ q₂ X → Prop) (U : Set (TaggedColumn q₁ q₂ s Y))
    (xcap floor0 : ℝ) (hfloor : floor0 ≤ 3 / 4) (default : U)
    (P : Protocol A U Bool) (assigned : Finset (Fin q₂)) :
    (∀ α ∈ (sourceInitial μ ν T U xcap default P assigned).coordinates,
      floor0 ≤ mass (ν.iid (q₁ + s + 1)).toFiniteLaw
        ((sourceInitial μ ν T U xcap default P assigned).support α)) ∧
    (∀ α ∈ (sourceInitial μ ν T U xcap default P assigned).attachments,
      (3 / 4 - floor0) + floor0 ≤ mass (ν.iid (q₁ + s + 1)).toFiniteLaw
        ((sourceInitial μ ν T U xcap default P assigned).support α)) := by
  have hm := sourceInitial_mass μ ν T U xcap default P assigned
  constructor
  · exact fun α hα => hfloor.trans (hm α hα)
  · intro α hα
    have hh := hm α (initial_attachments_subset U default P assigned _ hα)
    linarith

/-- Initialize from the actual selected common-prefix branch. -/
noncomputable def sourceBranch [Fintype X]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (T : Template q₁ q₂ X → Prop) (U : Set (TaggedColumn q₁ q₂ s Y))
    (xcap : ℝ) (default : U) (W : Set (RawRow q₁ q₂ s X I))
    (P : Protocol W U Bool) (a : ℕ) (j : Fin (2 ^ a))
    (assigned : Finset (Fin q₂)) :
    State (SourceProtocolPrefix.branchRows W P a j)
      (TaggedColumn q₁ q₂ s Y) (Fin q₂) (Word q₁ s Y) :=
  sourceInitial μ ν T U xcap default (SourceProtocolPrefix.branchProtocol W P a j) assigned

theorem sourceBranch_eval [Fintype X]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (T : Template q₁ q₂ X → Prop) (U : Set (TaggedColumn q₁ q₂ s Y))
    (xcap : ℝ) (default : U) (W : Set (RawRow q₁ q₂ s X I))
    (P : Protocol W U Bool) (a : ℕ) (j : Fin (2 ^ a)) (assigned : Finset (Fin q₂))
    (hp : SourceProtocolPrefixTree.CompleteAlicePrefix a P)
    (r : SourceProtocolPrefix.branchRows W P a j) (c : U) :
    (sourceBranch μ ν T U xcap default W P a j assigned).protocol.eval r c.val =
      P.eval (SourceProtocolPrefix.branchInput W P a j r) c :=
  extended_branch_eval U default W P a j hp r c

theorem sourceBranch_cost [Fintype X]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (T : Template q₁ q₂ X → Prop) (U : Set (TaggedColumn q₁ q₂ s Y))
    (xcap : ℝ) (default : U) (W : Set (RawRow q₁ q₂ s X I))
    (P : Protocol W U Bool) (a H : ℕ) (j : Fin (2 ^ a)) (assigned : Finset (Fin q₂))
    (hp : SourceProtocolPrefixTree.CompleteAlicePrefix a P) (hcost : P.cost ≤ H + a) :
    (sourceBranch μ ν T U xcap default W P a j assigned).protocol.cost ≤ H :=
  extended_branch_cost U default W P a H j hp hcost

theorem sourceBranch_computes [Fintype X] [NeZero s]
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (T : Template q₁ q₂ X → Prop) (U : Set (TaggedColumn q₁ q₂ s Y))
    (xcap : ℝ) (default : U) (W : Set (RawRow q₁ q₂ s X I))
    (P : Protocol W U Bool) (a : ℕ) (j : Fin (2 ^ a)) (assigned : Finset (Fin q₂))
    (hp : SourceProtocolPrefixTree.CompleteAlicePrefix a P)
    (hP : P.Computes (fun r c => N R activity ξ₀ c.val r.val)) :
    ∀ (r : SourceProtocolPrefix.branchRows W P a j) c,
      c ∈ (sourceBranch μ ν T U xcap default W P a j assigned).columns →
      (sourceBranch μ ν T U xcap default W P a j assigned).protocol.eval r c =
        N R activity ξ₀ c r.val :=
  extended_source_branch_computes R activity ξ₀ U default W P a j hp hP

end Paper2.SourceSupportInitial
