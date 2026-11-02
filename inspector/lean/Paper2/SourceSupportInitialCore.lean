import Paper2.SourceDeficiencyBudget
import Paper2.SourceCollisionPartition
import Paper2.SourceProtocolPrefixResidual
import Paper2.SourceSupportStep

/-!
# Initial retained word supports and the ambient-column protocol

Frozen v12 Section 4, `src:near-full`: the remaining conversation starts
on the original retained diagonal columns at every nondeficient coordinate.
The ambient-column extension changes no protocol node or cost. Outside the
retained set it uses one explicitly supplied default column; none of those
outside inputs belong to the initial state.
-/

namespace Paper2.SourceSupportInitial

open Workspace.Types.Protocol SourceMatrix SourceSupportStep

variable {A C : Type*}

/-- A retraction onto retained columns, identical on every retained input. -/
noncomputable def columnRetraction (U : Set C) (default : U) (c : C) : U := by
  classical
  exact if hc : c ∈ U then ⟨c, hc⟩ else default

@[simp] theorem columnRetraction_retained (U : Set C) (default : U) (c : U) :
    columnRetraction U default c.val = c := by
  classical
  simp [columnRetraction, c.property]

/-- Extend only the column carrier, preserving the literal protocol tree. -/
noncomputable def extendColumns (U : Set C) (default : U) (P : Protocol A U Bool) :
    Protocol A C Bool :=
  NPCC.Protocol.pullback id (columnRetraction U default) P

@[simp] theorem extendColumns_cost (U : Set C) (default : U) (P : Protocol A U Bool) :
    (extendColumns U default P).cost = P.cost :=
  NPCC.Protocol.pullback_cost _ _ _

@[simp] theorem extendColumns_eval (U : Set C) (default : U)
    (P : Protocol A U Bool) (a : A) (c : U) :
    (extendColumns U default P).eval a c.val = P.eval a c := by
  simp [extendColumns]

theorem extendColumns_computesOn (U : Set C) (default : U)
    (P : Protocol A U Bool) (F : A → C → Bool)
    (hP : P.Computes (fun a c => F a c.val)) :
    ∀ a c, c ∈ U → (extendColumns U default P).eval a c = F a c := by
  intro a c hc
  exact (extendColumns_eval U default P a ⟨c, hc⟩).trans (hP a ⟨c, hc⟩)

variable {X Y I : Type*} {q₁ q₂ s : ℕ}

/-- Full diagonal words retained in the original column set. -/
noncomputable def diagonalSupport [Fintype Y]
    (U : Set (TaggedColumn q₁ q₂ s Y)) (α : Fin q₂) : Finset (Word q₁ s Y) := by
  classical
  exact Finset.univ.filter fun γ => TaggedColumn.diagonal (α, γ) ∈ U

@[simp] theorem mem_diagonalSupport [Fintype Y]
    (U : Set (TaggedColumn q₁ q₂ s Y)) (α : Fin q₂) (γ : Word q₁ s Y) :
    γ ∈ diagonalSupport U α ↔ TaggedColumn.diagonal (α, γ) ∈ U := by
  classical
  simp [diagonalSupport]

theorem diagonalSupport_mass [Fintype Y] (ν : PositiveRationalLaw Y)
    (U : Set (TaggedColumn q₁ q₂ s Y)) (α : Fin q₂) :
    mass (ν.iid (q₁ + s + 1)).toFiniteLaw (diagonalSupport U α) =
      (ν.iid (q₁ + s + 1)).toFiniteLaw.prob
        (fun γ => TaggedColumn.diagonal (α, γ) ∈ U) := by
  simp only [mass, mem_diagonalSupport]

/-- The surviving coordinates, with no replacement or renumbering. -/
def coordinates (B : Finset (Fin q₂)) : Finset (Fin q₂) := Finset.univ \ B

/-- Attachments keep their original assigned coordinates. -/
def attachments (assigned B : Finset (Fin q₂)) : Finset (Fin q₂) := assigned \ B

@[simp] theorem mem_coordinates (B : Finset (Fin q₂)) (α : Fin q₂) :
    α ∈ coordinates B ↔ α ∉ B := by
  simp [coordinates]

@[simp] theorem mem_attachments (assigned B : Finset (Fin q₂)) (α : Fin q₂) :
    α ∈ attachments assigned B ↔ α ∈ assigned ∧ α ∉ B := by
  simp [attachments]

theorem attachments_subset (assigned B : Finset (Fin q₂)) :
    attachments assigned B ⊆ coordinates B := by
  intro α hα
  exact (mem_coordinates B α).mpr ((mem_attachments assigned B α).mp hα).2

theorem coordinates_card (B : Finset (Fin q₂)) :
    (coordinates B).card + B.card = q₂ := by
  simpa [coordinates] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ B)

theorem attachments_card (assigned B : Finset (Fin q₂)) :
    (attachments assigned B).card + (assigned ∩ B).card = assigned.card := by
  exact Finset.card_sdiff_add_card_inter assigned B

theorem attachments_excess (assigned B : Finset (Fin q₂))
    (hexcess : 4 * B.card < assigned.card) :
    3 * B.card < (attachments assigned B).card :=
  SourceCollisionPartition.survivors_excess assigned B hexcess

/-- The source's actual deficient set supplies the initial `3/4` word floor. -/
theorem usable_mass [Fintype X] [Fintype Y]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (T : Template q₁ q₂ X → Prop) (U : Set (TaggedColumn q₁ q₂ s Y))
    (xcap : ℝ) :
    ∀ α ∈ coordinates (SourceDeficiency.branchDeficient μ ν T U xcap),
      (3 / 4 : ℝ) ≤ mass (ν.iid (q₁ + s + 1)).toFiniteLaw (diagonalSupport U α) := by
  intro α hα
  rw [diagonalSupport_mass]
  exact (SourceDeficiency.usable_coordinate_masses μ ν T U xcap α
    ((mem_coordinates _ α).mp hα)).2

/-- A genuine retained diagonal fibre supplies the extension's default;
there is no independent nonemptiness assumption on the ambient carrier. -/
theorem retained_nonempty_of_mass [Fintype Y] (ν : PositiveRationalLaw Y)
    (U : Set (TaggedColumn q₁ q₂ s Y)) (α : Fin q₂)
    (h : 0 < mass (ν.iid (q₁ + s + 1)).toFiniteLaw (diagonalSupport U α)) :
    U.Nonempty := by
  classical
  by_contra hn
  have he : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
  simp [he, mass, diagonalSupport] at h

/-- The extended selected branch evaluates exactly as the original
retained-input protocol; the common-prefix theorem identifies this branch. -/
theorem extended_branch_eval (U : Set C) (default : U) (W : Set A)
    (P : Protocol W U Bool) (a : ℕ) (j : Fin (2 ^ a))
    (hp : SourceProtocolPrefixTree.CompleteAlicePrefix a P)
    (r : SourceProtocolPrefix.branchRows W P a j) (c : U) :
    (extendColumns U default (SourceProtocolPrefix.branchProtocol W P a j)).eval r c.val =
      P.eval (SourceProtocolPrefix.branchInput W P a j r) c := by
  rw [extendColumns_eval]
  exact SourceProtocolPrefix.branchProtocol_eval W P a j hp r c

theorem extended_branch_cost (U : Set C) (default : U) (W : Set A)
    (P : Protocol W U Bool) (a H : ℕ) (j : Fin (2 ^ a))
    (hp : SourceProtocolPrefixTree.CompleteAlicePrefix a P) (hcost : P.cost ≤ H + a) :
    (extendColumns U default (SourceProtocolPrefix.branchProtocol W P a j)).cost ≤ H := by
  rw [extendColumns_cost]
  exact SourceProtocolPrefix.branchProtocol_cost W P a H j hp hcost

/-- In the source application, this is the literal matrix entry, not an
assumed communication lower bound for a newly chosen matrix. -/
theorem extended_source_branch_computes [NeZero s]
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (U : Set (TaggedColumn q₁ q₂ s Y)) (default : U)
    (W : Set (RawRow q₁ q₂ s X I)) (P : Protocol W U Bool)
    (a : ℕ) (j : Fin (2 ^ a))
    (hp : SourceProtocolPrefixTree.CompleteAlicePrefix a P)
    (hP : P.Computes (fun r c => N R activity ξ₀ c.val r.val)) :
    ∀ (r : SourceProtocolPrefix.branchRows W P a j) c, c ∈ U →
      (extendColumns U default (SourceProtocolPrefix.branchProtocol W P a j)).eval r c =
        N R activity ξ₀ c r.val := by
  intro r c hc
  exact (extended_branch_eval U default W P a j hp r ⟨c, hc⟩).trans
    (hP (SourceProtocolPrefix.branchInput W P a j r) ⟨c, hc⟩)

end Paper2.SourceSupportInitial
