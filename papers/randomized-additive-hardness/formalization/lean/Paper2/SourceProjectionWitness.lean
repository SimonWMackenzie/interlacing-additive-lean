import Paper2.SourceProjection
import Paper2.SourceProjectionDiagonal

/-!
# The actual interlace inside a retained collision witness

Frozen v12 Section 4, `src:near-full`, the usable-witness paragraph.
The rows below consist of the actual head projection of retained templates,
followed by the retained base-row sets of two active and one inactive item.
Each head label is represented by one fixed surviving template. The selected
word tuple is a projection of one surviving whole word, never a Cartesian
product of independently selected coordinate labels.

The resulting matrix is a literal restriction of `fullInterlace R (q₁+3)`.
We prove that its communication cost is bounded above by the cost of the
original retained source rectangle. No communication lower bound or usable
witness existence assertion is assumed or proved in this module.
-/

namespace Paper2.SourceProjectionWitness

open SourceMatrix SourceProjection SourceProjectionDiagonal
open Workspace.Types.CommComplexity

variable {X Y I : Type*} {q₁ q₂ s : ℕ}

/-- Head labels actually realized by the retained templates, and the three
specified retained source-base families. -/
def witnessRows (α : Fin q₂) (A : Set (Template q₁ q₂ X)) (B : Fin 3 → Set X) :
    Set ((Fin q₁ ⊕ Fin 3) × X) :=
  fun a => match a.1 with
    | .inl r => (r, a.2) ∈ (fun z => z α) '' A
    | .inr t => a.2 ∈ B t

/-- The same row labels indexed by the finite ordinal of the interlace. -/
def witnessRowsFin (α : Fin q₂) (A : Set (Template q₁ q₂ X)) (B : Fin 3 → Set X) :
    Set (Fin (q₁ + 3) × X) :=
  (fun a => (finSumFinEquiv.symm a.1, a.2)) ⁻¹' witnessRows α A B

/-- Correlated tuples projected from actual surviving diagonal words. -/
def witnessWords (p p' : Fin s) (W : Set (Word q₁ s Y)) : Set (Fin (q₁ + 3) → Y) :=
  wordProjection (selectedCoordinateFin p p') '' W

/-- The actual source column representing a witness row. In a head block,
the same retained template is used against every word. -/
noncomputable def witnessRow (bin : Fin s) (α : Fin q₂)
    (A : Set (Template q₁ q₂ X)) (B : Fin 3 → Set X) (i₁ i₂ i₀ : I) :
    witnessRows α A B → RawRow q₁ q₂ s X I
  | ⟨(.inl r, u), h⟩ => .inl (bin,
      (representative (fun z : Template q₁ q₂ X => z α) A ⟨(r, u), h⟩).val)
  | ⟨(.inr t, u), _⟩ => .inr (collisionItem i₁ i₂ i₀ t, u)

theorem witnessRow_mem (bin : Fin s) (α : Fin q₂)
    (A : Set (Template q₁ q₂ X)) (B : Fin 3 → Set X) (i₁ i₂ i₀ : I)
    (V : Set (RawRow q₁ q₂ s X I))
    (hA : ∀ z ∈ A, Sum.inl (bin, z) ∈ V)
    (hB : ∀ t u, u ∈ B t → Sum.inr (collisionItem i₁ i₂ i₀ t, u) ∈ V)
    (a : witnessRows α A B) : witnessRow bin α A B i₁ i₂ i₀ a ∈ V := by
  rcases a with ⟨⟨r | t, u⟩, h⟩
  · exact hA _ (representative_survives (fun z : Template q₁ q₂ X => z α) A ⟨(r, u), h⟩)
  · exact hB t u h

theorem witnessRow_entry [NeZero s] (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (bin : Fin s) (α : Fin q₂) (A : Set (Template q₁ q₂ X)) (B : Fin 3 → Set X)
    (i₁ i₂ i₀ : I) (p p' : Fin s)
    (h₁ : activity i₁ α = some p) (h₂ : activity i₂ α = some p')
    (h₀ : activity i₀ α = none) (a : witnessRows α A B) (γ : Word q₁ s Y) :
    N R activity ξ₀ (.diagonal (α, γ)) (witnessRow bin α A B i₁ i₂ i₀ a) =
      R a.val.2 (γ (selectedCoordinate p p' a.val.1)) := by
  rcases a with ⟨⟨r | t, u⟩, h⟩
  · exact diagonal_template_selected_entry R activity ξ₀ α bin p p'
      (representative (fun z : Template q₁ q₂ X => z α) A ⟨(r, u), h⟩).val r u
      (representative_maps (fun z : Template q₁ q₂ X => z α) A ⟨(r, u), h⟩) γ
  · exact diagonal_source_selected_entry R activity ξ₀ α i₁ i₂ i₀ p p' h₁ h₂ h₀ t u γ

/-- The complete witness is an actual restricted `(q₁+3)`-interlace inside
the retained source matrix. Membership assumptions identify surviving inputs;
none states a communication bound. Distinctness of the active positions is
needed for the independent-word marginal, not for this protocol pullback. -/
theorem witness_interlace_D_le [Fintype X] [Fintype Y] [Fintype I] [NeZero s]
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (bin : Fin s) (α : Fin q₂) (A : Set (Template q₁ q₂ X)) (B : Fin 3 → Set X)
    (W : Set (Word q₁ s Y)) (i₁ i₂ i₀ : I) (p p' : Fin s)
    (h₁ : activity i₁ α = some p) (h₂ : activity i₂ α = some p')
    (h₀ : activity i₀ α = none)
    (U : Set (TaggedColumn q₁ q₂ s Y)) (V : Set (RawRow q₁ q₂ s X I))
    (hA : ∀ z ∈ A, Sum.inl (bin, z) ∈ V)
    (hB : ∀ t u, u ∈ B t → Sum.inr (collisionItem i₁ i₂ i₀ t, u) ∈ V)
    (hW : ∀ γ ∈ W, TaggedColumn.diagonal (α, γ) ∈ U) :
    Compression.restrictionD (fullInterlace R (q₁ + 3))
        (witnessRowsFin α A B) (witnessWords p p' W) ≤
      Compression.restrictionD (N R activity ξ₀) U V := by
  classical
  let row : witnessRowsFin α A B → V := fun a =>
    ⟨witnessRow bin α A B i₁ i₂ i₀
        ⟨(finSumFinEquiv.symm a.val.1, a.val.2), a.property⟩,
      witnessRow_mem bin α A B i₁ i₂ i₀ V hA hB _⟩
  let col : witnessWords p p' W → U := fun γ =>
    ⟨.diagonal (α, (representative (wordProjection (selectedCoordinateFin p p')) W γ).val),
      hW _ (representative_survives (wordProjection (selectedCoordinateFin p p')) W γ)⟩
  have heq : (fun (a : witnessRowsFin α A B) (γ : witnessWords p p' W) =>
      fullInterlace R (q₁ + 3) a.val γ.val) =
      fun a γ => N R activity ξ₀ (col γ).val (row a).val := by
    funext a γ
    dsimp only [row, col]
    rw [witnessRow_entry R activity ξ₀ bin α A B i₁ i₂ i₀ p p' h₁ h₂ h₀]
    change R a.val.2 (γ.val a.val.1) = R a.val.2
      ((representative (wordProjection (selectedCoordinateFin p p')) W γ).val
        (selectedCoordinateFin p p' a.val.1))
    exact congrArg (R a.val.2)
      (congrFun (representative_maps (wordProjection (selectedCoordinateFin p p')) W γ)
        a.val.1).symm
  change D (fun (a : witnessRowsFin α A B) (γ : witnessWords p p' W) =>
    fullInterlace R (q₁ + 3) a.val γ.val) ≤ _
  rw [heq]
  have h := Workspace.ProofLemmas.SublemmaPrecompNoIncrease
    (fun (k : V) (Z : U) => N R activity ξ₀ Z.val k.val) row col
  exact h.trans_eq (restrictionD_transpose (N R activity ξ₀) U V)

/-- Independent coordinates in the ambient word law give the projected
witness words at least the original surviving mass. The surviving set itself
can be arbitrarily correlated. -/
theorem witness_word_mass [Fintype Y] (ν : PositiveRationalLaw Y)
    (p p' : Fin s) (hpp : p ≠ p') (W : Set (Word q₁ s Y)) :
    (ν.iid (q₁ + s + 1)).toFiniteLaw.prob (· ∈ W) ≤
      (ν.iid (q₁ + 3)).toFiniteLaw.prob (· ∈ witnessWords p p' W) :=
  word_projection_mass ν (selectedCoordinateFin p p')
    (selectedCoordinateFin_injective p p' hpp) W

end Paper2.SourceProjectionWitness

#print axioms Paper2.SourceProjectionWitness.witness_interlace_D_le
#print axioms Paper2.SourceProjectionWitness.witness_word_mass
