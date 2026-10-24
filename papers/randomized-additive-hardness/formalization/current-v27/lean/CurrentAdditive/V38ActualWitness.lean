import CurrentAdditive.V38LocalDiagram
import CurrentAdditive.V38Matrix
import Paper2.SourceProjectionWitness

/-!
Selected v39/v38 src:near-full, robustness.tex:245--261. The selected
source has only ordinary and diagonal tags. The literal witness below uses
one retained template representative for all diagonal words. The three-tail
estimate itself is supplied by src:profiles; this file proves its actual
source restriction and protocol consequence without any older profile.
-/

namespace CurrentAdditive.V38ActualWitness

open Paper2 Paper2.SourceMatrix Paper2.SourceProjection
open Paper2.SourceProjectionDiagonal Paper2.SourceProjectionWitness
open CurrentAdditive.EdgeSourceMatrix CurrentAdditive.V38Matrix
open Workspace.Types.Protocol Workspace.Types.CommComplexity

variable {V E X Y : Type*} [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] {s q₁ q₂ : ℕ} [NeZero s]

/-- The full head-plus-three-tail interlace is an actual submatrix of the
selected two-family source. No removed fixed-tail family is introduced. -/
theorem witness_interlace_le
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4 * s)) E * r)
    (R : X → Y → Bool) (ξ₀ : Tail s Y)
    (bin : Fin s) (α : Fin q₂) (K : Set (Template q₁ q₂ X))
    (B : Fin 3 → Set X) (S : Set (Word q₁ s Y))
    (i₁ i₂ i₀ : Items s V) (p p' : Fin s)
    (h₁ : activity order edge hs r hq i₁ α = some p)
    (h₂ : activity order edge hs r hq i₂ α = some p')
    (h₀ : activity order edge hs r hq i₀ α = none)
    (U : Set (V38Matrix.TaggedColumn q₁ q₂ s Y))
    (A : Set (RawRow q₁ q₂ s X (Items s V)))
    (hK : ∀ z ∈ K, Sum.inl (bin, z) ∈ A)
    (hB : ∀ t u, u ∈ B t → Sum.inr (collisionItem i₁ i₂ i₀ t, u) ∈ A)
    (hS : ∀ γ ∈ S, Sum.inr (α, γ) ∈ U) :
    Compression.restrictionD (fullInterlace R (q₁ + 3))
      (witnessRowsFin α K B) (witnessWords p p' S) ≤
    Compression.restrictionD
      (V38Matrix.matrix order edge hs r hq R ξ₀) U A := by
  classical
  let row : witnessRowsFin α K B → A := fun a =>
    ⟨witnessRow bin α K B i₁ i₂ i₀
      ⟨(finSumFinEquiv.symm a.val.1, a.val.2), a.property⟩,
      witnessRow_mem bin α K B i₁ i₂ i₀ A hK hB _⟩
  let col : witnessWords p p' S → U := fun γ =>
    ⟨Sum.inr (α, (representative
      (wordProjection (selectedCoordinateFin p p')) S γ).val),
      hS _ (representative_survives
        (wordProjection (selectedCoordinateFin p p')) S γ)⟩
  have heq : (fun (a : witnessRowsFin α K B) (γ : witnessWords p p' S) =>
      fullInterlace R (q₁ + 3) a.val γ.val) =
      fun a γ => V38Matrix.matrix order edge hs r hq R ξ₀ (col γ).val (row a).val := by
    funext a γ
    have he := witnessRow_entry R (activity order edge hs r hq) ξ₀
      bin α K B i₁ i₂ i₀ p p' h₁ h₂ h₀
      ⟨(finSumFinEquiv.symm a.val.1, a.val.2), a.property⟩
      (representative (wordProjection (selectedCoordinateFin p p')) S γ).val
    change R a.val.2 (γ.val a.val.1) = _
    change R a.val.2 (γ.val a.val.1) =
      N R (activity order edge hs r hq) ξ₀
        (.diagonal (α, (representative
          (wordProjection (selectedCoordinateFin p p')) S γ).val))
        (witnessRow bin α K B i₁ i₂ i₀
          ⟨(finSumFinEquiv.symm a.val.1, a.val.2), a.property⟩)
    rw [he]
    exact congrArg (R a.val.2)
      (congrFun (representative_maps
        (wordProjection (selectedCoordinateFin p p')) S γ) a.val.1).symm
  change D (fun (a : witnessRowsFin α K B) (γ : witnessWords p p' S) =>
    fullInterlace R (q₁ + 3) a.val γ.val) ≤ _
  rw [heq]
  have hm := Workspace.ProofLemmas.SublemmaPrecompNoIncrease
    (fun (a : A) (u : U) =>
      V38Matrix.matrix order edge hs r hq R ξ₀ u.val a.val) row col
  exact hm.trans_eq (restrictionD_transpose
    (V38Matrix.matrix order edge hs r hq R ξ₀) U A)

/-- Local supplier (iii) from the source theorem's explicit three-tail
estimate. The assumption is on an interlace of the base R, not on the
target source, and all retained representatives are constructed above. -/
theorem marked_protocol_cost
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4 * s)) E * r)
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (ξ₀ : Tail s Y) (H : ℕ) (xcap : ℝ)
    (bin : Fin s) (α : Fin q₂) (K : Set (Template q₁ q₂ X))
    (B : Fin 3 → Set X) (S : Finset (Word q₁ s Y))
    (i₁ i₂ i₀ : Items s V) (p p' : Fin s) (hpp : p ≠ p')
    (h₁ : activity order edge hs r hq i₁ α = some p)
    (h₂ : activity order edge hs r hq i₂ α = some p')
    (h₀ : activity order edge hs r hq i₀ α = none)
    (U : Set (V38Matrix.TaggedColumn q₁ q₂ s Y))
    (A : Set (RawRow q₁ q₂ s X (Items s V)))
    (hK : ∀ z ∈ K, Sum.inl (bin, z) ∈ A)
    (hB : ∀ t u, u ∈ B t → Sum.inr (collisionItem i₁ i₂ i₀ t, u) ∈ A)
    (hS : ∀ γ ∈ S, Sum.inr (α, γ) ∈ U)
    (hhead : ∀ a : Fin q₁, xcap ≤ μ.toFiniteLaw.prob
      (fun u => (a, u) ∈ (fun z => z α) '' K))
    (hbase : ∀ t : Fin 3, xcap ≤ μ.toFiniteLaw.prob (· ∈ B t))
    (hSmass : (1 / 2 : ℝ) < SourceSupportStep.mass
      (ν.iid (q₁ + s + 1)).toFiniteLaw S)
    (threeTail : ∀ (Rows : Set (Fin (q₁ + 3) × X))
      (Words : Set (Fin (q₁ + 3) → Y)),
      (∀ a : Fin (q₁ + 3), xcap ≤ μ.toFiniteLaw.prob (fun u => (a, u) ∈ Rows)) →
      (1 / 2 : ℝ) < (ν.iid (q₁ + 3)).toFiniteLaw.prob (· ∈ Words) →
      H + 1 ≤ Compression.restrictionD (fullInterlace R (q₁ + 3)) Rows Words)
    (P : Protocol A U Bool)
    (hP : P.Computes (fun a u =>
      V38Matrix.matrix order edge hs r hq R ξ₀ u.val a.val)) :
    H + 1 ≤ P.cost := by
  classical
  have hm := witness_word_mass ν p p' hpp (S : Set (Word q₁ s Y))
  have hword : (1 / 2 : ℝ) < (ν.iid (q₁ + 3)).toFiniteLaw.prob
      (· ∈ witnessWords p p' (S : Set (Word q₁ s Y))) := hSmass.trans_le hm
  have hrows (a : Fin (q₁ + 3)) : xcap ≤ μ.toFiniteLaw.prob
      (fun u => (a, u) ∈ witnessRowsFin α K B) := by
    change xcap ≤ μ.toFiniteLaw.prob (fun u =>
      match finSumFinEquiv.symm a with
      | .inl j => (j, u) ∈ (fun z => z α) '' K
      | .inr t => u ∈ B t)
    cases he : finSumFinEquiv.symm a with
    | inl j => simpa only [he] using hhead j
    | inr t => simpa only [he] using hbase t
  have hl := threeTail (witnessRowsFin α K B)
    (witnessWords p p' (S : Set (Word q₁ s Y))) hrows hword
  have hmap := witness_interlace_le order edge hs r hq R ξ₀ bin α K B
    (S : Set (Word q₁ s Y)) i₁ i₂ i₀ p p' h₁ h₂ h₀ U A hK hB hS
  have hu : D (fun (a : A) (u : U) =>
      V38Matrix.matrix order edge hs r hq R ξ₀ u.val a.val) ≤ P.cost :=
    Nat.sInf_le ⟨P, rfl, hP⟩
  have he := restrictionD_transpose (V38Matrix.matrix order edge hs r hq R ξ₀) U A
  exact hl.trans (hmap.trans (he ▸ hu))

end CurrentAdditive.V38ActualWitness

#print axioms CurrentAdditive.V38ActualWitness.witness_interlace_le
#print axioms CurrentAdditive.V38ActualWitness.marked_protocol_cost
