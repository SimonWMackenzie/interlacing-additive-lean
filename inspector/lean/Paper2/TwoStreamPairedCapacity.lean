import Paper2.TwoStreamMatrix
import Paper2.PairedSelectorObstruction

/-!
# Capacity-one parent restriction for the actual two-stream matrix

Frozen v12 Section 5, `res:two-stream`, capacity-one attached-parent case.
The theorem below transports the checked T17 obstruction to surviving
original rows and tagged columns. It does not assert a frontier node exists.
-/

namespace Paper2.TwoStreamPairedCapacity

open Workspace.Types.CommComplexity
open Paper2.PairedSelectorMatrix Paper2.PairedSelectorPopulation
open Paper2.SourceProjection

variable {W J Rw Ω F E : Type*} [Fintype W] [Fintype J]
  [Fintype Rw] [Fintype Ω] [Fintype F] [Fintype E]
  {q s : ℕ} [NeZero q]

/-- The actual ordinary and foreign maps land in the genuinely tagged
T17 column space. The two tags never identify equal projected words. -/
def columnProjection (Φ : Ω → Fin s → Fin q × W) (ψ : F → Fin q × W)
    (star : Fin s) : (Ω ⊕ F) → Column q W
  | .inl c => ((false, (Φ c star).1), (Φ c star).2)
  | .inr f => ((true, (ψ f).1), (ψ f).2)

/-- The image of the two retained original column families is exactly
T17's original tagged column restriction, not a completed product. -/
theorem columnProjection_image
    (Φ : Ω → Fin s → Fin q × W) (ψ : F → Fin q × W)
    (star : Fin s) (O : Set Ω) (G : Set F) :
    columnProjection Φ ψ star '' ((Sum.inl '' O) ∪ (Sum.inr '' G)) =
      columns ((fun c => Φ c star) '' O) (ψ '' G) := by
  classical
  ext b
  rcases b with ⟨⟨tag, j⟩, w⟩
  cases tag with
  | false =>
      constructor
      · rintro ⟨c, hc, he⟩
        rcases hc with ⟨o, ho, rfl⟩ | ⟨f, hf, rfl⟩
        · simp only [columnProjection] at he
          cases he
          exact ⟨o, ho, rfl⟩
        · simp [columnProjection] at he
      · intro hb
        rcases hb with ⟨o, ho, he⟩
        refine ⟨.inl o, Or.inl ⟨o, ho, rfl⟩, ?_⟩
        simpa [columnProjection] using congrArg
          (fun p : Fin q × W => ((false, p.1), p.2)) he
  | true =>
      constructor
      · rintro ⟨c, hc, he⟩
        rcases hc with ⟨o, ho, rfl⟩ | ⟨f, hf, rfl⟩
        · simp [columnProjection] at he
        · simp only [columnProjection] at he
          cases he
          exact ⟨f, hf, rfl⟩
      · intro hb
        rcases hb with ⟨f, hf, he⟩
        refine ⟨.inr f, Or.inr ⟨f, hf, rfl⟩, ?_⟩
        simpa [columnProjection] using congrArg
          (fun p : Fin q × W => ((true, p.1), p.2)) he

/-- The T17 paired-selector matrix is a restriction of the actual
two-stream matrix on surviving original labels. `hordinary` and
`hforeign` are precisely the stipulated pointwise entries. -/
theorem paired_source_D_le
    (base : W → J → Bool) (M : Rw → (Ω ⊕ F) → Bool)
    (bin : Rw → Fin s) (selector : Rw → Fin q → J)
    (Φ : Ω → Fin s → Fin q × W) (ψ : F → Fin q × W)
    (star : Fin s) (ι : E → Rw) (ζ : E → Selector q J)
    (hordinary : ∀ r c,
      M r (.inl c) = base (Φ c (bin r)).2
        (selector r (Φ c (bin r)).1))
    (hstar : ∀ a, bin (ι a) = star ∧ selector (ι a) = (ζ a).1)
    (hforeign : ∀ a f,
      M (ι a) (.inr f) = base (ψ f).2 ((ζ a).2 (ψ f).1))
    (P : Set E) (R : Set Rw) (O : Set Ω) (G : Set F)
    (hι : ∀ a ∈ P, ι a ∈ R) :
    Compression.restrictionD (matrix base) (ζ '' P)
        (columns ((fun c => Φ c star) '' O) (ψ '' G)) ≤
      Compression.restrictionD M R ((Sum.inl '' O) ∪ (Sum.inr '' G)) := by
  classical
  let C : Set (Ω ⊕ F) := (Sum.inl '' O) ∪ (Sum.inr '' G)
  let proj := columnProjection Φ ψ star
  have hC : proj '' C = columns ((fun c => Φ c star) '' O) (ψ '' G) :=
    columnProjection_image Φ ψ star O G
  let row : (ζ '' P) → R := fun a =>
    ⟨ι (representative ζ P a).val, hι _ (representative ζ P a).property⟩
  let col : (columns ((fun c => Φ c star) '' O) (ψ '' G)) → C :=
    fun b => representative proj C ⟨b.val, hC.symm ▸ b.property⟩
  have heq : (fun (a : ζ '' P)
        (b : columns ((fun c => Φ c star) '' O) (ψ '' G)) =>
        matrix base a.val b.val) =
      fun a b => M (row a).val (col b).val := by
    funext a b
    rcases hc : (col b).val with o | f
    · change matrix base a.val b.val = M (ι (representative ζ P a).val) (.inl o)
      have hp := representative_maps proj C ⟨b.val, hC.symm ▸ b.property⟩
      change proj (col b).val = b.val at hp
      have hz := representative_maps ζ P a
      rw [hordinary, (hstar _).1, (hstar _).2, ← hz, ← hp]
      simp [proj, columnProjection, hc, matrix, coordinate]
    · change matrix base a.val b.val = M (ι (representative ζ P a).val) (.inr f)
      have hp := representative_maps proj C ⟨b.val, hC.symm ▸ b.property⟩
      change proj (col b).val = b.val at hp
      have hz := representative_maps ζ P a
      rw [hforeign, ← hz, ← hp]
      simp [proj, columnProjection, hc, matrix, coordinate]
  change Workspace.Types.CommComplexity.D
    (fun (a : ζ '' P)
      (b : columns ((fun c => Φ c star) '' O) (ψ '' G)) =>
      matrix base a.val b.val) ≤ _
  rw [heq]
  exact Workspace.ProofLemmas.SublemmaPrecompNoIncrease
    (fun (a : R) (b : C) => M a.val b.val) row col

/-- Capacity one with an attached paired family contradicts a parent
budget of `H+ell`: the extra bit is T17's proved obstruction. -/
theorem parent_capacity
    (μ : PositiveRationalLaw W) (ν : PositiveRationalLaw J)
    (base : W → J → Bool) (M : Rw → (Ω ⊕ F) → Bool)
    (H ell : ℕ) (hH : 2 ≤ H) (hq : q = 2 ^ ell)
    (x : ℝ) (hx : 0 < x)
    (hprofile : RestrictionProfile base μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (bin : Rw → Fin s) (selector : Rw → Fin q → J)
    (Φ : Ω → Fin s → Fin q × W) (ψ : F → Fin q × W)
    (star : Fin s) (ι : E → Rw) (ζ : E → Selector q J)
    (hordinary : ∀ r c,
      M r (.inl c) = base (Φ c (bin r)).2
        (selector r (Φ c (bin r)).1))
    (hstar : ∀ a, bin (ι a) = star ∧ selector (ι a) = (ζ a).1)
    (hforeign : ∀ a f,
      M (ι a) (.inr f) = base (ψ f).2 ((ζ a).2 (ψ f).1))
    (P : Set E) (R : Set Rw) (O : Set Ω) (G : Set F)
    (hι : ∀ a ∈ P, ι a ∈ R)
    (ε δ : ℝ)
    (hA : (49 / 64 : ℝ) ≤ (selectorLaw ν q).toFiniteLaw.prob (· ∈ ζ '' P))
    (hO : 1 - ε ≤ (columnLaw μ).toFiniteLaw.prob
      (· ∈ (fun c => Φ c star) '' O))
    (hF : δ ≤ (columnLaw μ).toFiniteLaw.prob (· ∈ ψ '' G))
    (hδpos : 0 < δ) (hδ : δ ≤ 1)
    (hslack : 2 * q * x + 5 * ε + 2 / q ≤ δ) :
    H + ell + 1 ≤ Compression.restrictionD M R
      ((Sum.inl '' O) ∪ (Sum.inr '' G)) := by
  exact (PairedSelectorObstruction.restriction_lower μ ν base H ell hH hq x hx
    hprofile (ζ '' P) ((fun c => Φ c star) '' O) (ψ '' G)
    ε δ hA hO hF hδpos hδ hslack).trans
    (paired_source_D_le base M bin selector Φ ψ star ι ζ hordinary hstar
      hforeign P R O G hι)

end Paper2.TwoStreamPairedCapacity

#print axioms Paper2.TwoStreamPairedCapacity.paired_source_D_le
#print axioms Paper2.TwoStreamPairedCapacity.parent_capacity
