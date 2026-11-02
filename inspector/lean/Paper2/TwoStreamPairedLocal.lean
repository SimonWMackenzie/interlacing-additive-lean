import Paper2.TwoStreamPairedCapacity

/-!
# Local paired-row hypotheses for the capacity-one parent

The original paired-capacity adapter states its entry identities on all
ambient paired labels. Restricting the paired carrier to the retained set
allows the same checked theorem to be used when the identities are known
only on surviving original paired rows. No probability law is changed.
Frozen v12 Section 5, `res:two-stream`, lines 134--201.
-/

namespace Paper2.TwoStreamPairedLocal

open Paper2.PairedSelectorMatrix Paper2.PairedSelectorPopulation
open Workspace.Types.CommComplexity

variable {W J Rw Ω F E : Type*} [Fintype W] [Fintype J]
  [Fintype Rw] [Fintype Ω] [Fintype F] [Fintype E]
  {q s : ℕ} [NeZero q]

/-- The T17 restriction lift needs the two paired-row identities only on
the retained paired event `P`. Other foreign entries remain arbitrary. -/
theorem paired_source_D_le
    (base : W → J → Bool) (M : Rw → (Ω ⊕ F) → Bool)
    (bin : Rw → Fin s) (selector : Rw → Fin q → J)
    (Φ : Ω → Fin s → Fin q × W) (ψ : F → Fin q × W)
    (star : Fin s) (ι : E → Rw) (ζ : E → Selector q J)
    (hordinary : ∀ r c,
      M r (.inl c) = base (Φ c (bin r)).2
        (selector r (Φ c (bin r)).1))
    (P : Set E) (R : Set Rw) (O : Set Ω) (G : Set F)
    (hstar : ∀ a ∈ P, bin (ι a) = star ∧ selector (ι a) = (ζ a).1)
    (hforeign : ∀ a ∈ P, ∀ f,
      M (ι a) (.inr f) = base (ψ f).2 ((ζ a).2 (ψ f).1))
    (hι : ∀ a ∈ P, ι a ∈ R) :
    Compression.restrictionD (matrix base) (ζ '' P)
        (columns ((fun c => Φ c star) '' O) (ψ '' G)) ≤
      Compression.restrictionD M R ((Sum.inl '' O) ∪ (Sum.inr '' G)) := by
  classical
  let ι' : P → Rw := fun a => ι a.val
  let ζ' : P → Selector q J := fun a => ζ a.val
  have himage : ζ' '' Set.univ = ζ '' P := by
    ext z
    constructor
    · rintro ⟨a, -, rfl⟩
      exact ⟨a.val, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, Set.mem_univ _, rfl⟩
  have h := TwoStreamPairedCapacity.paired_source_D_le
    base M bin selector Φ ψ star ι' ζ' hordinary
    (fun a => hstar a.val a.property)
    (fun a f => hforeign a.val a.property f)
    Set.univ R O G (fun a _ => hι a.val a.property)
  simpa only [himage] using h

/-- The checked T17 capacity-one contradiction with paired-row entry
rules stated only on the retained event. -/
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
    (P : Set E) (R : Set Rw) (O : Set Ω) (G : Set F)
    (hstar : ∀ a ∈ P, bin (ι a) = star ∧ selector (ι a) = (ζ a).1)
    (hforeign : ∀ a ∈ P, ∀ f,
      M (ι a) (.inr f) = base (ψ f).2 ((ζ a).2 (ψ f).1))
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
  classical
  let ι' : P → Rw := fun a => ι a.val
  let ζ' : P → Selector q J := fun a => ζ a.val
  have himage : ζ' '' Set.univ = ζ '' P := by
    ext z
    constructor
    · rintro ⟨a, -, rfl⟩
      exact ⟨a.val, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, Set.mem_univ _, rfl⟩
  have hA' : (49 / 64 : ℝ) ≤
      (selectorLaw ν q).toFiniteLaw.prob (· ∈ ζ' '' Set.univ) := by
    simpa only [himage] using hA
  exact TwoStreamPairedCapacity.parent_capacity μ ν base M
    H ell hH hq x hx hprofile bin selector Φ ψ star ι' ζ'
    hordinary (fun a => hstar a.val a.property)
    (fun a f => hforeign a.val a.property f)
    Set.univ R O G (fun a _ => hι a.val a.property)
    ε δ hA' hO hF hδpos hδ hslack

end Paper2.TwoStreamPairedLocal

#print axioms Paper2.TwoStreamPairedLocal.paired_source_D_le
#print axioms Paper2.TwoStreamPairedLocal.parent_capacity
