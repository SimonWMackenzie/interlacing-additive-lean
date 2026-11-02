import EthInapproximability.CurrentPaper.JointTransfer

/-!
# Actual tuple sections of a finite quotient-pair support

Source: v8 `A-stage4-details.tex`, `lem:paper-template-transfer`, specifically
the fixed completion of one surviving physical pair per quotient pair. Every
tuple here is obtained from that same completion into the original support.
No product of independently selected marginals is used.

This module supplies finite support geometry, not a communication lower bound
or a protocol routing theorem. Empty supports need no arbitrary inhabitant.
-/

noncomputable section
open scoped Classical

namespace EthInapproximability.CurrentPaper.TerminalPhysicalPairs

open JointTransfer

variable {C : Type*} {Q L : ℕ}

/-- The quotient of the actual surviving pairs. -/
def quotientPairs (P : Finset (C × C)) (f : C → Fin L) :
    Finset (Fin L × Fin L) :=
  P.image (fun p => (f p.1, f p.2))

/-- Choose one actual pair for each quotient pair, then use the fixed completion. -/
def pairCompletion (P : Finset (C × C)) (f : C → Fin L)
    (sigma : C × C → Fin Q → C) (k : {k // k ∈ quotientPairs P f}) :
    Fin Q → C :=
  sigma (selectedRowSection P (fun p => (f p.1, f p.2)) k)

/-- One completed original tuple per quotient pair. -/
def support (P : Finset (C × C)) (f : C → Fin L)
    (sigma : C × C → Fin Q → C) : Finset (Fin Q → C) :=
  (quotientPairs P f).attach.image (pairCompletion P f sigma)

theorem pairCompletion_mem (P : Finset (C × C)) (f : C → Fin L)
    (sigma : C × C → Fin Q → C) (S : Finset (Fin Q → C))
    (hsigma : ∀ p ∈ P, sigma p ∈ S) (k : {k // k ∈ quotientPairs P f}) :
    pairCompletion P f sigma k ∈ S :=
  hsigma _ (selectedRowSection_mem _ _ k)

theorem pairCompletion_quotient (P : Finset (C × C)) (f : C → Fin L)
    (sigma : C × C → Fin Q → C) (i j : Fin Q)
    (hsigma : ∀ p ∈ P, sigma p i = p.1 ∧ sigma p j = p.2)
    (k : {k // k ∈ quotientPairs P f}) :
    (f (pairCompletion P f sigma k i), f (pairCompletion P f sigma k j)) = k.val := by
  have h := hsigma _ (selectedRowSection_mem P (fun p => (f p.1, f p.2)) k)
  simp only [pairCompletion, h.1, h.2]
  exact selectedRowSection_apply P (fun p => (f p.1, f p.2)) k

theorem pairCompletion_injective (P : Finset (C × C)) (f : C → Fin L)
    (sigma : C × C → Fin Q → C) (i j : Fin Q)
    (hsigma : ∀ p ∈ P, sigma p i = p.1 ∧ sigma p j = p.2) :
    Function.Injective (pairCompletion P f sigma) := by
  intro k k' heq
  apply Subtype.ext
  exact (pairCompletion_quotient P f sigma i j hsigma k).symm.trans
    ((congrArg (fun z => (f (z i), f (z j))) heq).trans
      (pairCompletion_quotient P f sigma i j hsigma k'))

theorem support_subset (P : Finset (C × C)) (f : C → Fin L)
    (sigma : C × C → Fin Q → C) (S : Finset (Fin Q → C))
    (hsigma : ∀ p ∈ P, sigma p ∈ S) : support P f sigma ⊆ S := by
  intro z hz
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hz
  exact pairCompletion_mem P f sigma S hsigma k

theorem support_card (P : Finset (C × C)) (f : C → Fin L)
    (sigma : C × C → Fin Q → C) (i j : Fin Q)
    (hsigma : ∀ p ∈ P, sigma p i = p.1 ∧ sigma p j = p.2) :
    (support P f sigma).card = (quotientPairs P f).card := by
  rw [support, Finset.card_image_of_injective _
    (pairCompletion_injective P f sigma i j hsigma), Finset.card_attach]

/-- Every selected tuple has the physical coordinates of one pair in `P`. -/
theorem support_coordinates (P : Finset (C × C)) (f : C → Fin L)
    (sigma : C × C → Fin Q → C) (i j : Fin Q)
    (hsigma : ∀ p ∈ P, sigma p i = p.1 ∧ sigma p j = p.2)
    {z : Fin Q → C} (hz : z ∈ support P f sigma) : (z i, z j) ∈ P := by
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hz
  have hm := selectedRowSection_mem P (fun p => (f p.1, f p.2)) k
  have hc := hsigma _ hm
  simpa only [pairCompletion, hc.1, hc.2, Prod.mk.eta] using hm

theorem support_coordinates_mem (P : Finset (C × C)) (f : C → Fin L)
    (sigma : C × C → Fin Q → C) (i j : Fin Q)
    (hsigma : ∀ p ∈ P, sigma p i = p.1 ∧ sigma p j = p.2)
    (A B : Finset C) (hP : P ⊆ A ×ˢ B)
    {z : Fin Q → C} (hz : z ∈ support P f sigma) : z i ∈ A ∧ z j ∈ B :=
  Finset.mem_product.mp (hP (support_coordinates P f sigma i j hsigma hz))

theorem quotient_injOn_support (P : Finset (C × C)) (f : C → Fin L)
    (sigma : C × C → Fin Q → C) (i j : Fin Q)
    (hsigma : ∀ p ∈ P, sigma p i = p.1 ∧ sigma p j = p.2) :
    Set.InjOn (fun z : Fin Q → C => (f (z i), f (z j))) ↑(support P f sigma) := by
  intro z hz z' hz' heq
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨k', _, rfl⟩ := Finset.mem_image.mp hz'
  have hk : k = k' := Subtype.ext
    ((pairCompletion_quotient P f sigma i j hsigma k).symm.trans
      (heq.trans (pairCompletion_quotient P f sigma i j hsigma k')))
  exact congrArg (pairCompletion P f sigma) hk

theorem support_quotient_image (P : Finset (C × C)) (f : C → Fin L)
    (sigma : C × C → Fin Q → C) (i j : Fin Q)
    (hsigma : ∀ p ∈ P, sigma p i = p.1 ∧ sigma p j = p.2) :
    (support P f sigma).image (fun z => (f (z i), f (z j))) = quotientPairs P f := by
  ext k
  constructor
  · intro hk
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨k', _, rfl⟩ := Finset.mem_image.mp hz
    rw [pairCompletion_quotient P f sigma i j hsigma k']
    exact k'.property
  · intro hk
    refine Finset.mem_image.mpr ⟨pairCompletion P f sigma ⟨k, hk⟩, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨⟨k, hk⟩, Finset.mem_attach _ _, rfl⟩
    · exact pairCompletion_quotient P f sigma i j hsigma ⟨k, hk⟩

theorem support_first_image (P : Finset (C × C)) (f : C → Fin L)
    (sigma : C × C → Fin Q → C) (i j : Fin Q)
    (hsigma : ∀ p ∈ P, sigma p i = p.1 ∧ sigma p j = p.2) :
    (support P f sigma).image (fun z => f (z i)) =
      (quotientPairs P f).image Prod.fst := by
  rw [← support_quotient_image P f sigma i j hsigma]
  simp only [Finset.image_image, Function.comp_def]

/-- A first-coordinate value has at most `L` possible second values. -/
theorem quotientPairs_card_le_first_image (P : Finset (C × C)) (f : C → Fin L)
    (sigma : C × C → Fin Q → C) (i j : Fin Q)
    (hsigma : ∀ p ∈ P, sigma p i = p.1 ∧ sigma p j = p.2) :
    (quotientPairs P f).card ≤
      L * ((support P f sigma).image (fun z => f (z i))).card := by
  have hsub : quotientPairs P f ⊆
      ((quotientPairs P f).image Prod.fst) ×ˢ (Finset.univ : Finset (Fin L)) := by
    intro k hk
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨k, hk, rfl⟩,
      Finset.mem_univ _⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin,
    ← support_first_image P f sigma i j hsigma, Nat.mul_comm] at hc
  exact hc

end EthInapproximability.CurrentPaper.TerminalPhysicalPairs
