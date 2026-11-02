import Paper2.PairedSelectorMatrix

/-!
# An attached pair at a capacity-one parent

Frozen v12 Section 5, `res:paired`, the last capacity-one case. The two
supports use the same original coordinate but different selector tags.
Thus they are distinct product coordinates even when their word labels
coincide. The two-copy estimate applies at the parent, before any row query.
-/

namespace Paper2.PairedSelectorCapacityPair

open PairedSelectorMatrix
open Workspace.Types.CommComplexity Workspace.Types.Protocol

variable {W J : Type*} [Fintype W] [Fintype J] {q : ℕ}

/-- The ordinary and foreign coordinates remain differently tagged. -/
def pairBlock (α : Fin q) : Fin 2 → Block q :=
  Fin.cases (false, α) (fun _ => (true, α))

theorem pairBlock_injective (α : Fin q) : Function.Injective (pairBlock α) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · have hf : false = true := congrArg Prod.fst hij
    cases hf
  · have hf : true = false := congrArg Prod.fst hij
    cases hf
  · rfl

/-- Both original word supports, without identifying labels across tags. -/
def pairSupport (ordinary foreign : Set W) : Set (Fin 2 × W) :=
  fun a => Fin.cases (fun w => w ∈ ordinary) (fun _ w => w ∈ foreign) a.1 a.2

/-- An actual ordinary/foreign pair needs one more bit than the base
profile. The common selector set is kept joint throughout the projection. -/
theorem paired_parent_lower
    (μ : PositiveRationalLaw W) (ν : PositiveRationalLaw J)
    (R : W → J → Bool) (H : ℕ) {x : ℝ}
    (hH : 2 ≤ H) (hx : 0 < x) (hscale : 2 * x ≤ 1)
    (hprofile : RestrictionProfile R μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (α : Fin q) (A : Set (Selector q J)) (ordinary foreign : Set W)
    (C : Set (Column q W))
    (hordinary : ∀ w ∈ ordinary, ((false, α), w) ∈ C)
    (hforeign : ∀ w ∈ foreign, ((true, α), w) ∈ C)
    (hO : 2 * x ≤ μ.toFiniteLaw.prob (· ∈ ordinary))
    (hF : 2 * x ≤ μ.toFiniteLaw.prob (· ∈ foreign))
    (hA : (49 / 64 : ℝ) ≤ (selectorLaw ν q).toFiniteLaw.prob (· ∈ A)) :
    H + 1 ≤ Compression.restrictionD (matrix R) A C := by
  classical
  apply selected_capacity_two μ ν R H hH hx hscale hprofile
    (pairBlock α) (pairBlock_injective α) A (pairSupport ordinary foreign)
    Finset.univ (by simp) C
  · intro a ha
    rcases a with ⟨i, w⟩
    fin_cases i
    · apply hordinary w
      simpa only [pairSupport, Fin.cases_zero] using ha
    · apply hforeign w
      simpa [pairSupport] using ha
  · intro i _
    fin_cases i
    · simpa [pairSupport] using hO
    · simpa [pairSupport] using hF
  · linarith

/-- The lower bound is paid by the original parent protocol. No hypothesis
on its first speaker or on any selected query fibre is needed. -/
theorem paired_parent_cost
    (μ : PositiveRationalLaw W) (ν : PositiveRationalLaw J)
    (R : W → J → Bool) (H : ℕ) {x : ℝ}
    (hH : 2 ≤ H) (hx : 0 < x) (hscale : 2 * x ≤ 1)
    (hprofile : RestrictionProfile R μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (α : Fin q) (A : Set (Selector q J)) (ordinary foreign : Set W)
    (C : Set (Column q W))
    (hordinary : ∀ w ∈ ordinary, ((false, α), w) ∈ C)
    (hforeign : ∀ w ∈ foreign, ((true, α), w) ∈ C)
    (hO : 2 * x ≤ μ.toFiniteLaw.prob (· ∈ ordinary))
    (hF : 2 * x ≤ μ.toFiniteLaw.prob (· ∈ foreign))
    (hA : (49 / 64 : ℝ) ≤ (selectorLaw ν q).toFiniteLaw.prob (· ∈ A))
    (P : Protocol A C Bool)
    (hP : P.Computes (fun a c => matrix R a.val c.val)) : H + 1 ≤ P.cost := by
  classical
  have hl := paired_parent_lower μ ν R H hH hx hscale hprofile α A
    ordinary foreign C hordinary hforeign hO hF hA
  have hu : D (fun (a : A) (c : C) => matrix R a.val c.val) ≤ P.cost :=
    Nat.sInf_le ⟨P, rfl, hP⟩
  exact hl.trans hu

/-- Two differently tagged supported blocks contradict an `H`-bit parent. -/
theorem paired_parent_contradiction
    (μ : PositiveRationalLaw W) (ν : PositiveRationalLaw J)
    (R : W → J → Bool) (H : ℕ) {x : ℝ}
    (hH : 2 ≤ H) (hx : 0 < x) (hscale : 2 * x ≤ 1)
    (hprofile : RestrictionProfile R μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (α : Fin q) (A : Set (Selector q J)) (ordinary foreign : Set W)
    (C : Set (Column q W))
    (hordinary : ∀ w ∈ ordinary, ((false, α), w) ∈ C)
    (hforeign : ∀ w ∈ foreign, ((true, α), w) ∈ C)
    (hO : 2 * x ≤ μ.toFiniteLaw.prob (· ∈ ordinary))
    (hF : 2 * x ≤ μ.toFiniteLaw.prob (· ∈ foreign))
    (hA : (49 / 64 : ℝ) ≤ (selectorLaw ν q).toFiniteLaw.prob (· ∈ A))
    (P : Protocol A C Bool)
    (hP : P.Computes (fun a c => matrix R a.val c.val))
    (hcost : P.cost ≤ H) : False := by
  have hl := paired_parent_cost μ ν R H hH hx hscale hprofile α A
    ordinary foreign C hordinary hforeign hO hF hA P hP
  omega

end Paper2.PairedSelectorCapacityPair

#print axioms Paper2.PairedSelectorCapacityPair.pairBlock_injective
#print axioms Paper2.PairedSelectorCapacityPair.paired_parent_lower
#print axioms Paper2.PairedSelectorCapacityPair.paired_parent_cost
#print axioms Paper2.PairedSelectorCapacityPair.paired_parent_contradiction
