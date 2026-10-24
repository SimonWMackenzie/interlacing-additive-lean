import Paper2.DomainCounting
import Paper2.ProtocolDomains
import Paper2.RankLeaves

/-!
# All compatible domains of bounded-depth protocols

Source: Paper 2, frozen v12, Section 2, `thm:rank-count`.
This module connects the actual fixed-Alice protocol semantics to a finite
family of complete union/intersection formulas. The quantification is over
every retained row set, including the empty set, and every partial protocol.
There is no bound or enumeration assumption on Alice's message functions.
-/

namespace Paper2

namespace CompleteFormula

/-- Pad a leaf to any complete depth using idempotent unions. -/
def constant {A : Type*} (a : A) : (t : ℕ) → CompleteFormula A t
  | 0 => a
  | t + 1 => (false, constant a t, constant a t)

@[simp] theorem eval_constant {A Y : Type*} (leaf : A → Set Y)
    (a : A) (t : ℕ) : (constant a t).eval leaf = leaf a := by
  induction t with
  | zero => rfl
  | succ t ih => simp [constant, eval, ih]

end CompleteFormula

variable {X Y : Type*}

/-- The exact family being counted, not a syntactic protocol family. -/
def compatibleDomains (F : X → Y → Bool) (t : ℕ) : Set (Set Y) :=
  {S | ∃ U : Set X, ∃ P : PartialProtocol X,
    P.cost ≤ t ∧ P.compatible F U = S}

/-- Every bounded-depth partial protocol is represented by a complete
formula of precisely that depth. The only assumption here is coverage of
actual leaf domains; all retained row sets are covered simultaneously. -/
theorem compatible_eq_formula {A : Type*} (F : X → Y → Bool)
    (leaf : A → Set Y)
    (hleaf : ∀ (U : Set X) (b : Bool),
      ∃ a : A, leaf a = {y | ∀ x ∈ U, b = F x y})
    (t : ℕ) (P : PartialProtocol X) (U : Set X) (hcost : P.cost ≤ t) :
    ∃ q : CompleteFormula A t, q.eval leaf = P.compatible F U := by
  induction t generalizing P U with
  | zero =>
      cases P with
      | leaf b => exact hleaf U b
      | alice a l r => simp [PartialProtocol.cost] at hcost
      | bob l r => simp [PartialProtocol.cost] at hcost
  | succ t ih =>
      cases P with
      | leaf b =>
          obtain ⟨a, ha⟩ := hleaf U b
          exact ⟨CompleteFormula.constant a (t + 1), by simpa using ha⟩
      | alice a l r =>
          have hl : l.cost ≤ t := by
            have : l.cost ≤ max l.cost r.cost := le_max_left _ _
            simp only [PartialProtocol.cost] at hcost
            omega
          have hr : r.cost ≤ t := by
            have : r.cost ≤ max l.cost r.cost := le_max_right _ _
            simp only [PartialProtocol.cost] at hcost
            omega
          obtain ⟨p, hp⟩ := ih l {x | x ∈ U ∧ a x = false} hl
          obtain ⟨q, hq⟩ := ih r {x | x ∈ U ∧ a x = true} hr
          exact ⟨(true, p, q), by simp [CompleteFormula.eval,
            PartialProtocol.compatible, hp, hq]⟩
      | bob l r =>
          have hl : l.cost ≤ t := by
            have : l.cost ≤ max l.cost r.cost := le_max_left _ _
            simp only [PartialProtocol.cost] at hcost
            omega
          have hr : r.cost ≤ t := by
            have : r.cost ≤ max l.cost r.cost := le_max_right _ _
            simp only [PartialProtocol.cost] at hcost
            omega
          obtain ⟨p, hp⟩ := ih l U hl
          obtain ⟨q, hq⟩ := ih r U hr
          exact ⟨(false, p, q), by simp [CompleteFormula.eval,
            PartialProtocol.compatible, hp, hq]⟩

theorem compatibleDomains_subset_formula_domains {A : Type*}
    (F : X → Y → Bool) (leaf : A → Set Y)
    (hleaf : ∀ (U : Set X) (b : Bool),
      ∃ a : A, leaf a = {y | ∀ x ∈ U, b = F x y}) (t : ℕ) :
    compatibleDomains F t ⊆ Set.range (CompleteFormula.eval leaf (t := t)) := by
  rintro S ⟨U, P, hcost, rfl⟩
  exact compatible_eq_formula F leaf hleaf t P U hcost

/-- A finite leaf catalogue gives a finite catalogue for every bounded
protocol, without requiring the type of all protocols to be finite. -/
theorem compatibleDomains_finite_of_leaf_catalogue {A : Type*} [Fintype A]
    (F : X → Y → Bool) (leaf : A → Set Y)
    (hleaf : ∀ (U : Set X) (b : Bool),
      ∃ a : A, leaf a = {y | ∀ x ∈ U, b = F x y}) (t : ℕ) :
    (compatibleDomains F t).Finite :=
  (Set.finite_range (CompleteFormula.eval leaf (t := t))).subset
    (compatibleDomains_subset_formula_domains F leaf hleaf t)

/-- Cardinal bound conditional on the separately proved leaf-domain bound.
The protocol-to-formula coverage is proved, not assumed. -/
theorem compatibleDomains_card_le_of_leaf_catalogue {A : Type*} [Fintype A]
    (F : X → Y → Bool) (leaf : A → Set Y)
    (hleaf : ∀ (U : Set X) (b : Bool),
      ∃ a : A, leaf a = {y | ∀ x ∈ U, b = F x y})
    (r t : ℕ) (hcard : Fintype.card A ≤ 2 ^ (r * (r + 1) + 1)) :
    (compatibleDomains F t).ncard ≤
      2 ^ ((r * (r + 1) + 2) * 2 ^ t - 1) := by
  exact (Set.ncard_le_ncard
    (compatibleDomains_subset_formula_domains F leaf hleaf t)
    (Set.finite_range _)).trans (manuscript_formula_bound leaf r t hcard)

/-- The finite leaf alphabet includes the constraints from every retained
row set. Equality of repeated rows or columns is not assumed. -/
theorem leaf_catalogue_covers [Fintype X] [Fintype Y]
    (F : X → Y → Bool) (U : Set X) (b : Bool) :
    ∃ a : ↥(RankLeaves.leafDomains F),
      (↑a.val : Set Y) = {y | ∀ x ∈ U, b = F x y} := by
  classical
  refine ⟨⟨RankLeaves.leafDomain F U.toFinset b, ?_⟩, ?_⟩
  · exact Finset.mem_image.mpr ⟨(U.toFinset, b), Finset.mem_univ _, rfl⟩
  · ext y
    simp [RankLeaves.mem_leafDomain, eq_comm]

theorem compatibleDomains_finite [Fintype Y] (F : X → Y → Bool) (t : ℕ) :
    (compatibleDomains F t).Finite := Set.toFinite _

/-- The complete statement of v12 `thm:rank-count`: a real rank bound
controls all compatible domains, simultaneously over all retained row
sets and all bounded-depth partial protocols. Rank zero and depth zero
are included. The input types may have arbitrarily many duplicate labels. -/
theorem compatibleDomains_card_le [Fintype X] [Fintype Y]
    (F : X → Y → Bool) (r t : ℕ)
    (hrank : (RankLeaves.realMatrix F).rank ≤ r) :
    (compatibleDomains F t).ncard ≤
      2 ^ ((r * (r + 1) + 2) * 2 ^ t - 1) := by
  classical
  apply compatibleDomains_card_le_of_leaf_catalogue F
    (fun a : ↥(RankLeaves.leafDomains F) => (↑a.val : Set Y))
    (leaf_catalogue_covers F) r t
  simpa only [Fintype.card_coe] using RankLeaves.leafDomains_card_le F r hrank

/-- An explicit finite-family interface for probability arguments. The
catalogue is exactly the family just bounded; membership is not merely
an assumed completeness certificate. -/
theorem exists_compatible_catalogue [Fintype X] [Fintype Y]
    (F : X → Y → Bool) (r t : ℕ)
    (hrank : (RankLeaves.realMatrix F).rank ≤ r) :
    ∃ C : Finset (Set Y),
      C.card ≤ 2 ^ ((r * (r + 1) + 2) * 2 ^ t - 1) ∧
      (∀ S : Set Y, S ∈ C ↔ ∃ U : Set X, ∃ P : PartialProtocol X,
        P.cost ≤ t ∧ P.compatible F U = S) := by
  classical
  refine ⟨(compatibleDomains_finite F t).toFinset, ?_, ?_⟩
  · rw [← Set.ncard_eq_toFinset_card]
    exact compatibleDomains_card_le F r t hrank
  · intro S
    simp only [Set.Finite.mem_toFinset, compatibleDomains, Set.mem_setOf_eq]

/-- A convenient containment form of the same verified catalogue. -/
theorem exists_compatible_cover [Fintype X] [Fintype Y]
    (F : X → Y → Bool) (r t : ℕ)
    (hrank : (RankLeaves.realMatrix F).rank ≤ r) :
    ∃ C : Finset (Set Y),
      C.card ≤ 2 ^ ((r * (r + 1) + 2) * 2 ^ t - 1) ∧
      ∀ (U : Set X) (P : PartialProtocol X),
        P.cost ≤ t → P.compatible F U ∈ C := by
  obtain ⟨C, hcard, hC⟩ := exists_compatible_catalogue F r t hrank
  exact ⟨C, hcard, fun U P hP => (hC _).mpr ⟨U, P, hP, rfl⟩⟩

end Paper2

#print axioms Paper2.compatible_eq_formula
#print axioms Paper2.compatibleDomains_card_le
#print axioms Paper2.exists_compatible_catalogue
