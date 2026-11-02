import Workspace.UpperBound

/-!
# Compatible columns of fixed-Alice partial protocols

Source: Paper 2, `2026-09-22-protocol-labels-v12`, Section 2,
Definition `def:compatibility`, equation `eq:compatibility`, and the
intersection/union induction in the proof of `thm:rank-count`.

This module proves the semantic statement, not a rank or counting bound.
Trees may have unequal leaf depths; their cost is the maximum depth.
The predicate at every Bob node is a function of the column alone.
No nonemptiness hypothesis is imposed on the retained rows.
-/

namespace Paper2

open Workspace.Types.Protocol Workspace.Types.CommComplexity

/-- A binary protocol with Alice's messages and leaf outputs fixed, but
with Bob's messages unspecified. -/
inductive PartialProtocol (X : Type*) : Type _ where
  | leaf (b : Bool) : PartialProtocol X
  | alice (a : X → Bool) (l r : PartialProtocol X) : PartialProtocol X
  | bob (l r : PartialProtocol X) : PartialProtocol X

namespace PartialProtocol

universe u v
variable {X : Type u} {Y : Type v}

/-- Maximum number of messages on a root-to-leaf path. -/
def cost : PartialProtocol X → ℕ
  | leaf _ => 0
  | alice _ l r => 1 + max l.cost r.cost
  | bob l r => 1 + max l.cost r.cost

/-- A completion supplies one column-only function at each Bob node. -/
def Completion (Y : Type v) : PartialProtocol X → Type v
  | leaf _ => PUnit
  | alice _ l r => Completion Y l × Completion Y r
  | bob l r => (Y → Bool) × Completion Y l × Completion Y r

/-- A completion is realized as the existing concrete protocol datatype. -/
def complete : (P : PartialProtocol X) → P.Completion Y → Protocol X Y Bool
  | leaf b, _ => .leaf b
  | alice a l r, c => .aNode a (l.complete c.1) (r.complete c.2)
  | bob l r, c => .bNode c.1 (l.complete c.2.1) (r.complete c.2.2)

@[simp] theorem complete_cost (P : PartialProtocol X) (c : P.Completion Y) :
    (P.complete c).cost = P.cost := by
  induction P with
  | leaf b => rfl
  | alice a l r ihl ihr => simp [complete, cost, Protocol.cost, ihl, ihr]
  | bob l r ihl ihr => simp [complete, cost, Protocol.cost, ihl, ihr]

/-- The recursive intersection/union expression in the manuscript. At an
Alice node only her own decisions filter rows; a Bob node keeps all rows. -/
def compatible (F : X → Y → Bool) : PartialProtocol X → Set X → Set Y
  | leaf b, U => {y | ∀ x ∈ U, b = F x y}
  | alice a l r, U =>
      l.compatible F {x | x ∈ U ∧ a x = false} ∩
      r.compatible F {x | x ∈ U ∧ a x = true}
  | bob l r, U => l.compatible F U ∪ r.compatible F U

/-- Empty retained row groups impose no condition, including below Bob nodes. -/
@[simp] theorem compatible_empty (F : X → Y → Bool) (P : PartialProtocol X) :
    P.compatible F ∅ = Set.univ := by
  induction P with
  | leaf b => ext y; simp [compatible]
  | alice a l r ihl ihr => simpa [compatible] using congrArg₂ (· ∩ ·) ihl ihr
  | bob l r ihl ihr => simp [compatible, ihl, ihr]

/-- A single actual Bob completion correct on all retained rows implies
membership in the recursive compatible domain. -/
theorem mem_compatible_of_correct (F : X → Y → Bool) (P : PartialProtocol X)
    (c : P.Completion Y) (U : Set X) (y : Y)
    (h : ∀ x ∈ U, (P.complete c).eval x y = F x y) :
    y ∈ P.compatible F U := by
  induction P generalizing U with
  | leaf b => exact h
  | alice a l r ihl ihr =>
      constructor
      · apply ihl c.1
        intro x hx
        simpa [complete, Protocol.eval, hx.2] using h x hx.1
      · apply ihr c.2
        intro x hx
        simpa [complete, Protocol.eval, hx.2] using h x hx.1
  | bob l r ihl ihr =>
      cases hb : c.1 y with
      | false =>
          left
          apply ihl c.2.1
          intro x hx
          simpa [complete, Protocol.eval, hb] using h x hx
      | true =>
          right
          apply ihr c.2.2
          intro x hx
          simpa [complete, Protocol.eval, hb] using h x hx

/-- Canonical completion: Bob chooses left whenever left can serve the
entire current row group, and otherwise chooses right. This choice depends
on the column, never on the private row. -/
noncomputable def canonical (F : X → Y → Bool) :
    (P : PartialProtocol X) → Set X → P.Completion Y
  | leaf _, _ => PUnit.unit
  | alice a l r, U =>
      (l.canonical F {x | x ∈ U ∧ a x = false},
       r.canonical F {x | x ∈ U ∧ a x = true})
  | bob l r, U =>
      (fun y => @decide (y ∉ l.compatible F U) (Classical.propDecidable _),
       l.canonical F U, r.canonical F U)

/-- The same canonical completion works simultaneously on every compatible
column and every retained row. -/
theorem canonical_correct (F : X → Y → Bool) (P : PartialProtocol X)
    (U : Set X) (y : Y) (hy : y ∈ P.compatible F U) :
    ∀ x ∈ U, (P.complete (P.canonical F U)).eval x y = F x y := by
  induction P generalizing U with
  | leaf b => exact hy
  | alice a l r ihl ihr =>
      intro x hx
      cases ha : a x with
      | false =>
          simpa [canonical, complete, Protocol.eval, ha] using
            ihl _ hy.1 x ⟨hx, ha⟩
      | true =>
          simpa [canonical, complete, Protocol.eval, ha] using
            ihr _ hy.2 x ⟨hx, ha⟩
  | bob l r ihl ihr =>
      intro x hx
      classical
      by_cases hl : y ∈ l.compatible F U
      · simpa [canonical, complete, Protocol.eval, hl] using ihl U hl x hx
      · have hr : y ∈ r.compatible F U := hy.resolve_left hl
        simpa [canonical, complete, Protocol.eval, hl] using ihr U hr x hx

/-- Exact semantics of the recursive domain. The existential completion is
outside the universal row quantifier; Bob cannot choose separately by row. -/
theorem mem_compatible_iff (F : X → Y → Bool) (P : PartialProtocol X)
    (U : Set X) (y : Y) :
    y ∈ P.compatible F U ↔
      ∃ c : P.Completion Y, ∀ x ∈ U, (P.complete c).eval x y = F x y := by
  constructor
  · intro h
    exact ⟨P.canonical F U, P.canonical_correct F U y h⟩
  · rintro ⟨c, h⟩
    exact P.mem_compatible_of_correct F c U y h

/-- Columnwise compatibility yields one genuine protocol, not a separate
row-dependent witness for each input. -/
theorem subset_compatible_iff (F : X → Y → Bool) (P : PartialProtocol X)
    (U : Set X) (V : Set Y) :
    V ⊆ P.compatible F U ↔ ∃ c : P.Completion Y,
      ∀ y ∈ V, ∀ x ∈ U, (P.complete c).eval x y = F x y := by
  constructor
  · intro h
    exact ⟨P.canonical F U, fun y hy => P.canonical_correct F U y (h hy)⟩
  · rintro ⟨c, h⟩ y hy
    exact P.mem_compatible_of_correct F c U y (h y hy)

/-- Forget exactly the Bob message functions of a concrete protocol. -/
def forget : Protocol X Y Bool → PartialProtocol X
  | .leaf b => leaf b
  | .aNode a l r => alice a (forget l) (forget r)
  | .bNode _ l r => bob (forget l) (forget r)

@[simp] theorem forget_cost (P : Protocol X Y Bool) :
    (forget P).cost = P.cost := by
  induction P with
  | leaf b => rfl
  | aNode a l r ihl ihr => simp [forget, cost, Protocol.cost, ihl, ihr]
  | bNode b l r ihl ihr => simp [forget, cost, Protocol.cost, ihl, ihr]

/-- The discarded functions themselves give a completion of the forgotten tree. -/
def originalCompletion : (P : Protocol X Y Bool) → (forget P).Completion Y
  | .leaf _ => PUnit.unit
  | .aNode _ l r => (originalCompletion l, originalCompletion r)
  | .bNode b l r => (b, originalCompletion l, originalCompletion r)

@[simp] theorem complete_original (P : Protocol X Y Bool) :
    (forget P).complete (originalCompletion P) = P := by
  induction P with
  | leaf b => rfl
  | aNode a l r ihl ihr => simp [forget, originalCompletion, complete, ihl, ihr]
  | bNode b l r ihl ihr => simp [forget, originalCompletion, complete, ihl, ihr]

/-- An upper protocol restricts to arbitrary row and column labels at the
same cost. No injectivity is needed, so duplicate sampled labels are allowed. -/
theorem restriction_upper {A B : Type*} (F : X → Y → Bool)
    (P : Protocol X Y Bool) (hP : P.Computes F) (rows : A → X) (cols : B → Y) :
    ∃ Q : Protocol A B Bool, Q.cost = P.cost ∧
      Q.Computes (fun a b => F (rows a) (cols b)) := by
  refine ⟨Workspace.UpperBound.Protocol.comap rows cols P,
    Workspace.UpperBound.Protocol.comap_cost rows cols P, ?_⟩
  intro a b
  rw [Workspace.UpperBound.Protocol.comap_eval]
  exact hP _ _

/-- From compatibility to a protocol on the retained submatrix, preserving
the exact tree cost. -/
theorem restriction_protocol (F : X → Y → Bool) (P : PartialProtocol X)
    (U : Set X) (V : Set Y) (h : V ⊆ P.compatible F U) :
    ∃ Q : Protocol U V Bool, Q.cost = P.cost ∧
      Q.Computes (fun x y => F x.1 y.1) := by
  refine ⟨Workspace.UpperBound.Protocol.comap Subtype.val Subtype.val
      (P.complete (P.canonical F U)), ?_, ?_⟩
  · rw [Workspace.UpperBound.Protocol.comap_cost, complete_cost]
  · intro x y
    rw [Workspace.UpperBound.Protocol.comap_eval]
    exact P.canonical_correct F U y.1 (h y.2) x.1 x.2

/-- The communication lower-bound consequence used in the sampling proof. -/
theorem D_restriction_le
    (F : X → Y → Bool) (P : PartialProtocol X)
    (U : Set X) (V : Set Y) [Fintype U] [Fintype V]
    (h : V ⊆ P.compatible F U) :
    D (fun (x : U) (y : V) => F x.1 y.1) ≤ P.cost := by
  obtain ⟨Q, hcost, hcomp⟩ := P.restriction_protocol F U V h
  exact Nat.sInf_le ⟨Q, hcost, hcomp⟩

/-- Extend a protocol for a restriction to the original labelled inputs.
Outside the retained sets an arbitrary false message is used. This works
also for empty row and column sets; no default retained input is required. -/
noncomputable def extend (U : Set X) (V : Set Y) :
    Protocol U V Bool → Protocol X Y Bool
  | .leaf b => .leaf b
  | .aNode a l r =>
      .aNode (fun x => @dite Bool (x ∈ U) (Classical.propDecidable _)
        (fun hx => a ⟨x, hx⟩) (fun _ => false)) (extend U V l) (extend U V r)
  | .bNode b l r =>
      .bNode (fun y => @dite Bool (y ∈ V) (Classical.propDecidable _)
        (fun hy => b ⟨y, hy⟩) (fun _ => false)) (extend U V l) (extend U V r)

@[simp] theorem extend_cost (U : Set X) (V : Set Y) (P : Protocol U V Bool) :
    (extend U V P).cost = P.cost := by
  induction P with
  | leaf b => rfl
  | aNode a l r ihl ihr => simp [extend, Protocol.cost, ihl, ihr]
  | bNode b l r ihl ihr => simp [extend, Protocol.cost, ihl, ihr]

@[simp] theorem extend_eval (U : Set X) (V : Set Y) (P : Protocol U V Bool)
    (x : U) (y : V) : (extend U V P).eval x.1 y.1 = P.eval x y := by
  induction P with
  | leaf b => rfl
  | aNode a l r ihl ihr =>
      simp [extend, Protocol.eval, x.2, ihl, ihr]
  | bNode b l r ihl ihr =>
      simp [extend, Protocol.eval, y.2, ihl, ihr]

/-- Equation `eq:compatibility`, using trees of depth at most `t`.
Both directions use the actual existing deterministic communication
complexity. In particular the forward direction obtains an optimal
protocol from the nonempty achievable-cost set, rather than assuming one. -/
theorem D_restriction_le_iff
    (F : X → Y → Bool) (U : Set X) (V : Set Y)
    [Fintype U] [Fintype V] (t : ℕ) :
    D (fun (x : U) (y : V) => F x.1 y.1) ≤ t ↔
      ∃ P : PartialProtocol X, P.cost ≤ t ∧ V ⊆ P.compatible F U := by
  constructor
  · intro hD
    have hm := Nat.sInf_mem (Workspace.UpperBound.AchievableCosts_nonempty
      (fun (x : U) (y : V) => F x.1 y.1))
    obtain ⟨Q, hcost, hcomp⟩ := hm
    refine ⟨forget (extend U V Q), ?_, ?_⟩
    · simpa only [forget_cost, extend_cost, hcost, D] using hD
    · intro y hy
      apply mem_compatible_of_correct F _ (originalCompletion (extend U V Q)) U y
      intro x hx
      rw [complete_original]
      exact (extend_eval U V Q ⟨x, hx⟩ ⟨y, hy⟩).trans (hcomp ⟨x, hx⟩ ⟨y, hy⟩)
  · rintro ⟨P, hcost, h⟩
    exact (P.D_restriction_le F U V h).trans hcost

/-- Restriction to arbitrary labelled samples never raises communication
complexity; sampling maps are not required to be injective. -/
theorem D_reindex_le {A B : Type*} [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] (F : X → Y → Bool) (rows : A → X) (cols : B → Y) :
    D (fun a b => F (rows a) (cols b)) ≤ D F := by
  obtain ⟨P, hcost, hcomp⟩ :=
    Nat.sInf_mem (Workspace.UpperBound.AchievableCosts_nonempty F)
  obtain ⟨Q, hQcost, hQcomp⟩ := restriction_upper F P hcomp rows cols
  exact Nat.sInf_le ⟨Q, hQcost.trans hcost, hQcomp⟩

/-- Every leaf occurs at the specified depth, as in the manuscript's complete
binary trees. This is a structural predicate, not a complexity certificate. -/
def IsComplete : PartialProtocol X → ℕ → Prop
  | leaf _, 0 => True
  | alice _ l r, t + 1 => l.IsComplete t ∧ r.IsComplete t
  | bob l r, t + 1 => l.IsComplete t ∧ r.IsComplete t
  | _, _ => False

/-- Pad short branches with dummy Alice messages and unchanged leaf outputs. -/
def pad : PartialProtocol X → ℕ → PartialProtocol X
  | P, 0 => P
  | leaf b, t + 1 => alice (fun _ => false) ((leaf b).pad t) ((leaf b).pad t)
  | alice a l r, t + 1 => alice a (l.pad t) (r.pad t)
  | bob l r, t + 1 => bob (l.pad t) (r.pad t)

/-- Dummy-message padding does not change any compatible domain. -/
theorem compatible_pad (F : X → Y → Bool) (P : PartialProtocol X)
    (t : ℕ) (U : Set X) : (P.pad t).compatible F U = P.compatible F U := by
  induction t generalizing P U with
  | zero => rfl
  | succ t ih =>
      cases P with
      | leaf b => simp [pad, compatible, ih]
      | alice a l r => simp only [pad, compatible, ih]
      | bob l r => simp only [pad, compatible, ih]

theorem isComplete_pad (P : PartialProtocol X) (t : ℕ) (h : P.cost ≤ t) :
    (P.pad t).IsComplete t := by
  induction t generalizing P with
  | zero =>
      cases P with
      | leaf b => trivial
      | alice a l r => simp [cost] at h
      | bob l r => simp [cost] at h
  | succ t ih =>
      cases P with
      | leaf b => exact ⟨ih _ (Nat.zero_le _), ih _ (Nat.zero_le _)⟩
      | alice a l r =>
          have hl : l.cost ≤ t := by simp only [cost] at h; omega
          have hr : r.cost ≤ t := by simp only [cost] at h; omega
          exact ⟨ih l hl, ih r hr⟩
      | bob l r =>
          have hl : l.cost ≤ t := by simp only [cost] at h; omega
          have hr : r.cost ≤ t := by simp only [cost] at h; omega
          exact ⟨ih l hl, ih r hr⟩

theorem IsComplete.cost_eq {P : PartialProtocol X} {t : ℕ}
    (h : P.IsComplete t) : P.cost = t := by
  induction P generalizing t with
  | leaf b => cases t <;> simp_all [IsComplete, cost]
  | alice a l r ihl ihr =>
      cases t with
      | zero => exact False.elim h
      | succ t => simp [cost, ihl h.1, ihr h.2, Nat.add_comm]
  | bob l r ihl ihr =>
      cases t with
      | zero => exact False.elim h
      | succ t => simp [cost, ihl h.1, ihr h.2, Nat.add_comm]

/-- The literal complete-depth version of the manuscript's compatibility
equivalence. Short protocols are padded rather than assumed complete. -/
theorem D_restriction_le_iff_complete
    (F : X → Y → Bool) (U : Set X) (V : Set Y)
    [Fintype U] [Fintype V] (t : ℕ) :
    D (fun (x : U) (y : V) => F x.1 y.1) ≤ t ↔
      ∃ P : PartialProtocol X, P.IsComplete t ∧ V ⊆ P.compatible F U := by
  rw [D_restriction_le_iff]
  constructor
  · rintro ⟨P, hcost, h⟩
    exact ⟨P.pad t, P.isComplete_pad t hcost, by simpa [compatible_pad] using h⟩
  · rintro ⟨P, hdepth, h⟩
    exact ⟨P, hdepth.cost_eq.le, h⟩

end PartialProtocol
end Paper2
