import Paper2.SourceSupportFrontierTree
import Workspace.Types.Protocol

/-!
# Actual Alice-prefix paths for the reference-copy restoration

Frozen Paper 2 v12, Section 5, `res:destinations`, lines 250--310.
This file supplies protocol structure only. Certificate-bearing early leaves
must be excluded separately from the reference profile; padding does not do so.
-/

namespace Paper2.ReferencePrefix

open Workspace.Types.Protocol Paper2.SourceSupportFrontier
open scoped BigOperators

variable {X Y : Type*}

/-- Pad leaves encountered during the first `r` Alice queries by dummy Alice
queries. A Bob node and its subtree are left unchanged. -/
def padAlicePrefix : ℕ → Protocol X Y Bool → Protocol X Y Bool
  | 0, P => P
  | r + 1, .leaf z =>
      .aNode (fun _ => false) (padAlicePrefix r (.leaf z))
        (padAlicePrefix r (.leaf z))
  | r + 1, .aNode q left right =>
      .aNode q (padAlicePrefix r left) (padAlicePrefix r right)
  | _ + 1, .bNode q left right => .bNode q left right

theorem padAlicePrefix_eval (r : ℕ) (P : Protocol X Y Bool) (x : X) (y : Y) :
    (padAlicePrefix r P).eval x y = P.eval x y := by
  induction r generalizing P with
  | zero => rfl
  | succ r ih =>
      cases P with
      | leaf z => simp [padAlicePrefix, Protocol.eval, ih]
      | aNode q left right =>
          simp only [padAlicePrefix, Protocol.eval]
          split <;> simp [ih]
      | bNode q left right => rfl

theorem padAlicePrefix_cost_le (r : ℕ) (P : Protocol X Y Bool) :
    (padAlicePrefix r P).cost ≤ max P.cost r := by
  induction r generalizing P with
  | zero => simp [padAlicePrefix]
  | succ r ih =>
      cases P with
      | leaf z =>
          simp only [padAlicePrefix, Protocol.cost]
          have h := ih (Protocol.leaf z)
          simp only [Protocol.cost, Nat.zero_max] at h
          omega
      | aNode q left right =>
          simp only [padAlicePrefix, Protocol.cost]
          have hl := ih left
          have hr := ih right
          omega
      | bNode q left right =>
          simp [padAlicePrefix]

/-- No leaf occurs strictly before `r` along the Alice-only prefix. Bob
nodes terminate that prefix and need not satisfy any subtree condition. -/
def NoEarlyLeaf : ℕ → Protocol X Y Bool → Prop
  | 0, _ => True
  | _ + 1, .leaf _ => False
  | r + 1, .aNode _ left right => NoEarlyLeaf r left ∧ NoEarlyLeaf r right
  | _ + 1, .bNode _ _ _ => True

theorem padAlicePrefix_noEarlyLeaf (r : ℕ) (P : Protocol X Y Bool) :
    NoEarlyLeaf r (padAlicePrefix r P) := by
  induction r generalizing P with
  | zero => trivial
  | succ r ih =>
      cases P with
      | leaf z => exact ⟨ih (.leaf z), ih (.leaf z)⟩
      | aNode q left right => exact ⟨ih left, ih right⟩
      | bNode q left right => trivial

/-- Stop before the first Bob query or at Alice depth `r`. A tree leaf is
a physical position; both branches remain present, including empty ones. -/
def runPrefix : (r : ℕ) → Protocol X Y Bool →
    SourceSupportFrontier.Tree (Protocol X Y Bool)
  | 0, P => .stop P
  | r + 1, .aNode _ left right =>
      .fork 0 (runPrefix r left) (runPrefix r right)
  | _ + 1, P => .stop P

/-- The row's unique syntactic stopping position. The Bob input is irrelevant
until the stop because the traversed prefix consists entirely of Alice nodes. -/
def destination : (r : ℕ) → (P : Protocol X Y Bool) → (x : X) →
    (runPrefix r P).Leaves
  | 0, _, _ => ()
  | r + 1, .aNode q left right, x =>
      if q x then .inr (destination r right x)
        else .inl (destination r left x)
  | _ + 1, .leaf _, _ => ()
  | _ + 1, .bNode _ _ _, _ => ()

/-- The exact sequence of Alice answers until the first Bob query or the
depth cap. -/
def rowRoute : ℕ → Protocol X Y Bool → X → List Bool
  | 0, _, _ => []
  | r + 1, .aNode q left right, x =>
      if q x then true :: rowRoute r right x
        else false :: rowRoute r left x
  | _ + 1, _, _ => []

/-- A row actually follows each Alice query on a proposed prefix. A stopped
route may end at any protocol node; it need not continue to a leaf. -/
def Follows : Protocol X Y Bool → X → List Bool → Prop
  | _, _, [] => True
  | .aNode q left _, x, false :: route =>
      q x = false ∧ Follows left x route
  | .aNode q _ right, x, true :: route =>
      q x = true ∧ Follows right x route
  | _, _, _ :: _ => False

/-- Among all physical stopping positions, exactly one is followed by a
given row. In particular, empty and dummy branches do not create owners. -/
theorem follows_iff_destination (r : ℕ) (P : Protocol X Y Bool) (x : X)
    (v : (runPrefix r P).Leaves) :
    Follows P x ((runPrefix r P).route v) ↔ v = destination r P x := by
  induction r generalizing P with
  | zero =>
      cases v
      simp [runPrefix, Follows, destination]
  | succ r ih =>
      cases P with
      | leaf z =>
          cases v
          simp [runPrefix, Follows, destination]
      | bNode q left right =>
          cases v
          simp [runPrefix, Follows, destination]
      | aNode q left right =>
          cases v with
          | inl v =>
              by_cases hq : q x = true
              · simp [runPrefix, Follows, destination, hq]
              · have hf : q x = false := Bool.eq_false_iff.mpr hq
                simp [runPrefix, Follows, destination, hf, ih]
                exact ⟨congrArg Sum.inl, Sum.inl.inj⟩
          | inr v =>
              by_cases hq : q x = true
              · simp [runPrefix, Follows, destination, hq, ih]
                exact ⟨congrArg Sum.inr, Sum.inr.inj⟩
              · have hf : q x = false := Bool.eq_false_iff.mpr hq
                simp [runPrefix, Follows, destination, hf]

theorem destination_route (r : ℕ) (P : Protocol X Y Bool) (x : X) :
    (runPrefix r P).route (destination r P x) = rowRoute r P x := by
  induction r generalizing P with
  | zero => rfl
  | succ r ih =>
      cases P with
      | leaf z => rfl
      | bNode q left right => rfl
      | aNode q left right =>
          by_cases hq : q x = true
          · simp only [runPrefix, destination, rowRoute, hq, if_true,
              Tree.route_fork_inr, List.cons.injEq, true_and]
            exact ih right
          · have hf : q x = false := Bool.eq_false_iff.mpr hq
            simp only [runPrefix, destination, rowRoute, hf,
              Bool.false_eq_true, if_false, Tree.route_fork_inl,
              List.cons.injEq, true_and]
            exact ih left

/-- At a row-determined stop the remaining subtree computes exactly the
same output as the original protocol on that row and every Bob input. -/
theorem destination_eval (r : ℕ) (P : Protocol X Y Bool) (x : X) (y : Y) :
    ((runPrefix r P).state (destination r P x)).eval x y = P.eval x y := by
  induction r generalizing P with
  | zero => rfl
  | succ r ih =>
      cases P with
      | leaf z => rfl
      | bNode q left right => rfl
      | aNode q left right =>
          by_cases hq : q x = true
          · simp only [runPrefix, destination, hq, if_true,
              Tree.state_fork_inr, Protocol.eval]
            exact ih right
          · have hf : q x = false := Bool.eq_false_iff.mpr hq
            simp only [runPrefix, destination, hf, Bool.false_eq_true,
              if_false, Tree.state_fork_inl, Protocol.eval]
            exact ih left

/-- Every physical stopping subtree is value-correct on the rows that
actually follow its route. -/
theorem runPrefix_eval_of_follows (r : ℕ) (P : Protocol X Y Bool)
    (v : (runPrefix r P).Leaves) (x : X) (y : Y)
    (h : Follows P x ((runPrefix r P).route v)) :
    ((runPrefix r P).state v).eval x y = P.eval x y := by
  have hv := (follows_iff_destination r P x v).mp h
  subst v
  exact destination_eval r P x y

/-- The exact remaining budget at every physical stopping position. -/
theorem runPrefix_cost_add_length (r : ℕ) (P : Protocol X Y Bool)
    (v : (runPrefix r P).Leaves) :
    ((runPrefix r P).state v).cost + ((runPrefix r P).route v).length ≤ P.cost := by
  induction r generalizing P with
  | zero => simp [runPrefix]
  | succ r ih =>
      cases P with
      | leaf z => simp [runPrefix]
      | bNode q left right => simp [runPrefix]
      | aNode q left right =>
          cases v with
          | inl v =>
              have h := ih left v
              simp only [runPrefix, Tree.state_fork_inl, Tree.route_fork_inl,
                List.length_cons, Protocol.cost]
              omega
          | inr v =>
              have h := ih right v
              simp only [runPrefix, Tree.state_fork_inr, Tree.route_fork_inr,
                List.length_cons, Protocol.cost]
              omega

theorem runPrefix_depth_le (r : ℕ) (P : Protocol X Y Bool)
    (v : (runPrefix r P).Leaves) : ((runPrefix r P).route v).length ≤ r := by
  induction r generalizing P with
  | zero => simp [runPrefix]
  | succ r ih =>
      cases P with
      | leaf z => simp [runPrefix]
      | bNode q left right => simp [runPrefix]
      | aNode q left right =>
          cases v with
          | inl v => simpa [runPrefix, Tree.route] using Nat.succ_le_succ (ih left v)
          | inr v => simpa [runPrefix, Tree.route] using Nat.succ_le_succ (ih right v)

/-- Every early stop of a padded Alice prefix is an actual Bob node. -/
theorem runPrefix_stop_or_depth (r : ℕ) (P : Protocol X Y Bool)
    (h : NoEarlyLeaf r P) (v : (runPrefix r P).Leaves) :
    ((runPrefix r P).route v).length = r ∨
      ∃ q left right, (runPrefix r P).state v = Protocol.bNode q left right := by
  induction r generalizing P with
  | zero => exact Or.inl rfl
  | succ r ih =>
      cases P with
      | leaf z => exact False.elim h
      | bNode q left right => exact Or.inr ⟨q, left, right, rfl⟩
      | aNode q left right =>
          cases v with
          | inl v =>
              rcases ih left h.1 v with hd | ⟨b, l, rr, hb⟩
              · exact Or.inl (by simpa [runPrefix, Tree.route] using congrArg Nat.succ hd)
              · exact Or.inr ⟨b, l, rr, by simpa [runPrefix, Tree.state] using hb⟩
          | inr v =>
              rcases ih right h.2 v with hd | ⟨b, l, rr, hb⟩
              · exact Or.inl (by simpa [runPrefix, Tree.route] using congrArg Nat.succ hd)
              · exact Or.inr ⟨b, l, rr, by simpa [runPrefix, Tree.state] using hb⟩

/-- The full stopped prefix has exact total dyadic capacity. This is an
equality derived by recursion over its branches, not a Kraft-bound premise. -/
theorem runPrefix_capacity_eq (r : ℕ) (P : Protocol X Y Bool)
    (h : NoEarlyLeaf r P) :
    (∑ v : (runPrefix r P).Leaves,
      2 ^ (r - ((runPrefix r P).route v).length)) = 2 ^ r := by
  induction r generalizing P with
  | zero =>
      change (∑ _ : Unit, (1 : ℕ)) = 1
      simp
  | succ r ih =>
      cases P with
      | leaf z => exact False.elim h
      | bNode q left right =>
          change (∑ _ : Unit, 2 ^ (r + 1)) = 2 ^ (r + 1)
          simp
      | aNode q left right =>
          have hl := ih left h.1
          have hr := ih right h.2
          change (∑ v : (Tree.fork 0 (runPrefix r left) (runPrefix r right)).Leaves,
            2 ^ (r + 1 - ((Tree.fork 0 (runPrefix r left) (runPrefix r right)).route v).length)) =
              2 ^ (r + 1)
          rw [Tree.sum_fork]
          simp only [Tree.route_fork_inl, Tree.route_fork_inr, List.length_cons]
          have hsub (n : ℕ) : r + 1 - (n + 1) = r - n := by omega
          simp_rw [hsub]
          rw [hl, hr]
          rw [pow_succ]
          omega

theorem padded_capacity_eq (r : ℕ) (P : Protocol X Y Bool) :
    (∑ v : (runPrefix r (padAlicePrefix r P)).Leaves,
      2 ^ (r - ((runPrefix r (padAlicePrefix r P)).route v).length)) = 2 ^ r :=
  runPrefix_capacity_eq r _ (padAlicePrefix_noEarlyLeaf r P)

theorem padded_stop_or_depth (r : ℕ) (P : Protocol X Y Bool)
    (v : (runPrefix r (padAlicePrefix r P)).Leaves) :
    ((runPrefix r (padAlicePrefix r P)).route v).length = r ∨
      ∃ q left right,
        (runPrefix r (padAlicePrefix r P)).state v = Protocol.bNode q left right :=
  runPrefix_stop_or_depth r _ (padAlicePrefix_noEarlyLeaf r P) v

theorem padded_cost_add_length (r : ℕ) (P : Protocol X Y Bool)
    (v : (runPrefix r (padAlicePrefix r P)).Leaves) :
    ((runPrefix r (padAlicePrefix r P)).state v).cost +
      ((runPrefix r (padAlicePrefix r P)).route v).length ≤ max P.cost r :=
  (runPrefix_cost_add_length r (padAlicePrefix r P) v).trans
    (padAlicePrefix_cost_le r P)

theorem runPrefix_prefixFree (r : ℕ) (P : Protocol X Y Bool) :
    Paper2.Frontier.PrefixFree (runPrefix r P).route :=
  (runPrefix r P).prefixFree

/-- The tree position reached by a row is unique because its physical route
is unique. This does not count certificates or owners. -/
theorem destination_unique_route (r : ℕ) (P : Protocol X Y Bool) (x : X)
    (v : (runPrefix r P).Leaves)
    (h : (runPrefix r P).route v =
      (runPrefix r P).route (destination r P x)) :
    v = destination r P x := (runPrefix r P).route_injective h

end Paper2.ReferencePrefix

#print axioms Paper2.ReferencePrefix.padAlicePrefix_eval
#print axioms Paper2.ReferencePrefix.padAlicePrefix_cost_le
#print axioms Paper2.ReferencePrefix.destination_eval
#print axioms Paper2.ReferencePrefix.runPrefix_cost_add_length
#print axioms Paper2.ReferencePrefix.follows_iff_destination
#print axioms Paper2.ReferencePrefix.padded_capacity_eq
#print axioms Paper2.ReferencePrefix.padded_stop_or_depth
