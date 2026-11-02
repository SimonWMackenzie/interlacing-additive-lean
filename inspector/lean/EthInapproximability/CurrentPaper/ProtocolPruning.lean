import NPCC.Control

/-!
# Small protocol witnesses for an explicit truth table

Source: current paper v8, `03-exact-hardness.tex`, NP-membership paragraph.
This module proves an alternative, depth-independent size normalization:
empty branches can be removed without increasing cost, and
the resulting full binary tree has at most one leaf per input pair.

The normalization is used only for existence of a certificate. It is not a
claim about computing an optimal protocol. The inherited restriction operation
is inspected directly in `NPCC.Control`: it folds a query exactly when that
query is constant on the current side of the reachable rectangle.
-/

namespace EthInapproximability.CurrentPaper.ProtocolPruning

open Workspace.Types.Protocol

variable {X Y Z : Type*}

/-- Number of leaves in the actual binary protocol tree. -/
def leafCount : Protocol X Y Z → ℕ
  | .leaf _ => 1
  | .aNode _ l r => leafCount l + leafCount r
  | .bNode _ l r => leafCount l + leafCount r

/-- Number of all nodes, including output leaves, in the actual tree. -/
def nodeCount : Protocol X Y Z → ℕ
  | .leaf _ => 1
  | .aNode _ l r => 1 + nodeCount l + nodeCount r
  | .bNode _ l r => 1 + nodeCount l + nodeCount r

theorem nodeCount_add_one (P : Protocol X Y Z) :
    nodeCount P + 1 = 2 * leafCount P := by
  induction P <;> simp_all [nodeCount, leafCount] <;> omega

private theorem boolean_partition_card (S : Finset X) (a : X → Bool) :
    (S.filter fun x => a x = false).card +
      (S.filter fun x => a x = true).card = S.card := by
  classical
  simpa [Bool.not_eq_true] using
    (Finset.card_filter_add_card_filter_not
      (s := S) (p := fun x => a x = false))

private theorem both_parts_nonempty (S : Finset X) (a : X → Bool)
    (h : ¬ ∃ b : Bool, ∀ x ∈ S, a x = b) :
    (S.filter fun x => a x = false).Nonempty ∧
      (S.filter fun x => a x = true).Nonempty := by
  classical
  constructor
  · by_contra hempty
    apply h
    refine ⟨true, ?_⟩
    intro x hx
    cases ha : a x with
    | false => exact False.elim (hempty ⟨x, Finset.mem_filter.mpr ⟨hx, ha⟩⟩)
    | true => rfl
  · by_contra hempty
    apply h
    refine ⟨false, ?_⟩
    intro x hx
    cases ha : a x with
    | false => rfl
    | true => exact False.elim (hempty ⟨x, Finset.mem_filter.mpr ⟨hx, ha⟩⟩)

/-- Once constant queries have been folded, each remaining leaf accounts for
at least one of the input pairs in a nonempty starting rectangle. -/
theorem restrict_leafCount_le (P : Protocol X Y Z)
    (R : Finset X) (C : Finset Y) (hR : R.Nonempty) (hC : C.Nonempty) :
    leafCount (NPCC.Protocol.restrict R C P) ≤ R.card * C.card := by
  classical
  induction P generalizing R C with
  | leaf z =>
      have hr := Finset.card_pos.mpr hR
      have hc := Finset.card_pos.mpr hC
      change 1 ≤ R.card * C.card
      exact Nat.mul_pos hr hc
  | aNode a l r ihl ihr =>
      unfold NPCC.Protocol.restrict
      by_cases h : ∃ b, NPCC.Protocol.IsRowConstantOn R a b
      · rw [dif_pos h]
        split
        · exact ihr R C hR hC
        · exact ihl R C hR hC
      · rw [dif_neg h]
        have hp := both_parts_nonempty R a h
        have hl := ihl (R.filter fun x => a x = false) C hp.1 hC
        have hr := ihr (R.filter fun x => a x = true) C hp.2 hC
        simpa only [leafCount, ← Nat.add_mul, boolean_partition_card] using
          Nat.add_le_add hl hr
  | bNode b l r ihl ihr =>
      unfold NPCC.Protocol.restrict
      by_cases h : ∃ a, NPCC.Protocol.IsColConstantOn C b a
      · rw [dif_pos h]
        split
        · exact ihr R C hR hC
        · exact ihl R C hR hC
      · rw [dif_neg h]
        have hp := both_parts_nonempty C b h
        have hl := ihl R (C.filter fun y => b y = false) hR hp.1
        have hr := ihr R (C.filter fun y => b y = true) hR hp.2
        simpa only [leafCount, ← Nat.mul_add, boolean_partition_card] using
          Nat.add_le_add hl hr

/-- Remove unreachable branches. An empty starting rectangle needs no input
queries and can return either output; we fix false. -/
noncomputable def prune (R : Finset X) (C : Finset Y)
    (P : Protocol X Y Bool) : Protocol X Y Bool := by
  classical
  exact if R.Nonempty ∧ C.Nonempty then NPCC.Protocol.restrict R C P else .leaf false

theorem prune_eval (R : Finset X) (C : Finset Y)
    (P : Protocol X Y Bool) {x : X} {y : Y} (hx : x ∈ R) (hy : y ∈ C) :
    (prune R C P).eval x y = P.eval x y := by
  classical
  rw [prune, if_pos ⟨⟨x, hx⟩, ⟨y, hy⟩⟩]
  exact NPCC.Protocol.eval_restrict_of_mem R C P hx hy

theorem prune_cost_le (R : Finset X) (C : Finset Y)
    (P : Protocol X Y Bool) : (prune R C P).cost ≤ P.cost := by
  classical
  unfold prune
  split
  · exact NPCC.Protocol.cost_restrict_le R C P
  · exact Nat.zero_le _

theorem prune_leafCount_le (R : Finset X) (C : Finset Y)
    (P : Protocol X Y Bool) :
    leafCount (prune R C P) ≤ max 1 (R.card * C.card) := by
  classical
  unfold prune
  split
  · rename_i h
    exact (restrict_leafCount_le P R C h.1 h.2).trans (le_max_right _ _)
  · exact le_max_left _ _

/-- Linear in the number of entries, uniformly including empty input sets. -/
theorem prune_nodeCount_le (R : Finset X) (C : Finset Y)
    (P : Protocol X Y Bool) :
    nodeCount (prune R C P) ≤ 2 * (R.card * C.card) + 1 := by
  have hle := prune_leafCount_le R C P
  have heq := nodeCount_add_one (prune R C P)
  omega

/-- On nonempty rectangles the full-binary-tree bound is exactly the usual
`2L-1` bound with `L` at most the number of matrix entries. -/
theorem prune_nodeCount_add_one_le (R : Finset X) (C : Finset Y)
    (P : Protocol X Y Bool) (hR : R.Nonempty) (hC : C.Nonempty) :
    nodeCount (prune R C P) + 1 ≤ 2 * (R.card * C.card) := by
  classical
  rw [nodeCount_add_one, prune, if_pos ⟨hR, hC⟩]
  exact Nat.mul_le_mul_left 2 (restrict_leafCount_le P R C hR hC)

/-- Every protocol for a finite explicit matrix has an equally cheap protocol
with a truth-table-polynomial number of nodes. -/
theorem exists_small_protocol [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (P : Protocol X Y Bool) (hP : P.Computes f) :
    ∃ Q : Protocol X Y Bool, Q.Computes f ∧ Q.cost ≤ P.cost ∧
      nodeCount Q ≤ 2 * (Fintype.card X * Fintype.card Y) + 1 := by
  classical
  refine ⟨prune Finset.univ Finset.univ P, ?_, prune_cost_le _ _ _, ?_⟩
  · intro x y
    exact (prune_eval _ _ _ (Finset.mem_univ x) (Finset.mem_univ y)).trans (hP x y)
  · simpa using prune_nodeCount_le Finset.univ Finset.univ P

end EthInapproximability.CurrentPaper.ProtocolPruning
