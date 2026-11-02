import EthInapproximability.ParameterizedNP.RoutedCertificateConstruction
import EthInapproximability.CurrentPaper.GlobalCount

/-!
# The complete stopping collection of an actual protocol

Trace: current replacement v8, `A-stage4-details.tex`, "The full-cost bound"
and "Stopping rectangles" (in particular the instruction to include nodes with
no reference rows), then the final global row count.

Unlike the old reference-certificate frontier, the finite collection below is
computed from **all retained rows**. Every row follows the actual Alice
predicates; its destination does not depend on Bob's input. Dummy completion,
the Alice-path definitions, and the prefix-free Kraft theorem are consumed from
their audited existing owners, not reimplemented. The new part is the complete
row-based stopping collection and its connection to the current global count.

This file does not derive the reference assignment or the construction-specific
local communication lower bounds. Those remain explicit inputs at their sites.
-/

namespace EthInapproximability.CurrentPaper.ProtocolFrontier

open scoped BigOperators
open Workspace.Types.Protocol
open Workspace.UpperBound
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.ParameterizedNP.DenseFrontierConservation
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem
open EthInapproximability.ParameterizedNP.RoutingDynamics
open EthInapproximability.ParameterizedNP.RoutedCertificateConstruction

variable {X Y Z : Type*}

/-- Execute at most `r` actual Alice queries, stopping before any Bob query.
For a completed protocol, the leaf case cannot arise before the cutoff. -/
def rowStop : ℕ → Protocol X Y Z → X → List Bool
  | 0, _, _ => []
  | _ + 1, .leaf _, _ => []
  | _ + 1, .bNode _ _ _, _ => []
  | r + 1, .aNode a l h, x =>
      if a x then true :: rowStop r h x else false :: rowStop r l x

/-- The chosen row address follows only Alice queries and has the prescribed
depth bound. This is proved from protocol execution, not assumed. -/
theorem rowStop_alice_length (r : ℕ) (P : Protocol X Y Z) (x : X) :
    IsAlicePath P (rowStop r P x) ∧ (rowStop r P x).length ≤ r := by
  induction r generalizing P with
  | zero => simp [rowStop]
  | succ r ih =>
    cases P with
    | leaf z => simp [rowStop]
    | bNode b l h => simp [rowStop]
    | aNode a l h =>
      have hl := ih l
      have hh := ih h
      cases ha : a x <;>
        simp [rowStop, ha, IsAlicePath, descendStep, hl, hh,
          EthInapproximability.ParameterizedNP.DenseSynchronisation.IsANode]

/-- Completion excludes premature leaves, so the actual row destination is
either a first-Bob node or a depth-`r` terminal node. -/
theorem rowStop_stops (r : ℕ) (P : Protocol X Y Z) (x : X)
    (hc : CompletedNoBob P r) :
    IsFirstBobNode P r (rowStop r P x) ∨ IsFinalAliceNode P r (rowStop r P x) := by
  induction r generalizing P with
  | zero => exact Or.inr ⟨trivial, rfl⟩
  | succ r ih =>
    cases P with
    | leaf z => exact (hc [] trivial (by simp)).elim
    | bNode b l h => exact Or.inl ⟨trivial, trivial, by simp [rowStop]⟩
    | aNode a l h =>
      have hchild (bit : Bool) : CompletedNoBob (descendStep (.aNode a l h) bit) r := by
        intro p hp hlen
        exact hc (bit :: p) ⟨⟨a, l, h, rfl⟩, hp⟩ (by simpa using Nat.succ_lt_succ hlen)
      cases ha : a x with
      | false =>
        have hs := ih l (by simpa [descendStep] using hchild false)
        rcases hs with hs | hs
        · exact Or.inl ⟨(rowStop_alice_length (r + 1) _ x).1,
            by simpa [rowStop, ha, descend, descendStep] using hs.2.1,
            by simpa [rowStop, ha] using Nat.succ_lt_succ hs.2.2⟩
        · exact Or.inr ⟨(rowStop_alice_length (r + 1) _ x).1,
            by simpa [rowStop, ha] using congrArg Nat.succ hs.2⟩
      | true =>
        have hs := ih h (by simpa [descendStep] using hchild true)
        rcases hs with hs | hs
        · exact Or.inl ⟨(rowStop_alice_length (r + 1) _ x).1,
            by simpa [rowStop, ha, descend, descendStep] using hs.2.1,
            by simpa [rowStop, ha] using Nat.succ_lt_succ hs.2.2⟩
        · exact Or.inr ⟨(rowStop_alice_length (r + 1) _ x).1,
            by simpa [rowStop, ha] using congrArg Nat.succ hs.2⟩

/-- All columns remain available: executing the prefix on row `x` preserves
evaluation for every Bob input `y`. -/
theorem rowStop_eval (r : ℕ) (P : Protocol X Y Z) (x : X) (y : Y) :
    (descend P (rowStop r P x)).eval x y = P.eval x y := by
  induction r generalizing P with
  | zero => rfl
  | succ r ih =>
    cases P with
    | leaf z => rfl
    | bNode b l h => rfl
    | aNode a l h =>
      cases ha : a x <;> simp [rowStop, ha, descend, descendStep, Protocol.eval, ih]

/-- The complete, reachable stopping collection, with no reference-support
filter. Empty/unreachable protocol branches need not be counted. -/
def nodes (P : Protocol X Y Z) (r : ℕ) (retained : Finset X) : Finset (List Bool) :=
  retained.image (rowStop r (completeNoBob r P))

/-- Every retained row has its one computed destination in the collection. -/
theorem destination_mem (P : Protocol X Y Z) (r : ℕ) (retained : Finset X)
    {x : X} (hx : x ∈ retained) : rowStop r (completeNoBob r P) x ∈ nodes P r retained :=
  Finset.mem_image_of_mem _ hx

/-- Each actual reachable stopping node satisfies the two stopping rules. -/
theorem node_stops (P : Protocol X Y Z) (r : ℕ) (retained : Finset X)
    {p : List Bool} (hp : p ∈ nodes P r retained) :
    IsFirstBobNode (completeNoBob r P) r p ∨ IsFinalAliceNode (completeNoBob r P) r p := by
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hp
  exact rowStop_stops r _ x (completedNoBob_completeNoBob P r)

/-- Prefix-freeness is a theorem about the actual row-generated collection. -/
theorem nodes_prefixFree (P : Protocol X Y Z) (r : ℕ) (retained : Finset X) :
    PrefixFreeFrontier (fun p : nodes P r retained => p.val) :=
  prefixFree_of_stopping _ (fun p => node_stops P r retained p.property)
    (fun _ _ h => Subtype.ext h)

/-- Kraft for all retained-row stopping nodes, including zero-reference ones. -/
theorem nodes_kraft (P : Protocol X Y Z) (r : ℕ) (retained : Finset X) :
    ∑ p ∈ nodes P r retained, stoppingCapacity r p.length ≤ 2 ^ r := by
  have hk := sum_stoppingCapacity_le_width (r := r)
    (fun p : nodes P r retained => p.val) (nodes_prefixFree P r retained) (fun p => by
      obtain ⟨x, _, hx⟩ := Finset.mem_image.mp p.property
      change p.val.length ≤ r
      rw [← hx]
      exact (rowStop_alice_length r _ x).2)
  calc
    _ = ∑ p : nodes P r retained, stoppingCapacity r p.val.length :=
      (Finset.sum_coe_sort (nodes P r retained)
        (fun p : List Bool => stoppingCapacity r p.length)).symm
    _ ≤ _ := hk

/-- On each stopping rectangle the genuine residual protocol computes the
original function; every retained Bob column can be used. -/
theorem residual_computes (P : Protocol X Y Z) (r : ℕ) (f : X → Y → Z)
    (hf : P.Computes f) (p : List Bool) (x : X)
    (hx : rowStop r (completeNoBob r P) x = p) (y : Y) :
    (descend (completeNoBob r P) p).eval x y = f x y := by
  rw [← hx, rowStop_eval, completeNoBob_eval]
  exact hf x y

/-- Actual prefix length is charged to the residual communication budget. -/
theorem node_residual_budget (P : Protocol X Y Z) (r : ℕ) (retained : Finset X)
    {C : ℕ} (hC : 1 ≤ C) (hcost : P.cost ≤ C + r - 1)
    {p : List Bool} (hp : p ∈ nodes P r retained) :
    (descend (completeNoBob r P) p).cost + p.length ≤ C + r - 1 := by
  have hpath : IsAlicePath (completeNoBob r P) p := by
    rcases node_stops P r retained hp with h | h <;> exact h.1
  exact (cost_descend_add_length_le_of_isAlicePath hpath).trans
    (completeNoBob_cost_le_frame hC hcost)

/-- The actual residual protocol on a stopping rectangle. Alice's carrier is
the fibre of the computed destination; Bob keeps the same entire column set. -/
def residualRestriction [DecidableEq X] (P : Protocol X Y Z) (r : ℕ)
    (retained : Finset X) (columns : Finset Y) (p : List Bool) :
    Protocol {x // x ∈ retained ∧ rowStop r (completeNoBob r P) x = p}
      {y // y ∈ columns} Z :=
  Protocol.comap Subtype.val Subtype.val (descend (completeNoBob r P) p)

/-- One actual common-column rectangle, with its residual cost charged to the
same original protocol. No choice of columns or protocol is made per row. -/
theorem residualRestriction_correct [DecidableEq X] (P : Protocol X Y Z) (r : ℕ)
    (retained : Finset X) (columns : Finset Y) (f : X → Y → Z)
    (hf : P.Computes f) {C : ℕ} (hC : 1 ≤ C) (hcost : P.cost ≤ C + r - 1)
    {p : List Bool} (hp : p ∈ nodes P r retained) :
    (residualRestriction P r retained columns p).Computes (fun x y => f x.val y.val) ∧
      (residualRestriction P r retained columns p).cost + p.length ≤ C + r - 1 := by
  constructor
  · intro x y
    rw [residualRestriction, Protocol.comap_eval]
    exact residual_computes P r f hf p x.val x.property.2 y.val
  · simpa only [residualRestriction, Protocol.comap_cost] using
      node_residual_budget P r retained hC hcost hp

/-- The full-node Kraft bound in the rational normalization used by the new
paper's finite row-count theorem. -/
theorem nodes_kraft_rat (P : Protocol X Y Z) (r : ℕ) (retained : Finset X) :
    (∑ p ∈ nodes P r retained, (stoppingCapacity r p.length : ℚ)) ≤ (2 : ℚ) ^ r := by
  exact_mod_cast nodes_kraft P r retained

/-- A node chosen by an actual retained representative belongs to the complete
collection. If that representative reaches depth `r`, its selector capacity
is one. The injection of distinct assigned coordinates remains an upstream
reference-uniqueness obligation. -/
theorem representative_node_properties (P : Protocol X Y Z) (r : ℕ)
    (retained : Finset X) {x : X} (hx : x ∈ retained)
    (hterminal : (rowStop r (completeNoBob r P) x).length = r) :
    rowStop r (completeNoBob r P) x ∈ nodes P r retained ∧
      stoppingCapacity r (rowStop r (completeNoBob r P) x).length = 1 := by
  exact ⟨destination_mem P r retained hx, by simp [stoppingCapacity, hterminal]⟩

/-- Wire the complete actual-protocol frontier to v8's global row count.

Completeness, stopping capacities, Kraft and membership of assigned nodes are
**derived**. The assignment is induced by actual retained representative rows.
Its injectivity and terminal depth, the size of `J`, and the three local
communication estimates remain explicit upstream obligations. The finite rows
in all three estimates are the same retained `additional` rows, not an abstract
mass array; reference-only filtering is absent.
-/
theorem global_count_of_protocol [DecidableEq X] {Coord : Type*} [DecidableEq Coord]
    (P : Protocol X Y Z) (r : ℕ) (retained additional : Finset X)
    (hadditional : additional ⊆ retained) (origin : X → Coord)
    (J : Finset Coord) (representative : Coord → X)
    (hrepresentative : ∀ j ∈ J, representative j ∈ retained)
    (hinj : Set.InjOn (fun j => rowStop r (completeNoBob r P) (representative j)) J)
    (hterminal : ∀ j ∈ J, (rowStop r (completeNoBob r P) (representative j)).length = r)
    (m : ℕ) (eta F E : ℚ) (hm : 0 < m) (heta : 0 < eta) (hF : 0 ≤ F)
    (hJ : (2 : ℚ) ^ r - E ≤ (J.card : ℚ))
    (hout : ∀ j ∈ J, 7 * eta / 8 < GlobalCount.mass m
      (GlobalCount.outgoing additional origin (rowStop r (completeNoBob r P))
        (fun j => rowStop r (completeNoBob r P) (representative j)) j))
    (htransfer : ∀ j ∈ J, GlobalCount.mass m
      (GlobalCount.transferred additional origin (rowStop r (completeNoBob r P)) J
        (fun j => rowStop r (completeNoBob r P) (representative j)) j) ≤ 3 * eta / 40)
    (hreceive : ∀ p ∈ GlobalCount.otherNodes (nodes P r retained) J
        (fun j => rowStop r (completeNoBob r P) (representative j)),
      GlobalCount.mass m
        (GlobalCount.received additional origin (rowStop r (completeNoBob r P)) J p) ≤
          2 * F * (stoppingCapacity r p.length : ℚ))
    (hgate : (1 + 4 * F / eta) * E < (2 : ℚ) ^ r) : False := by
  apply GlobalCount.global_count_contradiction additional origin
    (rowStop r (completeNoBob r P)) (nodes P r retained) J
    (fun j => rowStop r (completeNoBob r P) (representative j))
    (fun p => (stoppingCapacity r p.length : ℚ)) m ((2 : ℚ) ^ r) eta F E
    hm heta hF
  · exact fun x hx => destination_mem P r retained (hadditional hx)
  · exact fun j hj => destination_mem P r retained (hrepresentative j hj)
  · exact hinj
  · intro j hj
    simp only [stoppingCapacity, hterminal j hj, Nat.sub_self, pow_zero, Nat.cast_one]
  · exact nodes_kraft_rat P r retained
  · exact hJ
  · exact hout
  · exact htransfer
  · exact hreceive
  · exact hgate

/-- A small protocol for a coverage regression, not a paper parameter choice.
The false row stops before Bob; the true row reaches a padded final node. -/
def regressionProtocol : Protocol Bool Bool Bool :=
  .aNode id (.bNode id (.leaf false) (.leaf true)) (.leaf true)

/-- With only the false row marked as reference, the actual true-row terminal
node is still present in the complete collection. Filtering by reference rows
would drop it. -/
theorem zero_reference_node_regression :
    nodes regressionProtocol 2 {false, true} = {[false], [true, false]} ∧
    nodes regressionProtocol 2 {false} = {[false]} ∧
    rowStop 2 (completeNoBob 2 regressionProtocol) true = [true, false] := by
  norm_num [nodes, regressionProtocol, rowStop, completeNoBob, alicePad]

end EthInapproximability.CurrentPaper.ProtocolFrontier

#print axioms EthInapproximability.CurrentPaper.ProtocolFrontier.nodes_kraft
#print axioms EthInapproximability.CurrentPaper.ProtocolFrontier.residual_computes
#print axioms EthInapproximability.CurrentPaper.ProtocolFrontier.node_residual_budget
#print axioms EthInapproximability.CurrentPaper.ProtocolFrontier.global_count_of_protocol
#print axioms EthInapproximability.CurrentPaper.ProtocolFrontier.residualRestriction_correct
#print axioms EthInapproximability.CurrentPaper.ProtocolFrontier.zero_reference_node_regression
