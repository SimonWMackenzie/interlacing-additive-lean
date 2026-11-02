import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Current replacement paper: the global count of additional rows

Source: `papers/interlacing-np-eth/versions/2026-09-22-complete-replacement-v8/`
`source/sections/A-stage4-details.tex`, claims `clm:paper-global-outflow`,
`clm:paper-global-transfer`, `clm:paper-global-capacity`, and the paragraph
"The total row count", using `eq:paper-global-count-gate`.

This is a finite counting theorem, not a communication lower bound. Rows are
actual distinct elements of a finite set. Each has one originating coordinate
and one stopping destination. Their mass is their cardinality divided by the
same positive row count. The complete stopping set is used: there is no
reference-row-support predicate and no exclusion of zero-reference nodes.

The old frozen route's `MassRedistributionCounting` / `OwnerMassTransfer`
engines were inspected, but they use the obsolete Bob-heavy / good-donor split
and arbitrary real-valued mass arrays. They are not used or modified here.
The current proof has a different finite partition, with one additional group.

The protocol construction of the assignment, its Kraft bound, and the local
communication arguments supplying outflow, transfer and receiving bounds
remain separate obligations. None is encoded as an opaque proof record.
-/

namespace EthInapproximability.CurrentPaper.GlobalCount

open scoped BigOperators

variable {Row Coord Node : Type*}
variable [DecidableEq Row] [DecidableEq Coord] [DecidableEq Node]

/-- All stopping nodes not assigned to a coordinate of `J`, including nodes
with no retained reference rows. -/
def otherNodes (nodes : Finset Node) (J : Finset Coord) (assigned : Coord → Node) :
    Finset Node := nodes \ J.image assigned

/-- Additional rows of `j` which leave its assigned stopping node. -/
def outgoing (rows : Finset Row) (origin : Row → Coord) (destination : Row → Node)
    (assigned : Coord → Node) (j : Coord) : Finset Row :=
  rows.filter fun r => origin r = j ∧ destination r ≠ assigned j

/-- Those outgoing rows which reach another assigned node. -/
def transferred (rows : Finset Row) (origin : Row → Coord) (destination : Row → Node)
    (J : Finset Coord) (assigned : Coord → Node) (j : Coord) : Finset Row :=
  (outgoing rows origin destination assigned j).filter fun r =>
    destination r ∈ J.image assigned

/-- Rows originating at `j` which reach an unassigned stopping node. -/
def sentToOther (rows : Finset Row) (origin : Row → Coord) (destination : Row → Node)
    (nodes : Finset Node) (J : Finset Coord) (assigned : Coord → Node)
    (j : Coord) : Finset Row :=
  rows.filter fun r => origin r = j ∧ destination r ∈ otherNodes nodes J assigned

/-- All retained additional rows from coordinates of `J` received at `v`. -/
def received (rows : Finset Row) (origin : Row → Coord) (destination : Row → Node)
    (J : Finset Coord) (v : Node) : Finset Row :=
  rows.filter fun r => origin r ∈ J ∧ destination r = v

/-- All masses use the row count of one copy of the duplicated matrix. -/
def mass (m : ℕ) (s : Finset Row) : ℚ := (s.card : ℚ) / m

/-- The set identity behind the paper's stay / transfer / unassigned split.
Completeness of the stopping collection prevents rows from disappearing. -/
theorem outgoing_partition (rows : Finset Row) (origin : Row → Coord)
    (destination : Row → Node) (nodes : Finset Node) (J : Finset Coord)
    (assigned : Coord → Node) (j : Coord) (hj : j ∈ J)
    (hcomplete : ∀ r ∈ rows, destination r ∈ nodes) :
    outgoing rows origin destination assigned j =
      transferred rows origin destination J assigned j ∪
        sentToOther rows origin destination nodes J assigned j := by
  ext r
  simp only [outgoing, transferred, sentToOther, otherNodes, Finset.mem_filter,
    Finset.mem_union, Finset.mem_sdiff]
  have hown : assigned j ∈ J.image assigned := Finset.mem_image_of_mem _ hj
  constructor
  · rintro ⟨hr, horigin, hdest⟩
    by_cases h : destination r ∈ J.image assigned
    · exact Or.inl ⟨⟨hr, horigin, hdest⟩, h⟩
    · exact Or.inr ⟨hr, horigin, hcomplete r hr, h⟩
  · rintro (⟨⟨hr, horigin, hdest⟩, _⟩ | ⟨hr, horigin, _, hnot⟩)
    · exact ⟨hr, horigin, hdest⟩
    · exact ⟨hr, horigin, fun h => hnot (h ▸ hown)⟩

omit [DecidableEq Row] in
/-- No actual row can count both as a transfer and as unassigned reception. -/
theorem transferred_disjoint_sentToOther (rows : Finset Row) (origin : Row → Coord)
    (destination : Row → Node) (nodes : Finset Node) (J : Finset Coord)
    (assigned : Coord → Node) (j : Coord) :
    Disjoint (transferred rows origin destination J assigned j)
      (sentToOther rows origin destination nodes J assigned j) := by
  apply Finset.disjoint_left.mpr
  intro r ht hs
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hs).2.2).2
    (Finset.mem_filter.mp ht).2

/-- Consequently the outgoing mass is exactly transfer plus unassigned mass. -/
theorem outgoing_mass_split (rows : Finset Row) (origin : Row → Coord)
    (destination : Row → Node) (nodes : Finset Node) (J : Finset Coord)
    (assigned : Coord → Node) (j : Coord) (hj : j ∈ J) (m : ℕ)
    (hcomplete : ∀ r ∈ rows, destination r ∈ nodes) :
    mass m (outgoing rows origin destination assigned j) =
      mass m (transferred rows origin destination J assigned j) +
        mass m (sentToOther rows origin destination nodes J assigned j) := by
  rw [outgoing_partition rows origin destination nodes J assigned j hj hcomplete]
  simp only [mass, Finset.card_union_of_disjoint
    (transferred_disjoint_sentToOther rows origin destination nodes J assigned j),
    Nat.cast_add, add_div]

omit [DecidableEq Row] in
/-- Sender and receiver descriptions count the identical finite row set.
No conservation equation is assumed. -/
theorem total_sent_eq_total_received (rows : Finset Row) (origin : Row → Coord)
    (destination : Row → Node) (nodes : Finset Node) (J : Finset Coord)
    (assigned : Coord → Node) (m : ℕ) :
    (∑ j ∈ J, mass m (sentToOther rows origin destination nodes J assigned j)) =
      ∑ v ∈ otherNodes nodes J assigned, mass m (received rows origin destination J v) := by
  have hleft := Finset.sum_card_fiberwise_eq_card_filter
    (rows.filter fun r => destination r ∈ otherNodes nodes J assigned) J origin
  have hright := Finset.sum_card_fiberwise_eq_card_filter
    (rows.filter fun r => origin r ∈ J) (otherNodes nodes J assigned) destination
  have hcards : (∑ j ∈ J, (sentToOther rows origin destination nodes J assigned j).card) =
      ∑ v ∈ otherNodes nodes J assigned, (received rows origin destination J v).card := by
    calc
      _ = (rows.filter fun r =>
          destination r ∈ otherNodes nodes J assigned ∧ origin r ∈ J).card := by
        simpa only [sentToOther, Finset.filter_filter, and_comm] using hleft
      _ = (rows.filter fun r =>
          origin r ∈ J ∧ destination r ∈ otherNodes nodes J assigned).card := by
        simp only [and_comm]
      _ = _ := by simpa only [received, Finset.filter_filter] using hright.symm
  simp only [mass, ← Finset.sum_div, ← Nat.cast_sum]
  rw [hcards]

/-- The paper's local constants give more than `4 eta / 5` mass to unassigned
nodes at every assigned coordinate. -/
theorem sent_mass_lower (rows : Finset Row) (origin : Row → Coord)
    (destination : Row → Node) (nodes : Finset Node) (J : Finset Coord)
    (assigned : Coord → Node) (j : Coord) (hj : j ∈ J) (m : ℕ) (eta : ℚ)
    (hcomplete : ∀ r ∈ rows, destination r ∈ nodes)
    (hout : 7 * eta / 8 < mass m (outgoing rows origin destination assigned j))
    (htransfer : mass m (transferred rows origin destination J assigned j) ≤ 3 * eta / 40) :
    4 * eta / 5 < mass m (sentToOther rows origin destination nodes J assigned j) := by
  have hsplit := outgoing_mass_split rows origin destination nodes J assigned j hj m hcomplete
  linarith

omit [DecidableEq Coord] in
/-- Distinct assigned terminal nodes each consume one unit of the total
selector capacity. This derives the other-node capacity bound from Kraft. -/
theorem other_capacity_le (nodes : Finset Node) (J : Finset Coord)
    (assigned : Coord → Node) (capacity : Node → ℚ) (q : ℚ)
    (hassign : ∀ j ∈ J, assigned j ∈ nodes)
    (hinj : Set.InjOn assigned J)
    (hunit : ∀ j ∈ J, capacity (assigned j) = 1)
    (hbudget : ∑ v ∈ nodes, capacity v ≤ q) :
    ∑ v ∈ otherNodes nodes J assigned, capacity v ≤ q - J.card := by
  have hsubset : J.image assigned ⊆ nodes := by
    intro v hv
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
    exact hassign j hj
  have hsum : (∑ v ∈ J.image assigned, capacity v) = (J.card : ℚ) := by
    rw [Finset.sum_image]
    · calc
        _ = ∑ _j ∈ J, (1 : ℚ) := Finset.sum_congr rfl hunit
        _ = _ := by simp
    · exact fun _ h₁ _ h₂ heq => hinj h₁ h₂ heq
  have hsplit := Finset.sum_sdiff hsubset (f := capacity)
  change ∑ v ∈ nodes \ J.image assigned, capacity v ≤ q - J.card
  linarith

/-- Finite contradiction used in the v8 final restriction bound.

Only *local* outflow/transfer/receiving estimates are supplied. The proof
derives the partition, conservation of actual rows, and total capacity.
`m > 0` fixes the intended common normalization; no synthetic mass array or
aggregate contradiction is accepted as input. The protocol-to-local-estimate
arguments are deliberately not claimed here. -/
theorem global_count_contradiction
    (rows : Finset Row) (origin : Row → Coord) (destination : Row → Node)
    (nodes : Finset Node) (J : Finset Coord) (assigned : Coord → Node)
    (capacity : Node → ℚ) (m : ℕ) (q eta F E : ℚ)
    (hm : 0 < m) (heta : 0 < eta) (hF : 0 ≤ F)
    (hcomplete : ∀ r ∈ rows, destination r ∈ nodes)
    (hassign : ∀ j ∈ J, assigned j ∈ nodes)
    (hinj : Set.InjOn assigned J)
    (hunit : ∀ j ∈ J, capacity (assigned j) = 1)
    (hbudget : ∑ v ∈ nodes, capacity v ≤ q)
    (hJ : q - E ≤ (J.card : ℚ))
    (hout : ∀ j ∈ J, 7 * eta / 8 < mass m (outgoing rows origin destination assigned j))
    (htransfer : ∀ j ∈ J,
      mass m (transferred rows origin destination J assigned j) ≤ 3 * eta / 40)
    (hreceive : ∀ v ∈ otherNodes nodes J assigned,
      mass m (received rows origin destination J v) ≤ 2 * F * capacity v)
    (hgate : (1 + 4 * F / eta) * E < q) : False := by
  have hdenom : (m : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hgate' : 2 * F * E < eta / 2 * (q - E) := by
    have hh := (mul_lt_mul_of_pos_left hgate heta)
    field_simp [ne_of_gt heta] at hh
    nlinarith
  have hother : ∑ v ∈ otherNodes nodes J assigned, capacity v ≤ E :=
    le_trans (other_capacity_le nodes J assigned capacity q hassign hinj hunit hbudget)
      (by linarith)
  have hlow : eta / 2 * (J.card : ℚ) ≤
      ∑ j ∈ J, mass m (sentToOther rows origin destination nodes J assigned j) := by
    calc
      eta / 2 * (J.card : ℚ) = ∑ _j ∈ J, eta / 2 := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun j hj => by
        have hh := sent_mass_lower rows origin destination nodes J assigned j hj m eta
          hcomplete (hout j hj) (htransfer j hj)
        linarith
  have hupp : (∑ v ∈ otherNodes nodes J assigned,
      mass m (received rows origin destination J v)) ≤ 2 * F * E := by
    calc
      _ ≤ ∑ v ∈ otherNodes nodes J assigned, 2 * F * capacity v :=
        Finset.sum_le_sum hreceive
      _ = 2 * F * ∑ v ∈ otherNodes nodes J assigned, capacity v := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hother (by positivity)
  rw [total_sent_eq_total_received] at hlow
  have hlower := mul_le_mul_of_nonneg_left hJ (show 0 ≤ eta / 2 by positivity)
  linarith

/-- A finite regression, not a paper instance. Two retained additional rows
originate at coordinate zero. One reaches the node assigned to coordinate one;
the other reaches node two, which may have no reference rows. Keeping node two
gives `2/10 = 1/10 + 1/10`; omitting it incorrectly removes the last `1/10`.
This example uses kernel reduction, not an external evaluation oracle. -/
theorem complete_collection_regression :
    let rows : Finset ℕ := {0, 1}
    let origin : ℕ → ℕ := fun _ => 0
    let destination : ℕ → ℕ := fun r => if r = 0 then 1 else 2
    let J : Finset ℕ := {0, 1}
    let assigned : ℕ → ℕ := id
    mass 10 (outgoing rows origin destination assigned 0) = 1 / 5 ∧
    mass 10 (transferred rows origin destination J assigned 0) = 1 / 10 ∧
    mass 10 (sentToOther rows origin destination {0, 1, 2} J assigned 0) = 1 / 10 ∧
    mass 10 (sentToOther rows origin destination {0, 1} J assigned 0) = 0 := by
  norm_num [mass, outgoing, transferred, sentToOther, otherNodes,
    Finset.filter_insert, Finset.filter_singleton]

end EthInapproximability.CurrentPaper.GlobalCount

#print axioms EthInapproximability.CurrentPaper.GlobalCount.outgoing_partition
#print axioms EthInapproximability.CurrentPaper.GlobalCount.total_sent_eq_total_received
#print axioms EthInapproximability.CurrentPaper.GlobalCount.other_capacity_le
#print axioms EthInapproximability.CurrentPaper.GlobalCount.global_count_contradiction
#print axioms EthInapproximability.CurrentPaper.GlobalCount.complete_collection_regression
