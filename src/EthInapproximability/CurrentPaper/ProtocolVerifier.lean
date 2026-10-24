import Workspace.UpperBound
import EthInapproximability.CurrentPaper.ProtocolPruning

/-!
# Explicit protocol certificates and their verifier

Source: current paper v8, `03-exact-hardness.tex`, final paragraph of the
NP-completeness proof (NP membership).  Certificate queries are literal bit
lists, not arbitrary predicates or an assumed protocol-computability oracle.
The verifier checks their lengths, the depth, and every truth-table entry.

The finite correctness and operation-count claims here do not by themselves
assert membership in a machine-model definition of NP.  The final complexity
endpoint must connect this concrete finite algorithm to its chosen encoding.
-/

namespace EthInapproximability.CurrentPaper.ProtocolVerifier

open Workspace.Types.Protocol Workspace.Types.CommComplexity

/-- A finite binary tree with a public bit at each leaf and explicit query
tables at internal nodes.  Ill-shaped tables are allowed as inputs and rejected
by `wellFormed`; this makes verification total on all certificates. -/
inductive Certificate where
  | leaf (value : Bool)
  | alice (query : List Bool) (left right : Certificate)
  | bob (query : List Bool) (left right : Certificate)
  deriving DecidableEq, Repr

namespace Certificate

def nodes : Certificate → Nat
  | .leaf _ => 1
  | .alice _ l t | .bob _ l t => 1 + l.nodes + t.nodes

def depth : Certificate → Nat
  | .leaf _ => 0
  | .alice _ l t | .bob _ l t => 1 + max l.depth t.depth

/-- Two tag bits per node, plus the literal local query table. -/
def bits : Certificate → Nat
  | .leaf _ => 2
  | .alice q l t | .bob q l t => 2 + q.length + l.bits + t.bits

def wellFormed (rows cols : Nat) : Certificate → Bool
  | .leaf _ => true
  | .alice q l t => decide (q.length = rows) && l.wellFormed rows cols &&
      t.wellFormed rows cols
  | .bob q l t => decide (q.length = cols) && l.wellFormed rows cols &&
      t.wellFormed rows cols

def eval : Certificate → Nat → Nat → Bool
  | .leaf b, _, _ => b
  | .alice q l t, x, y => if q[x]?.getD false then t.eval x y else l.eval x y
  | .bob q l t, x, y => if q[y]?.getD false then t.eval x y else l.eval x y

/-- The semantic protocol associated with a certificate. -/
def toProtocol (rows cols : Nat) : Certificate → Protocol (Fin rows) (Fin cols) Bool
  | .leaf b => .leaf b
  | .alice q l t => .aNode (fun x => q[x.val]?.getD false)
      (l.toProtocol rows cols) (t.toProtocol rows cols)
  | .bob q l t => .bNode (fun y => q[y.val]?.getD false)
      (l.toProtocol rows cols) (t.toProtocol rows cols)

theorem toProtocol_cost (rows cols : Nat) (p : Certificate) :
    (p.toProtocol rows cols).cost = p.depth := by
  induction p with
  | leaf b => rfl
  | alice q l t hl ht => simp_all [toProtocol, Protocol.cost, depth]
  | bob q l t hl ht => simp_all [toProtocol, Protocol.cost, depth]

theorem toProtocol_eval (rows cols : Nat) (p : Certificate)
    (x : Fin rows) (y : Fin cols) :
    (p.toProtocol rows cols).eval x y = p.eval x.val y.val := by
  induction p with
  | leaf b => rfl
  | alice q l t hl ht => simp_all [toProtocol, Protocol.eval, eval]
  | bob q l t hl ht => simp_all [toProtocol, Protocol.eval, eval]

/-- Tabulate each query in a given finite-domain protocol. -/
def ofProtocol {rows cols : Nat} : Protocol (Fin rows) (Fin cols) Bool → Certificate
  | .leaf b => .leaf b
  | .aNode q l t => .alice (List.ofFn q) (ofProtocol l) (ofProtocol t)
  | .bNode q l t => .bob (List.ofFn q) (ofProtocol l) (ofProtocol t)

theorem ofProtocol_wellFormed {rows cols : Nat}
    (p : Protocol (Fin rows) (Fin cols) Bool) :
    (ofProtocol p).wellFormed rows cols = true := by
  induction p with
  | leaf b => rfl
  | aNode q l t hl ht => simp_all [ofProtocol, wellFormed]
  | bNode q l t hl ht => simp_all [ofProtocol, wellFormed]

theorem ofProtocol_depth {rows cols : Nat}
    (p : Protocol (Fin rows) (Fin cols) Bool) :
    (ofProtocol p).depth = p.cost := by
  induction p with
  | leaf b => rfl
  | aNode q l t hl ht => simp_all [ofProtocol, depth, Protocol.cost]
  | bNode q l t hl ht => simp_all [ofProtocol, depth, Protocol.cost]

theorem ofProtocol_nodes {rows cols : Nat}
    (p : Protocol (Fin rows) (Fin cols) Bool) :
    (ofProtocol p).nodes = ProtocolPruning.nodeCount p := by
  induction p with
  | leaf b => rfl
  | aNode q l t hl ht => simp_all [ofProtocol, nodes, ProtocolPruning.nodeCount]
  | bNode q l t hl ht => simp_all [ofProtocol, nodes, ProtocolPruning.nodeCount]

theorem ofProtocol_eval {rows cols : Nat}
    (p : Protocol (Fin rows) (Fin cols) Bool) (x : Fin rows) (y : Fin cols) :
    (ofProtocol p).eval x.val y.val = p.eval x y := by
  induction p with
  | leaf b => rfl
  | aNode q l t hl ht =>
      simp_all [ofProtocol, eval, Protocol.eval, x.isLt]
  | bNode q l t hl ht =>
      simp_all [ofProtocol, eval, Protocol.eval, y.isLt]

theorem nodes_pos (p : Certificate) : 0 < p.nodes := by
  cases p <;> simp [nodes]

theorem depth_le_nodes (p : Certificate) : p.depth ≤ p.nodes := by
  induction p with
  | leaf b => simp [depth, nodes]
  | alice q l t hl ht => simp [depth, nodes]; omega
  | bob q l t hl ht => simp [depth, nodes]; omega

theorem bits_le (rows cols : Nat) (p : Certificate)
    (h : p.wellFormed rows cols = true) :
    p.bits ≤ (max rows cols + 2) * p.nodes := by
  induction p with
  | leaf b => simp [bits, nodes]
  | alice q l t hl ht =>
      simp only [wellFormed, Bool.and_eq_true, decide_eq_true_eq] at h
      have hq := Nat.le_max_left rows cols
      have hleft := hl h.1.2
      have hright := ht h.2
      simp only [bits, nodes]
      rw [h.1.1]
      nlinarith
  | bob q l t hl ht =>
      simp only [wellFormed, Bool.and_eq_true, decide_eq_true_eq] at h
      have hq := Nat.le_max_right rows cols
      have hleft := hl h.1.2
      have hright := ht h.2
      simp only [bits, nodes]
      rw [h.1.1]
      nlinarith

end Certificate

/-- The actual row-major interpretation of the input list.  The verifier
rejects wrong list lengths before interpreting this as a valid truth table. -/
def tableEntry (cols : Nat) (table : List Bool) (x y : Nat) : Bool :=
  table[x * cols + y]?.getD false

def tableGame (rows cols : Nat) (table : List Bool) : Fin rows → Fin cols → Bool :=
  fun x y => tableEntry cols table x.val y.val

/-- Total Boolean verifier: the semantic check is a literal double traversal
of the finite numeric input ranges. -/
def verify (rows cols threshold : Nat) (table : List Bool) (p : Certificate) : Bool :=
  decide (table.length = rows * cols) && p.wellFormed rows cols &&
    decide (p.depth ≤ threshold) &&
    (if rows = 0 ∨ cols = 0 then true else
      (List.range rows).all (fun x => (List.range cols).all
        (fun y => p.eval x y == tableEntry cols table x y)))

theorem verify_iff (rows cols threshold : Nat) (table : List Bool) (p : Certificate) :
    verify rows cols threshold table p = true ↔
      table.length = rows * cols ∧ p.wellFormed rows cols = true ∧
      p.depth ≤ threshold ∧
      ∀ x : Fin rows, ∀ y : Fin cols, p.eval x.val y.val =
        tableGame rows cols table x y := by
  by_cases hrows : rows = 0
  · subst rows
    simp [verify, Bool.and_eq_true, and_assoc]
  by_cases hcols : cols = 0
  · subst cols
    simp [verify, Bool.and_eq_true, and_assoc]
  simp only [verify, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, beq_iff_eq, tableGame, hrows, hcols, or_self, if_false]
  constructor
  · rintro ⟨⟨⟨ht, hp⟩, hd⟩, he⟩
    exact ⟨ht, hp, hd, fun x y => he x.val x.isLt y.val y.isLt⟩
  · rintro ⟨ht, hp, hd, he⟩
    exact ⟨⟨⟨ht, hp⟩, hd⟩, fun x hx y hy => he ⟨x, hx⟩ ⟨y, hy⟩⟩

theorem verify_sound (rows cols threshold : Nat) (table : List Bool) (p : Certificate)
    (h : verify rows cols threshold table p = true) :
    D (tableGame rows cols table) ≤ threshold := by
  obtain ⟨_, _, hd, he⟩ := (verify_iff rows cols threshold table p).1 h
  have hc : (p.toProtocol rows cols).Computes (tableGame rows cols table) := by
    intro x y
    rw [Certificate.toProtocol_eval]
    exact he x y
  have hmem : (p.toProtocol rows cols).cost ∈ AchievableCosts
      (tableGame rows cols table) := ⟨p.toProtocol rows cols, rfl, hc⟩
  exact (Nat.sInf_le hmem).trans (by simpa only [Certificate.toProtocol_cost] using hd)

theorem verify_complete (rows cols threshold : Nat) (table : List Bool)
    (ht : table.length = rows * cols)
    (h : D (tableGame rows cols table) ≤ threshold) :
    ∃ p : Certificate, verify rows cols threshold table p = true := by
  have hne := Workspace.UpperBound.AchievableCosts_nonempty (tableGame rows cols table)
  have hmem : D (tableGame rows cols table) ∈ AchievableCosts
      (tableGame rows cols table) := Nat.sInf_mem hne
  obtain ⟨p, hcost, hc⟩ := hmem
  refine ⟨Certificate.ofProtocol p, (verify_iff rows cols threshold table _).2
    ⟨ht, Certificate.ofProtocol_wellFormed p, ?_, ?_⟩⟩
  · simpa only [Certificate.ofProtocol_depth, hcost] using h
  · intro x y
    rw [Certificate.ofProtocol_eval]
    exact hc x y

/-- Number of list-cell inspections, including the terminal inspection, for
the actual list lookup used by evaluation.  Index arithmetic is not included
in this deliberately explicit list-access cost model. -/
def lookupWork : List Bool → Nat → Nat
  | [], _ => 1
  | _ :: _, 0 => 1
  | _ :: tail, i + 1 => 1 + lookupWork tail i

theorem lookupWork_le (q : List Bool) (i : Nat) : lookupWork q i ≤ q.length + 1 := by
  induction q generalizing i with
  | nil => simp [lookupWork]
  | cons b q ih =>
      cases i with
      | zero => simp [lookupWork]
      | succ i => simp only [lookupWork, List.length_cons]; have := ih i; omega

/-- Cost of the actual execution path: one inspection of each visited tree
node and the cell inspections in that node's explicit query list. -/
def evalWork : Certificate → Nat → Nat → Nat
  | .leaf _, _, _ => 1
  | .alice q l t, x, y => 1 + lookupWork q x +
      if q[x]?.getD false then evalWork t x y else evalWork l x y
  | .bob q l t, x, y => 1 + lookupWork q y +
      if q[y]?.getD false then evalWork t x y else evalWork l x y

theorem evalWork_le (rows cols : Nat) (p : Certificate)
    (h : p.wellFormed rows cols = true) (x y : Nat) :
    evalWork p x y ≤ (max rows cols + 2) * (p.depth + 1) := by
  induction p with
  | leaf b => simp [evalWork, Certificate.depth]
  | alice q l t hl ht =>
      simp only [Certificate.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at h
      have hleft := hl h.1.2
      have hright := ht h.2
      have hlookup := lookupWork_le q x
      have hdim := Nat.le_max_left rows cols
      have hdl := Nat.le_max_left l.depth t.depth
      have hdt := Nat.le_max_right l.depth t.depth
      rw [h.1.1] at hlookup
      simp only [evalWork, Certificate.depth]
      split <;> nlinarith
  | bob q l t hl ht =>
      simp only [Certificate.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at h
      have hleft := hl h.1.2
      have hright := ht h.2
      have hlookup := lookupWork_le q y
      have hdim := Nat.le_max_right rows cols
      have hdl := Nat.le_max_left l.depth t.depth
      have hdt := Nat.le_max_right l.depth t.depth
      rw [h.1.1] at hlookup
      simp only [evalWork, Certificate.depth]
      split <;> nlinarith

/-- Exhaustive (non-short-circuiting) entry comparison work.  This counts
each simulated protocol path, the actual truth-table list lookup, and one
Boolean comparison.  It bounds the short-circuiting entry-comparison phase
as well, not the remaining checks or their machine-level bit costs. -/
def entriesWork (rows cols : Nat) (table : List Bool) (p : Certificate) : Nat :=
  ∑ x ∈ Finset.range rows, ∑ y ∈ Finset.range cols,
    (evalWork p x y + lookupWork table (x * cols + y) + 1)

theorem entriesWork_le (rows cols : Nat) (table : List Bool) (p : Certificate)
    (h : p.wellFormed rows cols = true) :
    entriesWork rows cols table p ≤ rows * cols *
      ((max rows cols + 2) * (p.depth + 1) + table.length + 2) := by
  unfold entriesWork
  calc
    _ ≤ ∑ _x ∈ Finset.range rows, ∑ _y ∈ Finset.range cols,
        ((max rows cols + 2) * (p.depth + 1) + table.length + 2) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      have hEval := evalWork_le rows cols p h x y
      have hLookup := lookupWork_le table (x * cols + y)
      omega
    _ = _ := by simp [Nat.mul_assoc]

/-- Fully numerical polynomial bound on exhaustive entry checks for a
well-formed certificate with at most `nodeBound` nodes.  The additional
bit-cost treatment of counters, products and the threshold remains part of
the machine-model endpoint, not an unstated claim of this theorem. -/
theorem entriesWork_polynomial (rows cols nodeBound : Nat) (table : List Bool)
    (p : Certificate) (h : p.wellFormed rows cols = true)
    (ht : table.length = rows * cols) (hn : p.nodes ≤ nodeBound) :
    entriesWork rows cols table p ≤ rows * cols *
      ((rows + cols + 2) * (nodeBound + 1) + rows * cols + 2) := by
  have he := entriesWork_le rows cols table p h
  have hd := p.depth_le_nodes
  have hm : max rows cols ≤ rows + cols := max_le (by omega) (by omega)
  rw [ht] at he
  apply he.trans
  apply Nat.mul_le_mul_left
  have ha : (max rows cols + 2) * (p.depth + 1) ≤
      (rows + cols + 2) * (nodeBound + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

theorem malformed_table_rejected (rows cols threshold : Nat) (table : List Bool)
    (p : Certificate) (h : table.length ≠ rows * cols) :
    verify rows cols threshold table p = false := by
  simp [verify, h]

/-- A concrete regression: a constant certificate cannot certify a
nonconstant one-row truth table at zero communication. -/
theorem nonconstant_regression :
    verify 1 2 0 [false, true] (.leaf false) = false := by decide

/-- Polynomial certificate completeness, without assuming that the supplied
threshold is itself small.  Empty rectangles are covered by a one-leaf tree.
The query-table representation has at most `rows + cols` bits per node. -/
theorem verify_complete_polynomial (rows cols threshold : Nat) (table : List Bool)
    (ht : table.length = rows * cols)
    (h : D (tableGame rows cols table) ≤ threshold) :
    ∃ p : Certificate, verify rows cols threshold table p = true ∧
      p.nodes ≤ 2 * (rows * cols) + 1 ∧
      p.bits ≤ (rows + cols + 2) * (2 * (rows * cols) + 1) := by
  have hne := Workspace.UpperBound.AchievableCosts_nonempty (tableGame rows cols table)
  have hmem : D (tableGame rows cols table) ∈ AchievableCosts
      (tableGame rows cols table) := Nat.sInf_mem hne
  obtain ⟨p, hcost, hc⟩ := hmem
  obtain ⟨q, hq, hqc, hqn⟩ := ProtocolPruning.exists_small_protocol
    (tableGame rows cols table) p hc
  have hnodes : (Certificate.ofProtocol q).nodes ≤ 2 * (rows * cols) + 1 := by
    simpa only [Certificate.ofProtocol_nodes, Fintype.card_fin] using hqn
  have hw := Certificate.ofProtocol_wellFormed q
  refine ⟨Certificate.ofProtocol q, ?_, hnodes, ?_⟩
  · apply (verify_iff rows cols threshold table _).2
    refine ⟨ht, hw, ?_, ?_⟩
    · rw [Certificate.ofProtocol_depth]
      exact hqc.trans (hcost ▸ h)
    · intro x y
      rw [Certificate.ofProtocol_eval]
      exact hq x y
  · exact (Certificate.bits_le rows cols _ hw).trans
      (Nat.mul_le_mul (by omega) hnodes)

/-- Exact finite decision-language equivalence with a polynomial bound on
the literal certificate bits. -/
theorem small_certificate_iff (rows cols threshold : Nat) (table : List Bool)
    (ht : table.length = rows * cols) :
    D (tableGame rows cols table) ≤ threshold ↔
      ∃ p : Certificate, verify rows cols threshold table p = true ∧
        p.bits ≤ (rows + cols + 2) * (2 * (rows * cols) + 1) := by
  constructor
  · intro h
    obtain ⟨p, hp, _, hb⟩ := verify_complete_polynomial rows cols threshold table ht h
    exact ⟨p, hp, hb⟩
  · rintro ⟨p, hp, _⟩
    exact verify_sound rows cols threshold table p hp

/-- A bound polynomial in the number of truth-table entries alone.  Empty
carriers use a fixed two-bit leaf certificate; in the nonempty case each
local input set has at most `rows * cols` elements. -/
theorem verify_complete_table_polynomial (rows cols threshold : Nat) (table : List Bool)
    (ht : table.length = rows * cols)
    (h : D (tableGame rows cols table) ≤ threshold) :
    ∃ p : Certificate, verify rows cols threshold table p = true ∧
      p.nodes ≤ 2 * table.length + 1 ∧
      p.bits ≤ (table.length + 2) * (2 * table.length + 1) := by
  by_cases hrows : rows = 0
  · subst rows
    have ht0 : table.length = 0 := by simpa using ht
    refine ⟨.leaf false, ?_, ?_, ?_⟩
    · simp [verify, ht0, Certificate.wellFormed, Certificate.depth]
    · simp [Certificate.nodes, ht0]
    · simp [Certificate.bits, ht0]
  by_cases hcols : cols = 0
  · subst cols
    have ht0 : table.length = 0 := by simpa using ht
    refine ⟨.leaf false, ?_, ?_, ?_⟩
    · simp [verify, ht0, Certificate.wellFormed, Certificate.depth]
    · simp [Certificate.nodes, ht0]
    · simp [Certificate.bits, ht0]
  obtain ⟨p, hp, hn, _⟩ := verify_complete_polynomial rows cols threshold table ht h
  have hw := ((verify_iff rows cols threshold table p).1 hp).2.1
  have hmax : max rows cols ≤ rows * cols := by
    have hrowspos : 1 ≤ rows := by omega
    have hcolspos : 1 ≤ cols := by omega
    exact max_le (by nlinarith) (by nlinarith)
  refine ⟨p, hp, by simpa only [ht] using hn, ?_⟩
  rw [ht]
  exact (Certificate.bits_le rows cols p hw).trans
    (Nat.mul_le_mul (by omega) hn)

end EthInapproximability.CurrentPaper.ProtocolVerifier
