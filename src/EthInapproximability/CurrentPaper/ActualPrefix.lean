import NPCC.Control

/-!
# Actual prefixes of an unpruned protocol

Trace: v8 `02-separation.tex`, `lem:exact-prefix-budget`, and
`G-exact-control.tex`. These structural lemmas use the raw, unpruned input
pullback. When every binary prefix occurs on the retained inputs, the
reachable-prefix conclusion forces every node of the corresponding full
tree prefix to belong to Alice. Thus that prefix applies to additional
inputs as well. No conclusion about a pruned tree is substituted for a
conclusion about the original protocol.
-/

open Workspace.Types.Protocol

namespace EthInapproximability.CurrentPaper.ActualPrefix

open NPCC

variable {A B A' B' Z : Type*}

/-- Every node strictly above depth `k` in the full tree is an Alice node.
This predicate is syntactic, including branches unreachable on a particular
input restriction. -/
def AllAlice : ℕ → Protocol A B Z → Prop
  | 0, _ => True
  | k + 1, .aNode _ l r => AllAlice k l ∧ AllAlice k r
  | _ + 1, .leaf _ => False
  | _ + 1, .bNode _ _ _ => False

/-- Full prefix reachability upgrades restricted row-onlyness to a statement
about the original tree, including rows outside the retained rectangle. -/
theorem allAlice_of_all_codes (R : Finset A) (C : Finset B)
    (k : ℕ) (P : Protocol A B Z)
    (hrow : Protocol.FirstKRowBitsOn R C k P) (hC : C.Nonempty)
    (hcodes : ∀ j, (R.filter (fun a => Protocol.prefixCodeRaw k P a = j)).Nonempty) :
    AllAlice k P := by
  classical
  induction k generalizing R P with
  | zero => trivial
  | succ k ih =>
      have hR : R.Nonempty := by
        obtain ⟨a, ha⟩ := hcodes (Protocol.zeroPow2 (k + 1))
        exact ⟨a, (Finset.mem_filter.mp ha).1⟩
      cases P with
      | leaf z =>
          rcases hrow with h | h
          · exact (hR.ne_empty h).elim
          · exact (hC.ne_empty h).elim
      | bNode q l r =>
          rcases hrow with h | h
          · exact (hR.ne_empty h).elim
          · exact (hC.ne_empty h).elim
      | aNode q l r =>
          change AllAlice k l ∧ AllAlice k r
          have childCodes (b : Bool) : ∀ j,
              ((R.filter (fun a => q a = b)).filter
                (fun a => Protocol.prefixCodeRaw k (if b then r else l) a = j)).Nonempty := by
            intro j
            obtain ⟨a, ha⟩ := hcodes (Protocol.bitCons b j)
            obtain ⟨haR, haCode⟩ := Finset.mem_filter.mp ha
            change Protocol.bitCons (q a)
              (Protocol.prefixCodeRaw k (if q a then r else l) a) =
                Protocol.bitCons b j at haCode
            have he := Protocol.bitCons_injective
              (a₁ := (q a, Protocol.prefixCodeRaw k (if q a then r else l) a))
              (a₂ := (b, j)) haCode
            have hb : q a = b := congrArg Prod.fst he
            have ht := congrArg Prod.snd he
            refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨haR, hb⟩, ?_⟩⟩
            simpa only [hb] using ht
          exact ⟨ih _ l hrow.1 (by simpa using childCodes false),
            ih _ r hrow.2 (by simpa using childCodes true)⟩

/-- A syntactic Alice prefix holds on every input rectangle. -/
theorem AllAlice.onRectangle {k : ℕ} {P : Protocol A B Z}
    (h : AllAlice k P) (R : Finset A) (C : Finset B) :
    Protocol.FirstKRowBitsOn R C k P := by
  induction k generalizing P R with
  | zero => trivial
  | succ k ih =>
      cases P with
      | leaf z => exact h.elim
      | bNode q l r => exact h.elim
      | aNode q l r => exact ⟨ih h.1 _, ih h.2 _⟩

/-- Input pullback changes only predicates, not the sender or shape of nodes. -/
theorem allAlice_pullback_iff (φ : A' → A) (ψ : B' → B)
    (k : ℕ) (P : Protocol A B Z) :
    AllAlice k (Protocol.pullback φ ψ P) ↔ AllAlice k P := by
  induction k generalizing P with
  | zero => rfl
  | succ k ih =>
      cases P with
      | leaf z => rfl
      | bNode q l r => rfl
      | aNode q l r =>
          change (AllAlice k (Protocol.pullback φ ψ l) ∧
            AllAlice k (Protocol.pullback φ ψ r)) ↔ (AllAlice k l ∧ AllAlice k r)
          rw [ih, ih]

/-- The raw restriction can force the original tree's Alice prefix, without
surjectivity of either input map and without deleting any query. -/
theorem allAlice_of_pullback_codes (φ : A' → A) (ψ : B' → B)
    (R : Finset A') (C : Finset B') (k : ℕ) (P : Protocol A B Z)
    (hrow : Protocol.FirstKRowBitsOn R C k (Protocol.pullback φ ψ P))
    (hC : C.Nonempty)
    (hcodes : ∀ j, (R.filter (fun a =>
      Protocol.prefixCodeRaw k (Protocol.pullback φ ψ P) a = j)).Nonempty) :
    AllAlice k P :=
  (allAlice_pullback_iff φ ψ k P).mp
    (allAlice_of_all_codes R C k _ hrow hC hcodes)

/-- The actual unpruned subtree commutes with input pullback. -/
theorem rowSubtreeAtRaw_pullback (φ : A' → A) (ψ : B' → B)
    (k : ℕ) (P : Protocol A B Z) (j : Fin (2 ^ k)) :
    Protocol.rowSubtreeAtRaw k (Protocol.pullback φ ψ P) j =
      Protocol.pullback φ ψ (Protocol.rowSubtreeAtRaw k P j) := by
  induction k generalizing P with
  | zero => rfl
  | succ k ih =>
      cases P with
      | leaf z => rfl
      | bNode q l r => rfl
      | aNode q l r =>
          simp only [Protocol.pullback, Protocol.rowSubtreeAtRaw]
          cases Protocol.bitHead j <;> simp only [Bool.false_eq_true, ↓reduceIte, ih]

/-- Every full-tree suffix of a syntactic Alice prefix obeys the unspent
worst-case budget, whether or not the suffix is reached on a given input. -/
theorem AllAlice.subtree_cost {k : ℕ} {P : Protocol A B Z}
    (h : AllAlice k P) (j : Fin (2 ^ k)) :
    (Protocol.rowSubtreeAtRaw k P j).cost + k ≤ P.cost := by
  induction k generalizing P with
  | zero => simp [Protocol.rowSubtreeAtRaw]
  | succ k ih =>
      cases P with
      | leaf z => exact h.elim
      | bNode q l r => exact h.elim
      | aNode q l r =>
          have hl := ih h.1 (Protocol.bitTail j)
          have hr := ih h.2 (Protocol.bitTail j)
          simp only [Protocol.rowSubtreeAtRaw, Protocol.cost]
          cases Protocol.bitHead j <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- On every ambient row and column, the selected raw suffix gives exactly
the original answer. No membership in the template restriction is needed. -/
theorem AllAlice.subtree_eval {k : ℕ} {P : Protocol A B Z}
    (h : AllAlice k P) (a : A) (b : B) :
    (Protocol.rowSubtreeAtRaw k P (Protocol.prefixCodeRaw k P a)).eval a b =
      P.eval a b := by
  induction k generalizing P with
  | zero => rfl
  | succ k ih =>
      cases P with
      | leaf z => exact h.elim
      | bNode q l r => exact h.elim
      | aNode q l r =>
          cases hq : q a <;>
            simp only [Protocol.prefixCodeRaw, hq, Bool.false_eq_true, ↓reduceIte,
              Protocol.rowSubtreeAtRaw, Protocol.bitHead_bitCons,
              Protocol.bitTail_bitCons, Protocol.eval]
          · exact ih h.1
          · exact ih h.2

/-- Every execution really spends the `k` prefix bits, before entering the
selected suffix; this is an equality for the original protocol. -/
theorem AllAlice.evalDepth_eq {k : ℕ} {P : Protocol A B Z}
    (h : AllAlice k P) (a : A) (b : B) :
    Protocol.evalDepth P a b = k + Protocol.evalDepth
      (Protocol.rowSubtreeAtRaw k P (Protocol.prefixCodeRaw k P a)) a b := by
  induction k generalizing P with
  | zero => simp [Protocol.rowSubtreeAtRaw]
  | succ k ih =>
      cases P with
      | leaf z => exact h.elim
      | bNode q l r => exact h.elim
      | aNode q l r =>
          cases hq : q a <;>
            simp only [Protocol.prefixCodeRaw, hq, Bool.false_eq_true, ↓reduceIte,
              Protocol.rowSubtreeAtRaw, Protocol.bitHead_bitCons,
              Protocol.bitTail_bitCons, Protocol.evalDepth]
          · have hh := ih h.1
            omega
          · have hh := ih h.2
            omega

/-- Swapping the parties commutes with raw input pullback. -/
theorem swap_pullback (φ : A' → A) (ψ : B' → B) (P : Protocol A B Z) :
    Protocol.swap (Protocol.pullback φ ψ P) =
      Protocol.pullback ψ φ (Protocol.swap P) := by
  induction P with
  | leaf z => rfl
  | aNode q l r ihl ihr => simp only [Protocol.pullback, Protocol.swap, ihl, ihr]
  | bNode q l r ihl ihr => simp only [Protocol.pullback, Protocol.swap, ihl, ihr]

/-- The full-tree dual: all of the first `k` nodes belong to Bob. -/
def AllBob (k : ℕ) (P : Protocol A B Z) : Prop := AllAlice k (Protocol.swap P)

/-- Bob's raw suffix, transported back to the original orientation. -/
def colSubtree (k : ℕ) (P : Protocol A B Z) (j : Fin (2 ^ k)) : Protocol A B Z :=
  Protocol.swap (Protocol.rowSubtreeAtRaw k (Protocol.swap P) j)

theorem AllBob.onRectangle {k : ℕ} {P : Protocol A B Z}
    (h : AllBob k P) (R : Finset A) (C : Finset B) :
    Protocol.FirstKColBitsOn R C k P := AllAlice.onRectangle h C R

theorem allBob_pullback_iff (φ : A' → A) (ψ : B' → B)
    (k : ℕ) (P : Protocol A B Z) :
    AllBob k (Protocol.pullback φ ψ P) ↔ AllBob k P := by
  unfold AllBob
  rw [swap_pullback, allAlice_pullback_iff]

/-- The same full-tree lifting for a forced Bob prefix. -/
theorem allBob_of_pullback_codes (φ : A' → A) (ψ : B' → B)
    (R : Finset A') (C : Finset B') (k : ℕ) (P : Protocol A B Z)
    (hcol : Protocol.FirstKColBitsOn R C k (Protocol.pullback φ ψ P))
    (hR : R.Nonempty)
    (hcodes : ∀ j, (C.filter (fun b =>
      Protocol.prefixCodeRaw k (Protocol.swap (Protocol.pullback φ ψ P)) b = j)).Nonempty) :
    AllBob k P :=
  (allBob_pullback_iff φ ψ k P).mp
    (allAlice_of_all_codes C R k _ hcol hR hcodes)

theorem colSubtree_pullback (φ : A' → A) (ψ : B' → B)
    (k : ℕ) (P : Protocol A B Z) (j : Fin (2 ^ k)) :
    colSubtree k (Protocol.pullback φ ψ P) j =
      Protocol.pullback φ ψ (colSubtree k P j) := by
  simp only [colSubtree, swap_pullback, rowSubtreeAtRaw_pullback]

theorem AllBob.subtree_cost {k : ℕ} {P : Protocol A B Z}
    (h : AllBob k P) (j : Fin (2 ^ k)) :
    (colSubtree k P j).cost + k ≤ P.cost := by
  simpa only [colSubtree, Protocol.cost_swap] using AllAlice.subtree_cost h j

theorem AllBob.subtree_eval {k : ℕ} {P : Protocol A B Z}
    (h : AllBob k P) (a : A) (b : B) :
    (colSubtree k P (Protocol.prefixCodeRaw k (Protocol.swap P) b)).eval a b =
      P.eval a b := by
  simpa only [colSubtree, Protocol.eval_swap] using AllAlice.subtree_eval h b a

theorem AllBob.evalDepth_eq {k : ℕ} {P : Protocol A B Z}
    (h : AllBob k P) (a : A) (b : B) :
    Protocol.evalDepth P a b = k + Protocol.evalDepth
      (colSubtree k P (Protocol.prefixCodeRaw k (Protocol.swap P) b)) a b := by
  simpa only [colSubtree, Protocol.evalDepth_swap] using AllAlice.evalDepth_eq h b a

end EthInapproximability.CurrentPaper.ActualPrefix
