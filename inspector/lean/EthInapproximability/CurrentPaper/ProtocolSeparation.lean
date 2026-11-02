import EthInapproximability.CurrentPaper.Foundations
import NPCC.Control

/-!
# Current paper: first-message rigidity and protocol separation

Trace: `2026-09-22-complete-replacement-v8`,
`source/sections/02-separation.tex`, `lem:paper-two-test-rigidity` and
`thm:paper-classical-separation`.  This module uses the existing actual
protocol semantics and `NPCC.Protocol.FirstKRowBitsOn`: only reachable
rectangles are constrained, never unreachable branches of the protocol tree.

The generic lower-bound tests below quantify over actual row and column
subsets and actual minimum protocol depths.  They are the two hypotheses of
the paper's first-message lemma, not certificates containing its conclusion.

Public endpoints: `twoTestRigidity` and `classicalSeparation`. The latter is
the integer-`b`, `u = 2^k` specialization of the paper statement, using the
two one-copy bounds of `CurrentPaper.IsRobustAt`. No old `NPCC.IsRobust`
hypothesis or old classical-separation theorem is used. The imports supply
actual protocol/tree semantics, coordinate projection, and the elementary
dominant-block counting theorem. This is a finite protocol-separation result,
not an NP-hardness or ETH runtime theorem.
-/

open Workspace.Types.Protocol

noncomputable section

namespace NPCC

variable {A B A' B' Z : Type*}

/-- The surviving Alice-prefix property is preserved by input maps whose
images remain inside the current rectangle. No surjectivity is needed. -/
theorem Protocol.firstKRowBitsOn_pullback
    (φ : A' → A) (ψ : B' → B)
    (R : Finset A) (C : Finset B) (R' : Finset A') (C' : Finset B')
    (hR : ∀ a ∈ R', φ a ∈ R) (hC : ∀ b ∈ C', ψ b ∈ C)
    (k : ℕ) (P : Protocol A B Z)
    (h : Protocol.FirstKRowBitsOn R C k P) :
    Protocol.FirstKRowBitsOn R' C' k (Protocol.pullback φ ψ P) := by
  classical
  induction k generalizing R C R' C' P with
  | zero => trivial
  | succ k ih =>
      have empty_transfer (he : R = ∅ ∨ C = ∅) : R' = ∅ ∨ C' = ∅ := by
        rcases he with hr | hc
        · left
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro a ha
          simpa [hr] using hR a ha
        · right
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro b hb
          simpa [hc] using hC b hb
      cases P with
      | leaf z => exact empty_transfer h
      | bNode b l r => exact empty_transfer h
      | aNode a l r =>
          rcases h with ⟨hl, hr⟩
          constructor
          · apply ih (R.filter fun x => a x = false) C
              (R'.filter fun x => a (φ x) = false) C' ?_ hC l hl
            intro x hx
            rcases Finset.mem_filter.mp hx with ⟨hx, ha⟩
            exact Finset.mem_filter.mpr ⟨hR x hx, ha⟩
          · apply ih (R.filter fun x => a x = true) C
              (R'.filter fun x => a (φ x) = true) C' ?_ hC r hr
            intro x hx
            rcases Finset.mem_filter.mp hx with ⟨hx, ha⟩
            exact Finset.mem_filter.mpr ⟨hR x hx, ha⟩

theorem Protocol.restrictSub_eq_pullback
    (R : Finset A) (C : Finset B) (P : Protocol A B Z) :
    Protocol.restrictSub R C P = Protocol.pullback Subtype.val Subtype.val P := by
  induction P with
  | leaf z => rfl
  | aNode a l r ihl ihr => simp only [Protocol.restrictSub, Protocol.pullback, ihl, ihr]
  | bNode b l r ihl ihr => simp only [Protocol.restrictSub, Protocol.pullback, ihl, ihr]

/-- A row-prefix theorem stated on an ambient rectangle gives exactly the
usual row-prefix theorem for the protocol on the actual restricted matrix. -/
theorem Protocol.firstKRowBitsOn_restrictSub
    (R : Finset A) (C : Finset B) (k : ℕ) (P : Protocol A B Z)
    (h : Protocol.FirstKRowBitsOn R C k P) :
    Protocol.FirstKRowBitsOn Finset.univ Finset.univ k
      (Protocol.restrictSub R C P) := by
  rw [Protocol.restrictSub_eq_pullback]
  exact Protocol.firstKRowBitsOn_pullback Subtype.val Subtype.val R C
    Finset.univ Finset.univ (fun a _ => a.property) (fun b _ => b.property) k P h

/-- Identity on retained inputs, and a selected retained input elsewhere. -/
def retainedRetraction (R : Finset A) (hR : R.Nonempty) (a : A) : {a // a ∈ R} := by
  classical
  exact if ha : a ∈ R then ⟨a, ha⟩ else ⟨hR.choose, hR.choose_spec⟩

@[simp] theorem retainedRetraction_coe
    (R : Finset A) (hR : R.Nonempty) (a : {a // a ∈ R}) :
    retainedRetraction R hR a.val = a := by
  classical
  simp [retainedRetraction, a.property]

/-- Extend a subtype protocol to the ambient types without changing its tree.
Nonempty retained sets are needed only to choose values for discarded inputs. -/
def Protocol.extendSub
    (R : Finset A) (C : Finset B) (hR : R.Nonempty) (hC : C.Nonempty)
    (P : Protocol {a // a ∈ R} {b // b ∈ C} Z) : Protocol A B Z :=
  Protocol.pullback (retainedRetraction R hR) (retainedRetraction C hC) P

@[simp] theorem Protocol.cost_extendSub
    (R : Finset A) (C : Finset B) (hR : R.Nonempty) (hC : C.Nonempty)
    (P : Protocol {a // a ∈ R} {b // b ∈ C} Z) :
    (Protocol.extendSub R C hR hC P).cost = P.cost := by
  exact Protocol.pullback_cost _ _ P

@[simp] theorem Protocol.eval_extendSub
    (R : Finset A) (C : Finset B) (hR : R.Nonempty) (hC : C.Nonempty)
    (P : Protocol {a // a ∈ R} {b // b ∈ C} Z)
    (a : {a // a ∈ R}) (b : {b // b ∈ C}) :
    (Protocol.extendSub R C hR hC P).eval a.val b.val = P.eval a b := by
  simp [Protocol.extendSub]

@[simp] theorem Protocol.restrictSub_extendSub
    (R : Finset A) (C : Finset B) (hR : R.Nonempty) (hC : C.Nonempty)
    (P : Protocol {a // a ∈ R} {b // b ∈ C} Z) :
    Protocol.restrictSub R C (Protocol.extendSub R C hR hC P) = P := by
  induction P with
  | leaf z => rfl
  | aNode a l r ihl ihr =>
      change Protocol.aNode (fun x => a (retainedRetraction R hR x.val))
        (Protocol.restrictSub R C (Protocol.extendSub R C hR hC l))
        (Protocol.restrictSub R C (Protocol.extendSub R C hR hC r)) = _
      simp only [retainedRetraction_coe, ihl, ihr]
  | bNode b l r ihl ihr =>
      change Protocol.bNode (fun y => b (retainedRetraction C hC y.val))
        (Protocol.restrictSub R C (Protocol.extendSub R C hR hC l))
        (Protocol.restrictSub R C (Protocol.extendSub R C hR hC r)) = _
      simp only [retainedRetraction_coe, ihl, ihr]

theorem Protocol.firstKRowBitsOn_extendSub_iff
    (R : Finset A) (C : Finset B) (hR : R.Nonempty) (hC : C.Nonempty)
    (k : ℕ) (P : Protocol {a // a ∈ R} {b // b ∈ C} Z) :
    Protocol.FirstKRowBitsOn R C k (Protocol.extendSub R C hR hC P) ↔
      Protocol.FirstKRowBitsOn Finset.univ Finset.univ k P := by
  classical
  constructor
  · intro h
    simpa using Protocol.firstKRowBitsOn_restrictSub R C k
      (Protocol.extendSub R C hR hC P) h
  · intro h
    exact Protocol.firstKRowBitsOn_pullback
      (retainedRetraction R hR) (retainedRetraction C hC)
      Finset.univ Finset.univ R C (fun _ _ => Finset.mem_univ _)
      (fun _ _ => Finset.mem_univ _) k P h

/-- Input pullback preserves the row-prefix code, including its explicit junk
value on paths that meet a leaf or a Bob query too early. -/
theorem Protocol.prefixCodeRaw_pullback
    (φ : A' → A) (ψ : B' → B) (k : ℕ) (P : Protocol A B Z) (a : A') :
    Protocol.prefixCodeRaw k (Protocol.pullback φ ψ P) a =
      Protocol.prefixCodeRaw k P (φ a) := by
  induction k generalizing P with
  | zero => rfl
  | succ k ih =>
      cases P with
      | leaf z => rfl
      | bNode b l r => rfl
      | aNode q l r =>
          cases h : q (φ a) <;> simp [Protocol.pullback, Protocol.prefixCodeRaw, h, ih]

/-- The extended protocol has exactly the original row-prefix code on retained
rows; its column retraction cannot affect a row-prefix code. -/
theorem Protocol.prefixCodeRaw_extendSub
    (R : Finset A) (C : Finset B) (hR : R.Nonempty) (hC : C.Nonempty)
    (k : ℕ) (P : Protocol {a // a ∈ R} {b // b ∈ C} Z)
    (a : {a // a ∈ R}) :
    Protocol.prefixCodeRaw k (Protocol.extendSub R C hR hC P) a.val =
      Protocol.prefixCodeRaw k P a := by
  simp [Protocol.extendSub, Protocol.prefixCodeRaw_pullback]

/-- The ambient prefix code and the existing no-waste label coincide on every
retained row. They need not coincide on discarded rows, which no fiber counts. -/
theorem Protocol.prefixCodeRaw_extendSub_eq_prefixLabelFinQ
    {Q : ℕ} (R : Finset (Fin (2 ^ Q) × A)) (C : Finset B)
    (hR : R.Nonempty) (hC : C.Nonempty)
    (P : Protocol {a // a ∈ R} {b // b ∈ C} Z)
    (a : Fin (2 ^ Q) × A) (ha : a ∈ R) :
    Protocol.prefixCodeRaw Q (Protocol.extendSub R C hR hC P) a =
      Protocol.prefixLabelFinQ R P a := by
  classical
  simpa [Protocol.prefixLabelFinQ, ha] using
    Protocol.prefixCodeRaw_extendSub R C hR hC Q P ⟨a, ha⟩

/-- Consequently the actual ambient transcript fibers are exactly the existing
subtype-protocol fibers used by the no-waste theorem. -/
theorem Protocol.prefixFiber_extendSub_eq
    {Q : ℕ} (R : Finset (Fin (2 ^ Q) × A)) (C : Finset B)
    (hR : R.Nonempty) (hC : C.Nonempty)
    (P : Protocol {a // a ∈ R} {b // b ∈ C} Z) (j : Fin (2 ^ Q)) :
    R.filter (fun a => Protocol.prefixCodeRaw Q
      (Protocol.extendSub R C hR hC P) a = j) =
      Protocol.prefixFiber R (Protocol.prefixLabelFinQ R P) j := by
  apply Finset.filter_congr
  intro a ha
  rw [Protocol.prefixCodeRaw_extendSub_eq_prefixLabelFinQ R C hR hC P a ha]

end NPCC

namespace EthInapproximability.CurrentPaper.ProtocolSeparation

open NPCC Workspace.Types.CommComplexity Workspace.Types.Protocol
open Workspace.Types.Interlace

variable {A B I : Type*}

/-- A row block is specified by its label. This also handles rows that are
subtypes of a previously restricted matrix without changing their identity. -/
def HasRowsInBlocks [DecidableEq I] (label : A → I)
    (R : Finset A) (Q : Finset I) (T : ℕ) : Prop :=
  ∀ i ∈ Q, T ≤ (R.filter (fun a => label a = i)).card

/-- Literal restriction lower bound in the first-message tests. Densities
always use `C₀`, the same fixed original column set. -/
def BlockLowerBound [DecidableEq I] (F : A → B → Bool) (label : A → I)
    (C₀ : Finset B) (p T : ℕ) (h : ℝ) (L : ℕ) : Prop :=
  ∀ (R : Finset A) (C : Finset B) (Q : Finset I),
    C ⊆ C₀ → h * (C₀.card : ℝ) ≤ (C.card : ℝ) →
    p ≤ Q.card → HasRowsInBlocks label R Q T →
    L ≤ D (subgame F R C)

/-- An ambient protocol agreeing on a rectangle supplies an actual protocol
for its subgame, at no larger depth. -/
theorem restrictionCost_le_of_agrees (F : A → B → Bool)
    (R : Finset A) (C : Finset B) (P : Protocol A B Bool)
    (hP : ∀ a ∈ R, ∀ c ∈ C, P.eval a c = F a c) :
    D (subgame F R C) ≤ P.cost := by
  have hcomp : (Protocol.restrictSub R C P).Computes (subgame F R C) := by
    intro a c
    rw [Protocol.eval_restrictSub]
    exact hP a.1 a.2 c.1 c.2
  have hh := Nat.sInf_le (show (Protocol.restrictSub R C P).cost ∈
      AchievableCosts (subgame F R C) from ⟨_, rfl, hcomp⟩)
  simpa only [Protocol.cost_restrictSub] using hh

/-- A Boolean column query has a child keeping at least half the columns. -/
theorem exists_large_bool_child {α : Type*} (S : Finset α) (a : α → Bool) :
    ∃ β : Bool, S.card ≤ 2 * (S.filter (fun s => a s = β)).card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) (fun s => a s = true)
  have hfalse : S.filter (fun s => ¬ a s = true) = S.filter (fun s => a s = false) := by
    ext s
    simp
  rw [hfalse] at hsplit
  by_cases hh : S.card ≤ 2 * (S.filter (fun s => a s = true)).card
  · exact ⟨true, hh⟩
  · exact ⟨false, by omega⟩

/-- Each row block can be assigned to one Boolean branch that retains at least
half of its rows, with the ceiling encoded by `2 * Tnext ≤ T + 1`. The assigned
block sets are disjoint, even when both branches retain enough rows. -/
theorem row_block_majority_partition {A ι : Type*} [DecidableEq ι]
    (R : Finset A) (Q : Finset ι) (label : A → ι) (a : A → Bool)
    (T Tnext : ℕ)
    (hrows : ∀ i ∈ Q, T ≤ (R.filter (fun x => label x = i)).card)
    (hhalf : 2 * Tnext ≤ T + 1) :
    ∃ Q0 Q1 : Finset ι,
      Q0 ⊆ Q ∧ Q1 ⊆ Q ∧ Disjoint Q0 Q1 ∧ Q0 ∪ Q1 = Q ∧
      Q0.card + Q1.card = Q.card ∧
      (∀ i ∈ Q0,
        Tnext ≤ ((R.filter (fun x => a x = false)).filter
          (fun x => label x = i)).card) ∧
      (∀ i ∈ Q1,
        Tnext ≤ ((R.filter (fun x => a x = true)).filter
          (fun x => label x = i)).card) := by
  classical
  let good : ι → Prop := fun i =>
    Tnext ≤ ((R.filter (fun x => a x = false)).filter
      (fun x => label x = i)).card
  let Q0 := Q.filter good
  let Q1 := Q.filter (fun i => ¬ good i)
  refine ⟨Q0, Q1, Finset.filter_subset _ _, Finset.filter_subset _ _, ?_, ?_,
    ?_, ?_, ?_⟩
  · exact Finset.disjoint_filter_filter_not _ _ _
  · exact Finset.filter_union_filter_not_eq _ _
  · exact Finset.card_filter_add_card_filter_not _
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · intro i hi
    have hbad := (Finset.mem_filter.mp hi).2
    have hrow := hrows i (Finset.mem_filter.mp hi).1
    have hsplit :
        ((R.filter (fun x => a x = false)).filter (fun x => label x = i)).card +
        ((R.filter (fun x => a x = true)).filter (fun x => label x = i)).card =
        (R.filter (fun x => label x = i)).card := by
      simpa [Finset.filter_filter, and_comm, and_left_comm, and_assoc] using
        (Finset.card_filter_add_card_filter_not
          (s := R.filter (fun x => label x = i)) (p := fun x => a x = false))
    change ¬ Tnext ≤ _ at hbad
    omega

/-- The two-test induction with an explicit row-threshold sequence.  The
condition on successive thresholds is precisely majority rounding.  Both
tests are genuine universal restriction lower bounds, as in the paper. -/
theorem twoTestPrefix_of_thresholds [DecidableEq I]
    (F : A → B → Bool) (label : A → I) (C₀ : Finset B)
    (k B₀ : ℕ) (T : ℕ → ℕ) (h : ℝ) (hB : 1 ≤ B₀) (_hh : 0 ≤ h)
    (hhalf : ∀ d, d < k → 2 * T (d + 1) ≤ T d + 1)
    (hBob : ∀ d, d < k → BlockLowerBound F label C₀
      (2 ^ (k - d)) (T d) (h / 2) (B₀ + (k - d)))
    (hAlice : ∀ d, d + 1 < k → BlockLowerBound F label C₀
      (2 ^ (k - d - 1) + 1) (T (d + 1)) h (B₀ + (k - d))) :
    ∀ (r d : ℕ), d + r = k →
      ∀ (R : Finset A) (C : Finset B) (Q : Finset I) (P : Protocol A B Bool),
      C ⊆ C₀ → h * (C₀.card : ℝ) ≤ (C.card : ℝ) →
      Q.card = 2 ^ r → HasRowsInBlocks label R Q (T d) →
      P.cost ≤ B₀ + r →
      (∀ a ∈ R, ∀ c ∈ C, P.eval a c = F a c) →
      Protocol.FirstKRowBitsOn R C r P := by
  classical
  intro r
  induction r with
  | zero => intros; trivial
  | succ r ih =>
    intro d hdr R C Q P hCsub hCden hQ hR hcost hcomp
    have hd : d < k := by omega
    have hkd : k - d = r + 1 := by omega
    have hkd1 : k - d - 1 = r := by omega
    have hlow : B₀ + (r + 1) ≤ D (subgame F R C) := by
      have hden : h / 2 * (C₀.card : ℝ) ≤ (C.card : ℝ) := by
        have hc0 : (0 : ℝ) ≤ C₀.card := by positivity
        nlinarith
      simpa only [hkd] using hBob d hd R C Q hCsub hden (by simp [hkd, hQ]) hR
    cases P with
    | leaf z =>
      have hup := restrictionCost_le_of_agrees F R C (Protocol.leaf z) hcomp
      simp only [Protocol.cost] at hup
      omega
    | bNode a l p =>
      obtain ⟨β, hlarge⟩ := exists_large_bool_child C a
      let C' := C.filter (fun c => a c = β)
      let P' := if β then p else l
      have hcost' : P'.cost ≤ B₀ + r := by
        have hp' : P'.cost ≤ max l.cost p.cost := by
          cases β <;> simp [P']
        simp only [Protocol.cost] at hcost
        omega
      have hcomp' : ∀ x ∈ R, ∀ c ∈ C', P'.eval x c = F x c := by
        intro x hx c hc
        have hc' := Finset.mem_filter.mp hc
        have hp := hcomp x hx c hc'.1
        cases β <;> simpa [Protocol.eval, P', hc'.2] using hp
      have hden : h / 2 * (C₀.card : ℝ) ≤ (C'.card : ℝ) := by
        have hlargeR : (C.card : ℝ) ≤ 2 * (C'.card : ℝ) := by exact_mod_cast hlarge
        linarith
      have hl := hBob d hd R C' Q
        (Finset.Subset.trans (Finset.filter_subset _ _) hCsub) hden
        (by simp [hkd, hQ]) hR
      have hu := restrictionCost_le_of_agrees F R C' P' hcomp'
      rw [hkd] at hl
      omega
    | aNode a l p =>
      have hcl : l.cost ≤ B₀ + r := by
        simp only [Protocol.cost] at hcost
        omega
      have hcp : p.cost ≤ B₀ + r := by
        simp only [Protocol.cost] at hcost
        omega
      have hpl : ∀ x ∈ R.filter (fun x => a x = false), ∀ c ∈ C,
          l.eval x c = F x c := by
        intro x hx c hc
        have hx' := Finset.mem_filter.mp hx
        simpa only [Protocol.eval, hx'.2, Bool.false_eq_true, ↓reduceIte] using
          hcomp x hx'.1 c hc
      have hpp : ∀ x ∈ R.filter (fun x => a x = true), ∀ c ∈ C,
          p.eval x c = F x c := by
        intro x hx c hc
        have hx' := Finset.mem_filter.mp hx
        simpa only [Protocol.eval, hx'.2, ↓reduceIte] using hcomp x hx'.1 c hc
      by_cases hr : r = 0
      · rw [hr]
        exact ⟨trivial, trivial⟩
      have hda : d + 1 < k := by omega
      obtain ⟨Q0, Q1, _, _, _, _, hsum, hR0, hR1⟩ :=
        row_block_majority_partition R Q label a (T d) (T (d + 1)) hR (hhalf d hd)
      have hQ0 : Q0.card ≤ 2 ^ r := by
        by_contra hc
        have hl := hAlice d hda (R.filter (fun x => a x = false)) C Q0
          hCsub hCden (by rw [hkd1]; omega) hR0
        have hu := restrictionCost_le_of_agrees F _ C l hpl
        rw [hkd] at hl
        omega
      have hQ1 : Q1.card ≤ 2 ^ r := by
        by_contra hc
        have hl := hAlice d hda (R.filter (fun x => a x = true)) C Q1
          hCsub hCden (by rw [hkd1]; omega) hR1
        have hu := restrictionCost_le_of_agrees F _ C p hpp
        rw [hkd] at hl
        omega
      have heq0 : Q0.card = 2 ^ r := by rw [hQ, pow_succ] at hsum; omega
      have heq1 : Q1.card = 2 ^ r := by rw [hQ, pow_succ] at hsum; omega
      exact ⟨ih (d + 1) (by omega) _ C Q0 l hCsub hCden heq0 hR0 hcl hpl,
        ih (d + 1) (by omega) _ C Q1 p hCsub hCden heq1 hR1 hcp hpp⟩

/-- Ceiling-safe halving, with a real nonnegative population. -/
theorem ceil_half_threshold (t : ℝ) (ht : 0 ≤ t) :
    2 * ⌈t / 2⌉₊ ≤ ⌈t⌉₊ + 1 := by
  have hlt := Nat.ceil_lt_add_one (show 0 ≤ t / 2 by positivity)
  have hle := Nat.le_ceil t
  have hh : (2 * ⌈t / 2⌉₊ : ℕ) < ⌈t⌉₊ + 2 := by
    have hr : (2 : ℝ) * (⌈t / 2⌉₊ : ℝ) < (⌈t⌉₊ : ℝ) + 2 := by linarith
    exact_mod_cast hr
  omega

/-- The paper's exact ceiling threshold after `d` Alice bits. -/
noncomputable def rowThreshold (T₀ d : ℕ) : ℕ :=
  ⌈(T₀ : ℝ) / (2 : ℝ) ^ d⌉₊

theorem rowThreshold_half (T₀ d : ℕ) :
    2 * rowThreshold T₀ (d + 1) ≤ rowThreshold T₀ d + 1 := by
  unfold rowThreshold
  rw [pow_succ, ← div_div]
  exact ceil_half_threshold _ (by positivity)

/-- First assertion of `lem:paper-two-test-rigidity`, with its exact integer
thresholds and both universal lower-bound tests, over reachable executions. -/
theorem twoTestAlicePrefix [DecidableEq I]
    (F : A → B → Bool) (label : A → I) (C₀ : Finset B)
    (k B₀ T₀ : ℕ) (h : ℝ) (hB : 1 ≤ B₀) (hh : 0 ≤ h)
    (hBob : ∀ d, d < k → BlockLowerBound F label C₀
      (2 ^ (k - d)) (rowThreshold T₀ d) (h / 2) (B₀ + (k - d)))
    (hAlice : ∀ d, d + 1 < k → BlockLowerBound F label C₀
      (2 ^ (k - d - 1) + 1) (rowThreshold T₀ (d + 1)) h (B₀ + (k - d)))
    (R : Finset A) (C : Finset B) (Q : Finset I) (P : Protocol A B Bool)
    (hCsub : C ⊆ C₀) (hCden : h * (C₀.card : ℝ) ≤ (C.card : ℝ))
    (hQ : Q.card = 2 ^ k) (hR : HasRowsInBlocks label R Q T₀)
    (hcost : P.cost ≤ B₀ + k)
    (hcomp : ∀ a ∈ R, ∀ c ∈ C, P.eval a c = F a c) :
    Protocol.FirstKRowBitsOn R C k P := by
  apply twoTestPrefix_of_thresholds F label C₀ k B₀ (rowThreshold T₀) h hB hh
    (fun d _ => rowThreshold_half T₀ d) hBob hAlice k 0 (by omega)
    R C Q P hCsub hCden hQ ?_ hcost hcomp
  simpa [rowThreshold] using hR

/-- The residual below a reachable Alice-only prefix computes its actual
rectangle with at most the unspent budget. -/
theorem prefixRectangleCost_le (F : A → B → Bool) (R : Finset A) (C : Finset B)
    (P : Protocol A B Bool) (k : ℕ) (j : Fin (2 ^ k))
    (hprefix : Protocol.FirstKRowBitsOn R C k P)
    (hRj : (R.filter (fun a => Protocol.prefixCodeRaw k P a = j)).Nonempty)
    (hC : C.Nonempty)
    (hcomp : ∀ a ∈ R, ∀ c ∈ C, P.eval a c = F a c) :
    D (subgame F (R.filter (fun a => Protocol.prefixCodeRaw k P a = j)) C)
      ≤ P.cost - k := by
  have hc := Protocol.rowSubtreeAtRaw_cost_le_of_active R C k P j hprefix hRj hC
  refine (restrictionCost_le_of_agrees F _ C (Protocol.rowSubtreeAtRaw k P j) ?_).trans hc
  intro a ha c hcc
  have ha' := Finset.mem_filter.mp ha
  rw [Protocol.eval_rowSubtreeAtRaw_eq_of_prefix R C k P j hprefix ha'.1 hcc ha'.2]
  exact hcomp a ha'.1 c hcc

/-- The near-separation conclusion of the first-message lemma.  The labels
are the actual row transcripts of the given protocol.  The two-block test
rules out two heavy blocks in one actual residual rectangle. -/
theorem noWaste_of_twoBlock_test {X Y : Type*} {k B₀ T₀ τ : ℕ}
    (F : (Fin (2 ^ k) × X) → Y → Bool)
    (R : Finset (Fin (2 ^ k) × X)) (C C₀ : Finset Y)
    (P : Protocol (Fin (2 ^ k) × X) Y Bool) (h : ℝ)
    (hprefix : Protocol.FirstKRowBitsOn R C k P)
    (hR : IsEquipartitionedGE R Finset.univ T₀)
    (hC : C.Nonempty) (hCsub : C ⊆ C₀)
    (hCden : h * (C₀.card : ℝ) ≤ (C.card : ℝ))
    (hcost : P.cost ≤ B₀ + k)
    (hcomp : ∀ a ∈ R, ∀ c ∈ C, P.eval a c = F a c)
    (hτ : 1 ≤ τ) (hgap : 2 ^ k * τ < T₀)
    (hpair : BlockLowerBound F Prod.fst C₀ 2 τ h (B₀ + 1)) :
    NoWasteConclusion (Finset.univ : Finset (Fin (2 ^ k))) R
      (Protocol.prefixCodeRaw k P) T₀ τ := by
  classical
  apply no_waste_row_partition Finset.univ R T₀ τ (2 ^ k) (by simp)
    (Protocol.prefixCodeRaw k P) hR (by simpa using hgap)
  intro j
  rintro ⟨i₀, _, i₁, _, hne, h₀, h₁⟩
  let Rj := R.filter (fun a => Protocol.prefixCodeRaw k P a = j)
  have hRj : Rj.Nonempty := by
    have hh : 0 < (R.filter (fun a => Protocol.prefixCodeRaw k P a = j ∧ a.1 = i₀)).card := by
      omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hh
    refine ⟨a, ?_⟩
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2.1⟩
  have hblocks : HasRowsInBlocks Prod.fst Rj ({i₀, i₁} : Finset _) τ := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · simpa only [Rj, Finset.filter_filter] using h₀
    · simpa only [Rj, Finset.filter_filter] using h₁
  have hl := hpair Rj C {i₀, i₁} hCsub hCden (by simp [hne]) hblocks
  have hu := prefixRectangleCost_le F R C P k j hprefix hRj hC hcomp
  change D (subgame F Rj C) ≤ _ at hu
  omega

/-- Exact number and reachability of the prefix rectangles.  `NoWasteConclusion`
already gives unique block labels and the stated row-loss bound; the strict
integer gap makes each of the `2^k` labelled rectangles nonempty. -/
theorem all_prefix_rectangles_nonempty {X : Type*} {k T₀ τ : ℕ}
    (R : Finset (Fin (2 ^ k) × X)) (lab : (Fin (2 ^ k) × X) → Fin (2 ^ k))
    (hgap : 2 ^ k * τ < T₀)
    (hsep : NoWasteConclusion (Finset.univ : Finset (Fin (2 ^ k))) R lab T₀ τ) :
    ∀ j, (R.filter (fun a => lab a = j)).Nonempty := by
  intro j
  obtain ⟨i, ⟨_, hi, _⟩, _⟩ := hsep j
  have hle : (2 ^ k - 1) * τ ≤ 2 ^ k * τ := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hpos : 0 < T₀ - (2 ^ k - 1) * τ := by omega
  simp only [Finset.card_univ, Fintype.card_fin] at hi
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (lt_of_lt_of_le hpos hi)
  exact ⟨a, Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2.1⟩⟩

/-- Complete `lem:paper-two-test-rigidity` for an ambient protocol agreeing
on its retained rectangle: the all-Alice prefix, unique dominant block in
each terminal rectangle, and nonemptiness of all `2^k` rectangles. -/
theorem twoTestRigidity {X Y : Type*} (k B₀ T₀ τ : ℕ)
    (F : (Fin (2 ^ k) × X) → Y → Bool) (C₀ : Finset Y) (h : ℝ)
    (hB : 1 ≤ B₀) (hh : 0 ≤ h)
    (hBob : ∀ d, d < k → BlockLowerBound F Prod.fst C₀
      (2 ^ (k - d)) (rowThreshold T₀ d) (h / 2) (B₀ + (k - d)))
    (hAlice : ∀ d, d + 1 < k → BlockLowerBound F Prod.fst C₀
      (2 ^ (k - d - 1) + 1) (rowThreshold T₀ (d + 1)) h (B₀ + (k - d)))
    (hpair : BlockLowerBound F Prod.fst C₀ 2 τ h (B₀ + 1))
    (hτ : 1 ≤ τ) (hgap : 2 ^ k * τ < T₀)
    (R : Finset (Fin (2 ^ k) × X)) (C : Finset Y)
    (P : Protocol (Fin (2 ^ k) × X) Y Bool)
    (hC : C.Nonempty) (hCsub : C ⊆ C₀)
    (hCden : h * (C₀.card : ℝ) ≤ (C.card : ℝ))
    (hR : IsEquipartitionedGE R Finset.univ T₀)
    (hcost : P.cost ≤ B₀ + k)
    (hcomp : ∀ a ∈ R, ∀ c ∈ C, P.eval a c = F a c) :
    Protocol.FirstKRowBitsOn R C k P ∧
    NoWasteConclusion (Finset.univ : Finset (Fin (2 ^ k))) R
      (Protocol.prefixCodeRaw k P) T₀ τ ∧
    ∀ j, (R.filter (fun a => Protocol.prefixCodeRaw k P a = j)).Nonempty := by
  have hprefix := twoTestAlicePrefix F Prod.fst C₀ k B₀ T₀ h hB hh
    hBob hAlice R C Finset.univ P hCsub hCden (by simp) hR hcost hcomp
  have hsep := noWaste_of_twoBlock_test F R C C₀ P h hprefix hR hC hCsub hCden
    hcost hcomp hτ hgap hpair
  exact ⟨hprefix, hsep, all_prefix_rectangles_nonempty R _ hgap hsep⟩

/-- It suffices to check restrictions on exactly the requested number of
blocks: for a larger block set, keep a subset of the labels, not new rows. -/
theorem blockLowerBound_of_exact [DecidableEq I]
    (F : A → B → Bool) (label : A → I) (C₀ : Finset B) (p T : ℕ) (h : ℝ) (L : ℕ)
    (htest : ∀ (R : Finset A) (C : Finset B) (Q : Finset I),
      C ⊆ C₀ → h * (C₀.card : ℝ) ≤ (C.card : ℝ) →
      Q.card = p → HasRowsInBlocks label R Q T → L ≤ D (subgame F R C)) :
    BlockLowerBound F label C₀ p T h L := by
  intro R C Q hC hden hp hR
  obtain ⟨Q', hsub, hcard⟩ := Finset.exists_subset_card_eq hp
  exact htest R C Q' hC hden hcard (fun i hi => hR i (hsub hi))

/-! ## Classical lower-bound tests

Projection is applied to the actual selected columns, which need not be a
product. These tests consume the current two-bound amplification theorem.
-/

namespace ClassicalTests

theorem projected_subgame_le {X Y : Type*}
    {f : X → Y → Bool} {q r : ℕ}
    {R : Finset (Fin q × X)} {C : Finset (Fin q → Y)}
    {R' : Finset (Fin r × X)} {C' : Finset (Fin r → Y)}
    (emb : Fin r → Fin q)
    (hRows : ∀ a ∈ R', (emb a.1, a.2) ∈ R)
    (hCols : ∀ c' ∈ C', ∃ c ∈ C, ∀ j : Fin r, c' j = c (emb j)) :
    D (subgame (interlaceFun f r) R' C') ≤
      D (subgame (interlaceFun f q) R C) := by
  classical
  let ρ : {a // a ∈ R'} → {a // a ∈ R} :=
    fun a => ⟨(emb a.1.1, a.1.2), hRows a.1 a.2⟩
  let σ : {c // c ∈ C'} → {c // c ∈ C} :=
    fun c => ⟨Classical.choose (hCols c.1 c.2),
      (Classical.choose_spec (hCols c.1 c.2)).1⟩
  have hσ (c : {c // c ∈ C'}) (j : Fin r) : c.1 j = (σ c).1 (emb j) :=
    (Classical.choose_spec (hCols c.1 c.2)).2 j
  have heq : subgame (interlaceFun f r) R' C' =
      fun a c => subgame (interlaceFun f q) R C (ρ a) (σ c) := by
    funext a c
    simp only [subgame, interlaceFun]
    exact congrArg (fun y => f a.1.2 y) (hσ c a.1.1)
  rw [heq]
  exact D_mapNodes_le (subgame (interlaceFun f q) R C) ρ σ

theorem lowerBound_of_projection {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) {q r B T : ℕ} {x z : ℝ}
    (Q : Finset (Fin q)) (R : Finset (Fin q × X)) (C : Finset (Fin q → Y))
    (hQr : Q.card = r) (hr : 0 < r)
    (hrow : IsEquipartitionedGE R Q T)
    (hcol : ⌈((Fintype.card Y : ℝ) ^ q) * z⌉₊ ≤ C.card)
    (hxT : ⌈(Fintype.card X : ℝ) * x⌉₊ ≤ T)
    (hB : B ≤ Dfamily (interlaceFun f r) (bracketGE X Y r x z)) :
    B ≤ D (subgame (interlaceFun f q) R C) := by
  classical
  let e : Fin r ≃ {i // i ∈ Q} :=
    (Fintype.equivFinOfCardEq (by simpa using hQr)).symm
  obtain ⟨RC', hmem, hrows, hcols⟩ :=
    coord_projection hr e hrow hcol hxT
  have hmemcost : Dfamily (interlaceFun f r) (bracketGE X Y r x z) ≤
      D (subgame (interlaceFun f r) RC'.1 RC'.2) := by
    unfold Dfamily
    exact Nat.sInf_le ⟨RC', hmem, rfl⟩
  exact hB.trans (hmemcost.trans (projected_subgame_le
    (fun j => (e j).val) hrows hcols))

theorem powerOfTwoTest {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] {f : X → Y → Bool} {b q k T : ℕ}
    (hrobust : IsRobustAt f b) (hk : 1 ≤ k) (hkb : k ≤ b)
    (Q : Finset (Fin q)) (R : Finset (Fin q × X)) (C : Finset (Fin q → Y))
    (hQr : Q.card = 2 ^ k) (hrow : IsEquipartitionedGE R Q T)
    (hcol : ⌈((Fintype.card Y : ℝ) ^ q) * (9 / 25)⌉₊ ≤ C.card)
    (hxT : ⌈(Fintype.card X : ℝ) * (2 : ℝ) ^ ((k : ℝ) - (b : ℝ))⌉₊ ≤ T) :
    D f + k ≤ D (subgame (interlaceFun f q) R C) := by
  exact lowerBound_of_projection f Q R C hQr (by positivity) hrow hcol hxT
    (hrobust.classicalAmplification k hk hkb).2

theorem oddBlockTest {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] {f : X → Y → Bool} {b q k T : ℕ}
    (hrobust : IsRobustAt f b) (hk : 1 ≤ k) (hkb : k ≤ b)
    (Q : Finset (Fin q)) (R : Finset (Fin q × X)) (C : Finset (Fin q → Y))
    (hQr : Q.card = 2 ^ (k - 1) + 1) (hrow : IsEquipartitionedGE R Q T)
    (hcol : ⌈((Fintype.card Y : ℝ) ^ q) * (9 / 25)⌉₊ ≤ C.card)
    (hxT : ⌈(Fintype.card X : ℝ) * (2 : ℝ) ^ ((k : ℝ) - (b : ℝ))⌉₊ ≤ T) :
    D f + k ≤ D (subgame (interlaceFun f q) R C) := by
  apply lowerBound_of_projection f Q R C hQr (by positivity) hrow hcol hxT
  exact (hrobust.classicalAmplification k hk hkb).1.trans (min_le_left _ _)

theorem divided_row_threshold {m T d : ℕ} {a x : ℝ}
    (hscaled : a * (2 : ℝ) ^ d ≤ x) (hT : ⌈(m : ℝ) * x⌉₊ ≤ T) :
    ⌈(m : ℝ) * a⌉₊ ≤ ⌈(T : ℝ) / (2 : ℝ) ^ d⌉₊ := by
  apply Nat.ceil_mono
  apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ d)).2
  calc
    (m : ℝ) * a * (2 : ℝ) ^ d = (m : ℝ) * (a * (2 : ℝ) ^ d) := by ring
    _ ≤ (m : ℝ) * x := mul_le_mul_of_nonneg_left hscaled (by positivity)
    _ ≤ (⌈(m : ℝ) * x⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ T := by exact_mod_cast hT

theorem remaining_scale {k d b : ℕ} (hd : d ≤ k) :
    (2 : ℝ) ^ (((k - d : ℕ) : ℝ) - (b : ℝ)) * (2 : ℝ) ^ d =
      (2 : ℝ) ^ ((k : ℝ) - (b : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  rw [Nat.cast_sub hd]
  ring

/-- The actual first test at depth d.  The row threshold is rounded upward
exactly as in the manuscript, and the column count is measured in the original
q-fold column universe, not in its selected projection. -/
theorem classicalFirstTest {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] {f : X → Y → Bool} {b q k d T₀ : ℕ}
    {x h : ℝ} (hrobust : IsRobustAt f b) (hd : d < k) (hkb : k ≤ b)
    (hbase : (2 : ℝ) ^ ((k : ℝ) - (b : ℝ)) ≤ x)
    (hT₀ : ⌈(Fintype.card X : ℝ) * x⌉₊ ≤ T₀)
    (hh : (9 / 25 : ℝ) ≤ h / 2)
    (Q : Finset (Fin q)) (R : Finset (Fin q × X)) (C : Finset (Fin q → Y))
    (hQr : Q.card = 2 ^ (k - d))
    (hrow : IsEquipartitionedGE R Q ⌈(T₀ : ℝ) / (2 : ℝ) ^ d⌉₊)
    (hcol : ⌈((Fintype.card Y : ℝ) ^ q) * (h / 2)⌉₊ ≤ C.card) :
    D f + (k - d) ≤ D (subgame (interlaceFun f q) R C) := by
  apply powerOfTwoTest hrobust (by omega) (by omega) Q R C hQr hrow
  · exact (Nat.ceil_mono (mul_le_mul_of_nonneg_left hh (by positivity))).trans hcol
  · apply divided_row_threshold (hT := hT₀)
    rw [remaining_scale (Nat.le_of_lt hd)]
    exact hbase

/-- The actual second test: one block more than half, with the threshold
after one further row split.  The stronger base scale is precisely the
factor-two slack derived from the strict row-count hypothesis in v8. -/
theorem classicalSecondTest {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] {f : X → Y → Bool} {b q k d T₀ : ℕ}
    {x h : ℝ} (hrobust : IsRobustAt f b) (hd : d + 1 < k) (hkb : k ≤ b)
    (hbase : 2 * (2 : ℝ) ^ ((k : ℝ) - (b : ℝ)) ≤ x)
    (hT₀ : ⌈(Fintype.card X : ℝ) * x⌉₊ ≤ T₀)
    (hh : (9 / 25 : ℝ) ≤ h)
    (Q : Finset (Fin q)) (R : Finset (Fin q × X)) (C : Finset (Fin q → Y))
    (hQr : Q.card = 2 ^ (k - d - 1) + 1)
    (hrow : IsEquipartitionedGE R Q ⌈(T₀ : ℝ) / (2 : ℝ) ^ (d + 1)⌉₊)
    (hcol : ⌈((Fintype.card Y : ℝ) ^ q) * h⌉₊ ≤ C.card) :
    D f + (k - d) ≤ D (subgame (interlaceFun f q) R C) := by
  apply oddBlockTest hrobust (by omega) (by omega) Q R C hQr hrow
  · exact (Nat.ceil_mono (mul_le_mul_of_nonneg_left hh (by positivity))).trans hcol
  · apply divided_row_threshold (hT := hT₀)
    calc
      (2 : ℝ) ^ (((k - d : ℕ) : ℝ) - (b : ℝ)) * (2 : ℝ) ^ (d + 1) =
          2 * ((2 : ℝ) ^ (((k - d : ℕ) : ℝ) - (b : ℝ)) * (2 : ℝ) ^ d) := by
            rw [pow_succ]; ring
      _ = 2 * (2 : ℝ) ^ ((k : ℝ) - (b : ℝ)) := by
        rw [remaining_scale (by omega : d ≤ k)]
      _ ≤ x := hbase

theorem strict_row_slack {m u : ℕ} {a x : ℝ}
    (h : u * ⌈(m : ℝ) * a⌉₊ < ⌈(m : ℝ) * x⌉₊) :
    (u : ℝ) * a < x := by
  by_contra hnot
  have hxa : x ≤ (u : ℝ) * a := le_of_not_gt hnot
  have hmx : (m : ℝ) * x ≤ (u * ⌈(m : ℝ) * a⌉₊ : ℕ) := by
    calc
      (m : ℝ) * x ≤ (m : ℝ) * ((u : ℝ) * a) :=
        mul_le_mul_of_nonneg_left hxa (by positivity)
      _ = (u : ℝ) * ((m : ℝ) * a) := by ring
      _ ≤ (u : ℝ) * (⌈(m : ℝ) * a⌉₊ : ℝ) :=
        mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by positivity)
      _ = (u * ⌈(m : ℝ) * a⌉₊ : ℕ) := by push_cast; rfl
  exact (not_le_of_gt h) (Nat.ceil_le.mpr hmx)

theorem strict_classical_row_slack {m k b : ℕ} {x : ℝ}
    (h : 2 ^ k * ⌈(m : ℝ) * (2 : ℝ) ^ (1 - (b : ℝ))⌉₊ <
      ⌈(m : ℝ) * x⌉₊) :
    2 * (2 : ℝ) ^ ((k : ℝ) - (b : ℝ)) < x := by
  have hh := strict_row_slack h
  have heq : ((2 ^ k : ℕ) : ℝ) * (2 : ℝ) ^ (1 - (b : ℝ)) =
      2 * (2 : ℝ) ^ ((k : ℝ) - (b : ℝ)) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    calc
      (2 : ℝ) ^ ((k : ℝ) + (1 - (b : ℝ))) =
          (2 : ℝ) ^ (1 + ((k : ℝ) - (b : ℝ))) := by congr 1; ring
      _ = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ ((k : ℝ) - (b : ℝ)) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ = 2 * (2 : ℝ) ^ ((k : ℝ) - (b : ℝ)) := by rw [Real.rpow_one]
  rwa [heq] at hh

theorem classical_scale_in_range {k b : ℕ} {x : ℝ}
    (hslack : 2 * (2 : ℝ) ^ ((k : ℝ) - (b : ℝ)) < x) (hx : x ≤ 1) :
    k ≤ b := by
  by_contra hnot
  have hbk : b ≤ k := by omega
  have hexp : (0 : ℝ) ≤ (k : ℝ) - (b : ℝ) := by
    have hbkr : (b : ℝ) ≤ k := by exact_mod_cast hbk
    linarith
  have hone : (1 : ℝ) ≤ (2 : ℝ) ^ ((k : ℝ) - (b : ℝ)) := by
    calc
      (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
      _ ≤ (2 : ℝ) ^ ((k : ℝ) - (b : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  linarith

theorem lowerBound_of_projection_atLeast {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) {q r B T : ℕ} {x z : ℝ}
    (Q : Finset (Fin q)) (R : Finset (Fin q × X)) (C : Finset (Fin q → Y))
    (hQr : r ≤ Q.card) (hr : 0 < r)
    (hrow : IsEquipartitionedGE R Q T)
    (hcol : ⌈((Fintype.card Y : ℝ) ^ q) * z⌉₊ ≤ C.card)
    (hxT : ⌈(Fintype.card X : ℝ) * x⌉₊ ≤ T)
    (hB : B ≤ Dfamily (interlaceFun f r) (bracketGE X Y r x z)) :
    B ≤ D (subgame (interlaceFun f q) R C) := by
  classical
  obtain ⟨Q', hsub, hcard⟩ := Finset.exists_subset_card_eq hQr
  exact lowerBound_of_projection f Q' R C hcard hr
    (fun i hi => hrow i (hsub hi)) hcol hxT hB

end ClassicalTests

/-- Classical separation using exactly the NEW two-bound robustness
predicate.  This ambient-protocol form makes no assumptions away from the
retained rectangle.  The power of two is written as `2^k` rather than using
a logarithm; all row thresholds are literal ceilings.
Source: `thm:paper-classical-separation`. -/
theorem classicalSeparationOn {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] {f : X → Y → Bool} {b k : ℕ} {x z : ℝ}
    (hrobust : IsRobustAt f b) (_hk : 1 ≤ k) (hx1 : x ≤ 1)
    (hz : (18 / 25 : ℝ) ≤ z)
    (hgap : 2 ^ k * ⌈(Fintype.card X : ℝ) * (2 : ℝ) ^ (1 - (b : ℝ))⌉₊ <
      ⌈(Fintype.card X : ℝ) * x⌉₊)
    (R : Finset (Fin (2 ^ k) × X)) (C : Finset (Fin (2 ^ k) → Y))
    (hRC : (R, C) ∈ bracketGE X Y (2 ^ k) x z)
    (P : Protocol (Fin (2 ^ k) × X) (Fin (2 ^ k) → Y) Bool)
    (hcost : P.cost ≤ D f + k)
    (hcomp : ∀ a ∈ R, ∀ c ∈ C, P.eval a c = interlaceFun f (2 ^ k) a c) :
    Protocol.FirstKRowBitsOn R C k P ∧
    NoWasteConclusion (Finset.univ : Finset (Fin (2 ^ k))) R
      (Protocol.prefixCodeRaw k P) ⌈(Fintype.card X : ℝ) * x⌉₊
      ⌈(Fintype.card X : ℝ) * (2 : ℝ) ^ (1 - (b : ℝ))⌉₊ ∧
    ∀ j, (R.filter (fun a => Protocol.prefixCodeRaw k P a = j)).Nonempty := by
  classical
  let C₀ : Finset (Fin (2 ^ k) → Y) := Finset.univ
  let T₀ := ⌈(Fintype.card X : ℝ) * x⌉₊
  let τ := ⌈(Fintype.card X : ℝ) * (2 : ℝ) ^ (1 - (b : ℝ))⌉₊
  have hslack := ClassicalTests.strict_classical_row_slack hgap
  have hkb := ClassicalTests.classical_scale_in_range hslack hx1
  have hbase : (2 : ℝ) ^ ((k : ℝ) - (b : ℝ)) ≤ x := by
    have hp := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) ((k : ℝ) - (b : ℝ))
    linarith
  have hC₀ : (C₀.card : ℝ) = (Fintype.card Y : ℝ) ^ (2 ^ k) := by
    simp [C₀]
  have hCden : z * (C₀.card : ℝ) ≤ (C.card : ℝ) := by
    have hh : ((Fintype.card Y : ℝ) ^ (2 ^ k)) * z ≤ (C.card : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hRC.2)
    simpa only [hC₀, mul_comm] using hh
  have hCn : C.Nonempty := by
    have hc0 : (0 : ℝ) < (C₀.card : ℝ) := by
      rw [hC₀]
      exact pow_pos (by exact_mod_cast Fintype.card_pos (α := Y)) _
    have hz0 : 0 < z := by linarith
    have hcpos : (0 : ℝ) < (C.card : ℝ) := (mul_pos hz0 hc0).trans_le hCden
    exact Finset.card_pos.mp (by exact_mod_cast hcpos)
  have hτ : 1 ≤ τ := by
    apply Nat.one_le_iff_ne_zero.mpr
    apply Nat.ne_of_gt
    apply Nat.ceil_pos.mpr
    exact mul_pos (by exact_mod_cast Fintype.card_pos (α := X))
      (Real.rpow_pos_of_pos (by norm_num) _)
  apply twoTestRigidity k (D f) T₀ τ (interlaceFun f (2 ^ k)) C₀ z
    (by have hh := hrobust.2.1; omega) (by linarith)
    ?_ ?_ ?_ hτ hgap R C P hCn (Finset.subset_univ _) hCden hRC.1 hcost hcomp
  · intro d hd
    apply blockLowerBound_of_exact
    intro R' C' Q' _ hden hQ hrows
    apply ClassicalTests.classicalFirstTest (h := z) hrobust hd hkb hbase (le_refl T₀)
      (by linarith) Q' R' C' hQ hrows
    apply Nat.ceil_le.mpr
    simpa only [hC₀, mul_comm] using hden
  · intro d hd
    apply blockLowerBound_of_exact
    intro R' C' Q' _ hden hQ hrows
    apply ClassicalTests.classicalSecondTest (h := z) hrobust hd hkb hslack.le (le_refl T₀)
      (by linarith) Q' R' C' hQ hrows
    apply Nat.ceil_le.mpr
    simpa only [hC₀, mul_comm] using hden
  · apply blockLowerBound_of_exact
    intro R' C' Q' _ hden hQ hrows
    apply ClassicalTests.powerOfTwoTest hrobust (by omega : 1 ≤ (1 : ℕ))
      hrobust.1 Q' R' C' (by simpa using hQ) hrows
    · apply Nat.ceil_le.mpr
      have hh : (9 / 25 : ℝ) * (C₀.card : ℝ) ≤ z * (C₀.card : ℝ) := by
        apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      simpa only [hC₀, mul_comm] using hh.trans hden
    · simp only [Nat.cast_one]
      exact le_refl τ

/-- The dominant-block assertion depends only on labels of retained rows. -/
theorem noWaste_congr_labels {X : Type*} {L : ℕ} [DecidableEq I]
    (Q : Finset I) (R : Finset (I × X)) (lab lab' : I × X → Fin L)
    (T₀ τ : ℕ) (hlab : ∀ a ∈ R, lab a = lab' a) :
    NoWasteConclusion Q R lab T₀ τ ↔ NoWasteConclusion Q R lab' T₀ τ := by
  have heq : ∀ j i, R.filter (fun a => lab a = j ∧ a.1 = i) =
      R.filter (fun a => lab' a = j ∧ a.1 = i) := by
    intro j i
    apply Finset.filter_congr
    intro a ha
    rw [hlab a ha]
  simp only [NoWasteConclusion, heq]

/-- Classical separation for a protocol whose input types are precisely the
retained rows and columns of the restricted matrix. This is the literal
protocol interface of `thm:paper-classical-separation`; the ambient extension
used in the proof preserves cost, evaluation, and every retained transcript.
The robustness parameter `b` is natural, as in the current Foundations API. -/
theorem classicalSeparation {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] {f : X → Y → Bool} {b k : ℕ} {x z : ℝ}
    (hrobust : IsRobustAt f b) (hk : 1 ≤ k) (hx1 : x ≤ 1)
    (hz : (18 / 25 : ℝ) ≤ z)
    (hgap : 2 ^ k * ⌈(Fintype.card X : ℝ) * (2 : ℝ) ^ (1 - (b : ℝ))⌉₊ <
      ⌈(Fintype.card X : ℝ) * x⌉₊)
    (R : Finset (Fin (2 ^ k) × X)) (C : Finset (Fin (2 ^ k) → Y))
    (hRC : (R, C) ∈ bracketGE X Y (2 ^ k) x z)
    (P : Protocol {a // a ∈ R} {c // c ∈ C} Bool)
    (hcost : P.cost ≤ D f + k)
    (hcomp : P.Computes (subgame (interlaceFun f (2 ^ k)) R C)) :
    Protocol.FirstKRowBitsOn Finset.univ Finset.univ k P ∧
    NoWasteConclusion (Finset.univ : Finset (Fin (2 ^ k))) R
      (Protocol.prefixLabelFinQ R P) ⌈(Fintype.card X : ℝ) * x⌉₊
      ⌈(Fintype.card X : ℝ) * (2 : ℝ) ^ (1 - (b : ℝ))⌉₊ ∧
    ∀ j, (Protocol.prefixFiber R (Protocol.prefixLabelFinQ R P) j).Nonempty := by
  classical
  have hRn : R.Nonempty := by
    have hrow := hRC.1 (0 : Fin (2 ^ k)) (Finset.mem_univ _)
    have ht : 0 < ⌈(Fintype.card X : ℝ) * x⌉₊ := by omega
    exact (Finset.card_pos.mp (ht.trans_le hrow)).mono (Finset.filter_subset _ _)
  have hCn : C.Nonempty := by
    apply Finset.card_pos.mp
    have hc : 0 < ⌈(Fintype.card Y : ℝ) ^ (2 ^ k) * z⌉₊ := by
      apply Nat.ceil_pos.mpr
      exact mul_pos (pow_pos (by exact_mod_cast Fintype.card_pos (α := Y)) _) (by linarith)
    exact hc.trans_le hRC.2
  let P' := Protocol.extendSub R C hRn hCn P
  have hc' : P'.cost ≤ D f + k := by simpa [P'] using hcost
  have hp' : ∀ a ∈ R, ∀ c ∈ C, P'.eval a c = interlaceFun f (2 ^ k) a c := by
    intro a ha c hc
    change (Protocol.extendSub R C hRn hCn P).eval
      (⟨a, ha⟩ : {a // a ∈ R}).val (⟨c, hc⟩ : {c // c ∈ C}).val = _
    rw [Protocol.eval_extendSub]
    exact hcomp ⟨a, ha⟩ ⟨c, hc⟩
  obtain ⟨hprefix, hsep, _⟩ := classicalSeparationOn hrobust hk hx1 hz hgap R C hRC P' hc' hp'
  have hlabels : ∀ a ∈ R, Protocol.prefixCodeRaw k P' a = Protocol.prefixLabelFinQ R P a :=
    Protocol.prefixCodeRaw_extendSub_eq_prefixLabelFinQ R C hRn hCn P
  have hsep' := (noWaste_congr_labels Finset.univ R _ _ _ _ hlabels).mp hsep
  refine ⟨(Protocol.firstKRowBitsOn_extendSub_iff R C hRn hCn k P).mp hprefix,
    hsep', ?_⟩
  exact all_prefix_rectangles_nonempty R _ hgap hsep'

namespace SanityChecks

/-- Reachability really matters: a Bob node in a dead branch does not
invalidate the two-bit Alice prefix of every reachable execution. -/
theorem reachable_prefix_ignores_dead_bob :
    Protocol.FirstKRowBitsOn ({false} : Finset Bool) ({()} : Finset Unit) 2
    (Protocol.aNode (fun a => a)
      (Protocol.aNode (fun _ => false) (Protocol.leaf false) (Protocol.leaf true))
      (Protocol.bNode (fun _ => false) (Protocol.leaf true) (Protocol.leaf false))) := by
  simp [Protocol.FirstKRowBitsOn]

/-- In contrast, a reachable Bob node at the root violates the claimed prefix. -/
theorem reachable_bob_breaks_prefix :
    ¬ Protocol.FirstKRowBitsOn ({false} : Finset Bool) ({()} : Finset Unit) 1
    (Protocol.bNode (fun _ => false) (Protocol.leaf true) (Protocol.leaf false)) := by
  simp [Protocol.FirstKRowBitsOn]

end SanityChecks

end EthInapproximability.CurrentPaper.ProtocolSeparation
