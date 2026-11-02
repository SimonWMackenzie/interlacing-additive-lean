import EthInapproximability.CurrentPaper.ProtocolSeparation

/-!
# Current paper: excess blocks and the sharp tagged-fibre count

Source lock: `2026-09-22-complete-replacement-v8`,
`02-separation.tex`, `lem:paper-excess-block-induction`, and
`A-stage4-details.tex`, the paragraph "Two fixed blocks" in
`lem:paper-terminal-two-stream`.

The induction below reasons about actual finite restrictions and protocol
trees. Its base and half-column bounds are precisely the two lower-bound
inputs of the manuscript lemma; the full-density higher-level conclusion
is proved by first-message analysis. No exact-cost assumption is used.
-/

namespace EthInapproximability.CurrentPaper.TerminalExcess

open NPCC Workspace.Types.CommComplexity Workspace.Types.Protocol
open ProtocolSeparation
open scoped BigOperators

variable {A B I : Type*}

/-- Large fibres account for every possible excess above the threshold. -/
theorem sum_le_threshold_card {J : Type*} [Fintype J]
    (x : J → ℝ) (lam : ℝ) (hx : ∀ i, x i ≤ 1) :
    (∑ i, x i) ≤ (Fintype.card J : ℝ) * lam +
      ((Finset.univ.filter (fun i => lam ≤ x i)).card : ℝ) *
        (1 - lam) := by
  classical
  calc
    (∑ i, x i) ≤ ∑ i, (lam + if lam ≤ x i then 1 - lam else 0) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases h : lam ≤ x i
      · simp only [if_pos h]
        linarith [hx i]
      · simp only [if_neg h, add_zero]
        exact le_of_lt (lt_of_not_ge h)
    _ = _ := by
      simp [Finset.sum_add_distrib, Finset.sum_ite]
      ring

/-- The manuscript's sharp count: `delta > lambda + epsilon` guarantees
strictly more than one full set of large fibres across the two tagged copies.
The positive index count is essential; an empty index type would falsify it. -/
theorem sharp_large_count {J : Type*} [Fintype J] [Nonempty J]
    (r f : J → ℝ) (lam eps delta : ℝ)
    (hr : ∀ i, r i ≤ 1) (hf : ∀ i, f i ≤ 1)
    (hsr : (Fintype.card J : ℝ) * (1 - eps) ≤ ∑ i, r i)
    (hsf : (Fintype.card J : ℝ) * delta ≤ ∑ i, f i)
    (hlam : lam < 1) (hdelta : lam + eps < delta) :
    Fintype.card J <
      (Finset.univ.filter (fun i => lam ≤ r i)).card +
      (Finset.univ.filter (fun i => lam ≤ f i)).card := by
  classical
  by_contra h
  have hcount := Nat.le_of_not_gt h
  have hcountR :
      ((Finset.univ.filter (fun i => lam ≤ r i)).card : ℝ) +
      ((Finset.univ.filter (fun i => lam ≤ f i)).card : ℝ) ≤
      (Fintype.card J : ℝ) := by exact_mod_cast hcount
  have hq : (0 : ℝ) < Fintype.card J := by
    exact_mod_cast (Fintype.card_pos (α := J))
  have hstrict := mul_lt_mul_of_pos_left hdelta hq
  have hmul := mul_le_mul_of_nonneg_right hcountR (sub_nonneg.mpr hlam.le)
  have hru := sum_le_threshold_card r lam hr
  have hfu := sum_le_threshold_card f lam hf
  nlinarith

/-- Select `q+1` actual tagged fibre labels at the sharp threshold. -/
theorem exists_sharp_large_packet {J : Type*} [Fintype J] [Nonempty J]
    (r f : J → ℝ) (lam eps delta : ℝ)
    (hr : ∀ i, r i ≤ 1) (hf : ∀ i, f i ≤ 1)
    (hsr : (Fintype.card J : ℝ) * (1 - eps) ≤ ∑ i, r i)
    (hsf : (Fintype.card J : ℝ) * delta ≤ ∑ i, f i)
    (hlam : lam < 1) (hdelta : lam + eps < delta) :
    ∃ T : Finset (Bool × J), T.card = Fintype.card J + 1 ∧
      ∀ p ∈ T, lam ≤ if p.1 then f p.2 else r p.2 := by
  classical
  let S : Finset (Bool × J) := Finset.univ.filter
    (fun p => lam ≤ if p.1 then f p.2 else r p.2)
  have hcard : S.card =
      (Finset.univ.filter (fun i => lam ≤ r i)).card +
      (Finset.univ.filter (fun i => lam ≤ f i)).card := by
    simp only [S, Finset.card_filter]
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega
  have hlarge := sharp_large_count r f lam eps delta hr hf hsr hsf hlam hdelta
  have henough : Fintype.card J + 1 ≤ S.card := by omega
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq henough
  refine ⟨T, hT, ?_⟩
  intro p hp
  exact (Finset.mem_filter.mp (hTS hp)).2

/-- Extend the predicates of a protocol on a finite rectangle to the ambient
input types. Outside the rectangle each query is set to `false`. -/
noncomputable def extendRestriction (R : Finset A) (C : Finset B) :
    Protocol {a // a ∈ R} {c // c ∈ C} Bool → Protocol A B Bool := by
  classical
  exact fun P => match P with
  | .leaf z => .leaf z
  | .aNode a l r => .aNode (fun x => if hx : x ∈ R then a ⟨x, hx⟩ else false)
      (extendRestriction R C l) (extendRestriction R C r)
  | .bNode b l r => .bNode (fun y => if hy : y ∈ C then b ⟨y, hy⟩ else false)
      (extendRestriction R C l) (extendRestriction R C r)

theorem extendRestriction_cost (R : Finset A) (C : Finset B)
    (P : Protocol {a // a ∈ R} {c // c ∈ C} Bool) :
    (extendRestriction R C P).cost = P.cost := by
  induction P with
  | leaf z => rfl
  | aNode a l r ihl ihr => simp [extendRestriction, Protocol.cost, ihl, ihr]
  | bNode b l r ihl ihr => simp [extendRestriction, Protocol.cost, ihl, ihr]

theorem extendRestriction_eval (R : Finset A) (C : Finset B)
    (P : Protocol {a // a ∈ R} {c // c ∈ C} Bool)
    (x : A) (hx : x ∈ R) (y : B) (hy : y ∈ C) :
    (extendRestriction R C P).eval x y = P.eval ⟨x, hx⟩ ⟨y, hy⟩ := by
  induction P with
  | leaf z => rfl
  | aNode a l r ihl ihr => simp [extendRestriction, Protocol.eval, hx, ihl, ihr]
  | bNode b l r ihl ihr => simp [extendRestriction, Protocol.eval, hy, ihl, ihr]

/-- The one-step excess-block argument. The half-column test rules out a
leaf and handles a Bob query; an Alice query keeps enough rows in a strict
majority of the required block labels. -/
theorem excessBlockStep [DecidableEq I]
    (F : A → B → Bool) (label : A → I) (C₀ : Finset B)
    (p pprev T Tprev L : ℕ) (h : ℝ)
    (hL : 1 ≤ L)
    (hp : 2 * pprev ≤ p + 1) (hT : 2 * Tprev ≤ T + 1)
    (hprev : BlockLowerBound F label C₀ pprev Tprev h L)
    (hhalf : BlockLowerBound F label C₀ p T (h / 2) L) :
    BlockLowerBound F label C₀ p T h (L + 1) := by
  classical
  intro R C Q hCsub hCden hQ hR
  have hne := Workspace.UpperBound.AchievableCosts_nonempty (subgame F R C)
  have hmem : D (subgame F R C) ∈ AchievableCosts (subgame F R C) :=
    Nat.sInf_mem hne
  obtain ⟨P₀, hcost₀, hcomp₀⟩ := hmem
  let P := extendRestriction R C P₀
  have hcost : P.cost = D (subgame F R C) :=
    (extendRestriction_cost R C P₀).trans hcost₀
  have hcomp : ∀ a ∈ R, ∀ c ∈ C, P.eval a c = F a c := by
    intro a ha c hc
    rw [extendRestriction_eval R C P₀ a ha c hc]
    exact hcomp₀ ⟨a, ha⟩ ⟨c, hc⟩
  suffices L + 1 ≤ P.cost by omega
  cases hP : P with
  | leaf z =>
      rw [hP] at hcomp
      have hden : h / 2 * (C₀.card : ℝ) ≤ (C.card : ℝ) := by
        have hc : (0 : ℝ) ≤ C₀.card := by positivity
        nlinarith
      have hl := hhalf R C Q hCsub hden hQ hR
      have hu := restrictionCost_le_of_agrees F R C (.leaf z) hcomp
      simp only [Protocol.cost] at hu
      omega
  | bNode b l r =>
      rw [hP] at hcomp
      obtain ⟨β, hlarge⟩ := exists_large_bool_child C b
      let C' := C.filter (fun c => b c = β)
      let P' := if β then r else l
      have hcomp' : ∀ a ∈ R, ∀ c ∈ C', P'.eval a c = F a c := by
        intro a ha c hc
        have hc' := Finset.mem_filter.mp hc
        have hp' := hcomp a ha c hc'.1
        cases β <;> simpa [Protocol.eval, P', hc'.2] using hp'
      have hden : h / 2 * (C₀.card : ℝ) ≤ (C'.card : ℝ) := by
        have hlargeR : (C.card : ℝ) ≤ 2 * (C'.card : ℝ) := by exact_mod_cast hlarge
        linarith
      have hl := hhalf R C' Q
        (Finset.Subset.trans (Finset.filter_subset _ _) hCsub) hden hQ hR
      have hu := restrictionCost_le_of_agrees F R C' P' hcomp'
      have hp' : P'.cost ≤ max l.cost r.cost := by cases β <;> simp [P']
      simp only [Protocol.cost]
      omega
  | aNode a l r =>
      rw [hP] at hcomp
      obtain ⟨Q0, Q1, _, _, _, _, hsum, hR0, hR1⟩ :=
        row_block_majority_partition R Q label a T Tprev hR hT
      have hcomp0 : ∀ x ∈ R.filter (fun x => a x = false), ∀ c ∈ C,
          l.eval x c = F x c := by
        intro x hx c hc
        have hx' := Finset.mem_filter.mp hx
        simpa [Protocol.eval, hx'.2] using hcomp x hx'.1 c hc
      have hcomp1 : ∀ x ∈ R.filter (fun x => a x = true), ∀ c ∈ C,
          r.eval x c = F x c := by
        intro x hx c hc
        have hx' := Finset.mem_filter.mp hx
        simpa [Protocol.eval, hx'.2] using hcomp x hx'.1 c hc
      have hlarge : pprev ≤ Q0.card ∨ pprev ≤ Q1.card := by omega
      rcases hlarge with h0 | h1
      · have hl := hprev _ C Q0 hCsub hCden h0 hR0
        have hu := restrictionCost_le_of_agrees F _ C l hcomp0
        simp only [Protocol.cost]
        omega
      · have hl := hprev _ C Q1 hCsub hCden h1 hR1
        have hu := restrictionCost_le_of_agrees F _ C r hcomp1
        simp only [Protocol.cost]
        omega

/-- Excess-block induction with explicit integer thresholds. The only
communication premises are the source lemma's base and half-column tests. -/
theorem excessBlocks_of_thresholds [DecidableEq I]
    (F : A → B → Bool) (label : A → I) (C₀ : Finset B)
    (p T : ℕ → ℕ) (L ellMax : ℕ) (h : ℝ)
    (hL : 1 ≤ L)
    (hp : ∀ ell < ellMax, 2 * p ell ≤ p (ell + 1) + 1)
    (hT : ∀ ell < ellMax, 2 * T ell ≤ T (ell + 1) + 1)
    (hbase : BlockLowerBound F label C₀ (p 0) (T 0) h L)
    (hhalf : ∀ ell < ellMax,
      BlockLowerBound F label C₀ (p (ell + 1)) (T (ell + 1)) (h / 2) (L + ell)) :
    ∀ ell ≤ ellMax, BlockLowerBound F label C₀ (p ell) (T ell) h (L + ell) := by
  intro ell
  induction ell with
  | zero => intro _; simpa using hbase
  | succ ell ih =>
      intro he
      have he' : ell < ellMax := by omega
      have hh' := excessBlockStep F label C₀
        (p (ell + 1)) (p ell) (T (ell + 1)) (T ell) (L + ell) h
        (by omega) (hp ell he') (hT ell he') (ih (by omega)) (hhalf ell he')
      simpa [Nat.add_assoc] using hh'

/-- The integer block count in the manuscript, with `t = 2 * halfWidth`.
This form avoids subtraction in the exponent at level zero. -/
def excessWidth (halfWidth ell : ℕ) : ℕ := 2 ^ ell * halfWidth + 1

/-- The exact ceiling row threshold of the manuscript. -/
noncomputable def excessRows (m : ℕ) (a₀ : ℝ) (ell : ℕ) : ℕ :=
  ⌈(2 : ℝ) ^ ell * a₀ * m⌉₊

theorem excessWidth_half (halfWidth ell : ℕ) :
    2 * excessWidth halfWidth ell ≤ excessWidth halfWidth (ell + 1) + 1 := by
  simp only [excessWidth, pow_succ]
  nlinarith

theorem excessRows_half (m : ℕ) (a₀ : ℝ) (ha : 0 ≤ a₀) (ell : ℕ) :
    2 * excessRows m a₀ ell ≤ excessRows m a₀ (ell + 1) + 1 := by
  have hh := ceil_half_threshold ((2 : ℝ) ^ (ell + 1) * a₀ * m) (by positivity)
  have heq : (2 : ℝ) ^ (ell + 1) * a₀ * m / 2 = 2 ^ ell * a₀ * m := by
    rw [pow_succ]
    ring
  rw [heq] at hh
  exact hh

/-- `lem:paper-excess-block-induction`, with `t = 2 * halfWidth` and
`L = H + log t`. The certified integer `L` need not equal any exact cost.
The density/range guards used to prove its inputs are not needed again by
this protocol induction. -/
theorem excessBlocks [DecidableEq I]
    (F : A → B → Bool) (label : A → I) (C₀ : Finset B)
    (m halfWidth L ellMax : ℕ) (a₀ h : ℝ)
    (hL : 1 ≤ L) (ha : 0 ≤ a₀)
    (hbase : BlockLowerBound F label C₀ (halfWidth + 1) (excessRows m a₀ 0) h L)
    (hhalf : ∀ ell < ellMax,
      BlockLowerBound F label C₀ (excessWidth halfWidth (ell + 1))
        (excessRows m a₀ (ell + 1)) (h / 2) (L + ell)) :
    ∀ ell ≤ ellMax, BlockLowerBound F label C₀ (excessWidth halfWidth ell)
      (excessRows m a₀ ell) h (L + ell) := by
  apply excessBlocks_of_thresholds F label C₀ (excessWidth halfWidth)
    (excessRows m a₀) L ellMax h hL
  · exact fun ell _ => excessWidth_half halfWidth ell
  · exact fun ell _ => excessRows_half m a₀ ha ell
  · simpa only [excessWidth, pow_zero, one_mul] using hbase
  · exact hhalf

/-- Density of an actual retained fibre, normalized by the original number
of rows per block. Labels of the two streams remain distinct. -/
noncomputable def fibreDensity [DecidableEq I]
    (R : Finset A) (label : A → I) (m : ℕ) (i : I) : ℝ :=
  ((R.filter (fun a => label a = i)).card : ℝ) / m

/-- Sharp counting on an actual retained row set produces `q+1` labelled
blocks with the exact ceiling row threshold, not just abstract densities. -/
theorem actual_large_packet {J : Type*} [Fintype J] [Nonempty J]
    [DecidableEq J] (R : Finset A) (label : A → Bool × J)
    (m : ℕ) (hm : 0 < m) (lam eps delta : ℝ)
    (hrows : ∀ i, (R.filter (fun a => label a = i)).card ≤ m)
    (hsr : (Fintype.card J : ℝ) * (1 - eps) ≤
      ∑ i, fibreDensity R label m (false, i))
    (hsf : (Fintype.card J : ℝ) * delta ≤
      ∑ i, fibreDensity R label m (true, i))
    (hlam : lam < 1) (hdelta : lam + eps < delta) :
    ∃ Q : Finset (Bool × J), Q.card = Fintype.card J + 1 ∧
      HasRowsInBlocks label R Q ⌈lam * m⌉₊ := by
  classical
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hupper : ∀ i, fibreDensity R label m i ≤ 1 := by
    intro i
    rw [fibreDensity, div_le_one hmR]
    exact_mod_cast hrows i
  obtain ⟨Q, hQ, hlarge⟩ := exists_sharp_large_packet
    (fun i => fibreDensity R label m (false, i))
    (fun i => fibreDensity R label m (true, i)) lam eps delta
    (fun i => hupper (false, i)) (fun i => hupper (true, i)) hsr hsf hlam hdelta
  refine ⟨Q, hQ, ?_⟩
  intro i hi
  have hl : lam ≤ fibreDensity R label m i := by
    have hh := hlarge i hi
    rcases i with ⟨β, i⟩
    cases β <;> simpa using hh
  apply Nat.ceil_le.mpr
  exact (le_div_iff₀ hmR).mp hl

/-- The sharp count and excess induction combined on the same actual
retained matrix. The base and half-column tests remain explicit: for the
paper's product family they are supplied by coordinate projection and the
certified-cost stopping theorem, respectively. This is not a balancedness
or physical-section construction theorem. -/
theorem fixedBin_lower_of_tests {J : Type*} [Fintype J] [Nonempty J]
    [DecidableEq J] (F : A → B → Bool) (label : A → Bool × J)
    (C₀ : Finset B) (R : Finset A) (C : Finset B)
    (m halfWidth L ell : ℕ) (a₀ h eps delta : ℝ)
    (hm : 0 < m) (hL : 1 ≤ L) (ha : 0 ≤ a₀)
    (hq : Fintype.card J = 2 ^ ell * halfWidth)
    (hrows : ∀ i, (R.filter (fun a => label a = i)).card ≤ m)
    (hsr : (Fintype.card J : ℝ) * (1 - eps) ≤
      ∑ i, fibreDensity R label m (false, i))
    (hsf : (Fintype.card J : ℝ) * delta ≤
      ∑ i, fibreDensity R label m (true, i))
    (hlam : (2 : ℝ) ^ ell * a₀ < 1)
    (hdelta : (2 : ℝ) ^ ell * a₀ + eps < delta)
    (hCsub : C ⊆ C₀) (hCden : h * (C₀.card : ℝ) ≤ (C.card : ℝ))
    (hbase : BlockLowerBound F label C₀ (halfWidth + 1) (excessRows m a₀ 0) h L)
    (hhalf : ∀ d < ell, BlockLowerBound F label C₀
      (excessWidth halfWidth (d + 1)) (excessRows m a₀ (d + 1)) (h / 2) (L + d)) :
    L + ell ≤ D (subgame F R C) := by
  obtain ⟨Q, hQ, hR⟩ := actual_large_packet R label m hm
    ((2 : ℝ) ^ ell * a₀) eps delta hrows hsr hsf hlam hdelta
  have hlow := excessBlocks F label C₀ m halfWidth L ell a₀ h hL ha hbase hhalf
    ell (le_refl _)
  apply hlow R C Q hCsub hCden
  · simp only [excessWidth, hQ, hq, le_refl]
  · exact hR

end EthInapproximability.CurrentPaper.TerminalExcess
