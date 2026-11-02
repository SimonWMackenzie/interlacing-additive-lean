import EthInapproximability.CurrentPaper.Restoration
import EthInapproximability.CurrentPaper.GraphVectors
import EthInapproximability.CurrentPaper.PrimeSampler
import EthInapproximability.CurrentPaper.IndexSeed
import EthInapproximability.ParameterizedNP.CanonicalBracketInvariance

/-!
# Literal finite iteration of the current construction

Source: v8 `05-iteration.tex`, `thm:paper-finite-iteration` and
`eq:paper-gap-invariant`; `04-bridge.tex`, `eq:one-level-exact-carriers`.

The matrix at each level uses one fixed graph, the current edge-only vectors,
the explicit prime-polynomial family, the two-support duplicate, and two
literal interlaces followed by transposition. All numeric input relabellings
are explicit bijections in lexicographic/type-first order. No promise appears
in the constructor.

This module proves finite composition, conditional on the upstream protected
matrix bounds and profiles. Those hypotheses remain visible; it does not
prove them, eventual parameter acceptance, or a bit-machine runtime bound.
-/

namespace EthInapproximability.CurrentPaper.Iteration

open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP
open GuardedSourceGraph GuardedSourceSlab
open scoped BigOperators

noncomputable section

/-- An explicit finite enumeration, not a choice of distinct represented values. -/
structure Numbering (X : Type) where
  size : ℕ
  equiv : Fin size ≃ X

namespace Numbering

def fin (n : ℕ) : Numbering (Fin n) := ⟨n, Equiv.refl _⟩

/-- The right coordinate varies fastest. -/
def prod {X Y : Type} (eX : Numbering X) (eY : Numbering Y) : Numbering (X × Y) :=
  ⟨eX.size * eY.size, finProdFinEquiv.symm.trans (eX.equiv.prodCongr eY.equiv)⟩

/-- Every left-hand label precedes every right-hand label. -/
def sum {X Y : Type} (eX : Numbering X) (eY : Numbering Y) : Numbering (X ⊕ Y) :=
  ⟨eX.size + eY.size, finSumFinEquiv.symm.trans (eX.equiv.sumCongr eY.equiv)⟩

def ulift {X : Type} (e : Numbering X) : Numbering (ULift.{0} X) :=
  ⟨e.size, e.equiv.trans Equiv.ulift.symm⟩

/-- Function tuples are lexicographic: the last coordinate varies fastest. -/
def tuple {X : Type} (e : Numbering X) (q : ℕ) : Numbering (Fin q → X) :=
  ⟨e.size ^ q, finFunctionFinEquiv.symm.trans
    ((Equiv.piCongrLeft (fun _ : Fin q => Fin e.size) (Equiv.refl _)).trans
      { toFun := fun f i => e.equiv (f i.rev)
        invFun := fun f i => e.equiv.symm (f i.rev)
        left_inv := by intro f; ext i; simp
        right_inv := by intro f; ext i; simp })⟩

/-- Type-first enumeration of a finite disjoint union. -/
def sigma {k : ℕ} {X : Fin k → Type} (e : ∀ i, Numbering (X i)) :
    Numbering ((i : Fin k) × X i) :=
  ⟨∑ i, (e i).size,
    finSigmaFinEquiv.symm.trans (Equiv.sigmaCongrRight fun i => (e i).equiv)⟩

theorem card_eq {X : Type} [Fintype X] (e : Numbering X) :
    Fintype.card X = e.size := (Fintype.card_congr e.equiv).symm.trans (by simp)

theorem size_pos {X : Type} [Fintype X] [Nonempty X] (e : Numbering X) :
    0 < e.size := by rw [← e.card_eq]; exact Fintype.card_pos

theorem prod_index {X Y : Type} (eX : Numbering X) (eY : Numbering Y) (x : X) (y : Y) :
    ((prod eX eY).equiv.symm (x, y)).val =
      (eX.equiv.symm x).val * eY.size + (eY.equiv.symm y).val := by
  change (eY.equiv.symm y).val + eY.size * (eX.equiv.symm x).val = _
  ring

theorem tuple_index {X : Type} (e : Numbering X) (q : ℕ) (f : Fin q → X) :
    ((tuple e q).equiv.symm f).val =
      ∑ i : Fin q, (e.equiv.symm (f i.rev)).val * e.size ^ i.val := by
  exact finFunctionFinEquiv_apply _

def weighted {k : ℕ} {X : Fin k → Type} [∀ i, Fintype (X i)]
    (e : ∀ i, Numbering (X i)) (c : Fin k → ℕ) :
    Numbering (WeightedDuplication.Carrier X c) :=
  sigma fun i => prod (e i) (fin (WeightedDuplication.copies X c i))

def rowSupport {X T V B : Type} (x : Numbering X) (t : Numbering T)
    (v : Numbering V) (b : Numbering B) :
    ∀ i, Numbering (WeightedDuplication.rowSupport X T V B i) :=
  Fin.cases x (Fin.cases t (Fin.cases v (Fin.cases b (fun i => Fin.elim0 i))))

def columnSupport {X Y : Type} (x : Numbering X) (y : Numbering Y) :
    ∀ i, Numbering (WeightedDuplication.columnSupport X Y i) :=
  Fin.cases x (Fin.cases y (fun i => Fin.elim0 i))

end Numbering

/-- Matrices passed between levels have public nonempty numeric input domains. -/
structure Matrix where
  rows : ℕ
  columns : ℕ
  rows_pos : 0 < rows
  columns_pos : 0 < columns
  entry : Fin rows → Fin columns → Bool

instance (M : Matrix) : Nonempty (Fin M.rows) := ⟨⟨0, M.rows_pos⟩⟩
instance (M : Matrix) : Nonempty (Fin M.columns) := ⟨⟨0, M.columns_pos⟩⟩

def number {X Y : Type} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (f : X → Y → Bool) (eX : Numbering X) (eY : Numbering Y) : Matrix where
  rows := eX.size
  columns := eY.size
  rows_pos := eX.size_pos
  columns_pos := eY.size_pos
  entry := fun x y => f (eX.equiv x) (eY.equiv y)

theorem number_cost {X Y : Type} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (f : X → Y → Bool) (eX : Numbering X) (eY : Numbering Y) :
    D (number f eX eY).entry = D f := D_equiv_invariance f eX.equiv eY.equiv

theorem number_bracket {X Y : Type} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (f : X → Y → Bool) (eX : Numbering X) (eY : Numbering Y)
    (p : ℕ) (x z : ℝ) :
    Dfamily (interlaceFun (number f eX eY).entry p)
      (bracketGE (Fin eX.size) (Fin eY.size) p x z) =
    Dfamily (interlaceFun f p) (bracketGE X Y p x z) :=
  CanonicalBracketInvariance.bracket_transport_complexity p eX.equiv eY.equiv f x z

theorem number_lambda {X Y : Type} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (f : X → Y → Bool) (eX : Numbering X) (eY : Numbering Y)
    (p : ℕ) (x z : ℝ) :
    LambdaGE (number f eX eY).entry p x z = LambdaGE f p x z :=
  CanonicalBracketInvariance.lambda_transport p eX.equiv eY.equiv f x z

theorem number_robust {X Y : Type} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (f : X → Y → Bool) (eX : Numbering X) (eY : Numbering Y)
    (b : ℕ) : IsRobustAt (number f eX eY).entry b ↔ IsRobustAt f b := by
  unfold IsRobustAt
  change (1 ≤ b ∧ 2 ≤ D (number f eX eY).entry ∧
    D (number f eX eY).entry ≤ Dfamily (interlaceFun (number f eX eY).entry 1)
      (bracketGE (Fin eX.size) (Fin eY.size) 1 (2 ^ (-(b : ℝ))) (3 / 5)) ∧
    D (number f eX eY).entry - 1 ≤ Dfamily (interlaceFun (number f eX eY).entry 1)
      (bracketGE (Fin eX.size) (Fin eY.size) 1 (2 ^ (-(b : ℝ))) (3 / 10))) ↔ _
  rw [number_bracket, number_bracket, number_cost]

section Step

set_option maxHeartbeats 1200000

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

def parameters (_G : EndpointGraph V E) (sourceConstant b y i : ℕ) (M : Matrix) :
    Parameters.Input where
  sourceConstant := sourceConstant
  nextDepth := b
  cost := y + i
  rows := M.rows
  columns := M.columns
  edges := Fintype.card E
  incomingDepth := b

variable (G : EndpointGraph V E) (sourceConstant b y i : ℕ) (M : Matrix)

abbrev stepParameters := parameters G sourceConstant b y i M
abbrev a := Parameters.firstExponent (stepParameters G sourceConstant b y i M)
abbrev s := Parameters.bins (stepParameters G sourceConstant b y i M)
abbrev q₂ := q2 G (s G sourceConstant b y i M)
abbrev t₂ := Parameters.balanceOrder (stepParameters G sourceConstant b y i M)
abbrev alphabet := Construction.qOne (a G sourceConstant b y i M) * M.rows
abbrev labels := PrimeSampler.size (q₂ G sourceConstant b y i M)
  (t₂ G sourceConstant b y i M) (alphabet G sourceConstant b y i M)

theorem alphabet_pos : 0 < alphabet G sourceConstant b y i M := by
  exact Nat.mul_pos (Parameters.firstWidth_pos _) M.rows_pos

theorem bins_ge_four : 4 ≤ s G sourceConstant b y i M := by
  have h := Parameters.bins_hard_seed_floor (stepParameters G sourceConstant b y i M)
  have hp : 1 ≤ 2 ^ (2 ^ 20) := Nat.one_le_pow _ _ (by decide)
  change 4 ≤ Parameters.bins (stepParameters G sourceConstant b y i M)
  omega

def secondFamily : Construction.SecondFamily (a G sourceConstant b y i M)
    (q₂ G sourceConstant b y i M) (labels G sourceConstant b y i M) (Fin M.rows) :=
  PrimeSampler.secondFamily _ _ _ _ (alphabet_pos G sourceConstant b y i M)
    (PrimeSampler.canonicalFirstRowsEquiv _ _)

abbrev NRow := Construction.ProtectedColumns (a G sourceConstant b y i M)
  (s G sourceConstant b y i M) (q₂ G sourceConstant b y i M) (Fin M.columns)
abbrev NCol := Construction.ProtectedRows (s G sourceConstant b y i M)
  (labels G sourceConstant b y i M) (GraphVectors.vertexCount V (s G sourceConstant b y i M))
  (GraphVectors.auxiliaryCount (s G sourceConstant b y i M)) (Fin M.rows)

def protectedMatrix : NRow G sourceConstant b y i M → NCol G sourceConstant b y i M → Bool :=
  GraphVectors.protectedMatrix G M.entry _ _ _ (bins_ge_four G sourceConstant b y i M)
    (secondFamily G sourceConstant b y i M)

abbrev rq := Parameters.outerExponent (stepParameters G sourceConstant b y i M)
abbrev rQ := Parameters.restorationExponent (stepParameters G sourceConstant b y i M)

def aligned := Restoration.output (protectedMatrix G sourceConstant b y i M)
  (rq G sourceConstant b y i M)
def rawOutput := Restoration.output (aligned G sourceConstant b y i M)
  (rQ G sourceConstant b y i M)

abbrev OutputRow := Fin (2 ^ rQ G sourceConstant b y i M) →
  (Fin (2 ^ rq G sourceConstant b y i M) × NRow G sourceConstant b y i M)
abbrev OutputCol := Fin (2 ^ rQ G sourceConstant b y i M) ×
  (Fin (2 ^ rq G sourceConstant b y i M) → NCol G sourceConstant b y i M)

def firstColumnNumbering := (Numbering.fin M.columns).tuple
  (Construction.firstLength (a G sourceConstant b y i M) (s G sourceConstant b y i M))
def secondRowNumbering := (Numbering.fin (q₂ G sourceConstant b y i M)).prod
  (firstColumnNumbering G sourceConstant b y i M)
def rawColumnNumbering := ((Numbering.fin M.columns).tuple (s G sourceConstant b y i M + 1)).prod
  ((secondRowNumbering G sourceConstant b y i M).tuple (s G sourceConstant b y i M))
def templateNumbering := (Numbering.fin (s G sourceConstant b y i M)).prod
  (Numbering.fin (labels G sourceConstant b y i M))
def vertexNumbering := (Numbering.fin (GraphVectors.vertexCount V (s G sourceConstant b y i M))).prod
  (Numbering.fin M.rows)
def auxiliaryNumbering := (Numbering.fin (GraphVectors.auxiliaryCount (s G sourceConstant b y i M))).prod
  (Numbering.fin M.rows)
def rawRowNumbering := (templateNumbering G sourceConstant b y i M).sum
  ((vertexNumbering G sourceConstant b y i M).sum (auxiliaryNumbering G sourceConstant b y i M))

def nRowNumbering : Numbering (NRow G sourceConstant b y i M) :=
  (Numbering.weighted (Numbering.columnSupport
    (rawColumnNumbering G sourceConstant b y i M)
    (secondRowNumbering G sourceConstant b y i M)) WeightedDuplication.columnWeight).prod
      (Numbering.fin (Construction.uniformCopies (Y := Fin M.columns)
        (a G sourceConstant b y i M) (s G sourceConstant b y i M) (q₂ G sourceConstant b y i M)))

def nColNumbering : Numbering (NCol G sourceConstant b y i M) :=
  Numbering.weighted (Numbering.rowSupport
    (rawRowNumbering G sourceConstant b y i M)
    (templateNumbering G sourceConstant b y i M).ulift
    (vertexNumbering G sourceConstant b y i M)
    (auxiliaryNumbering G sourceConstant b y i M)) WeightedDuplication.rowWeight

instance : Nonempty (NRow G sourceConstant b y i M) := by
  apply Fintype.card_pos_iff.mp
  change 0 < Fintype.card (Construction.ProtectedColumns _ _ _ (Fin M.columns))
  rw [Construction.card_protectedColumns]
  have hq := q2_pos G (s G sourceConstant b y i M)
  have hn := M.columns_pos
  simp only [Fintype.card_fin]
  positivity

instance : Nonempty (NCol G sourceConstant b y i M) := by
  apply Fintype.card_pos_iff.mp
  change 0 < Fintype.card (Construction.ProtectedRows _ _ _ _ (Fin M.rows))
  rw [Construction.card_protectedRows]
  have hs := bins_ge_four G sourceConstant b y i M
  have hsb : 0 < s G sourceConstant b y i M - 3 := by omega
  have hn := M.rows_pos
  have hL : 0 < labels G sourceConstant b y i M := PrimeSampler.size_pos _ _ _
  have hV := G.card_vertex_pos
  simp only [GraphVectors.vertexCount, GraphVectors.auxiliaryCount, Fintype.card_fin]
  positivity

def outputRowNumbering : Numbering (OutputRow G sourceConstant b y i M) :=
  ((Numbering.fin (2 ^ rq G sourceConstant b y i M)).prod
    (nRowNumbering G sourceConstant b y i M)).tuple (2 ^ rQ G sourceConstant b y i M)

def outputColNumbering : Numbering (OutputCol G sourceConstant b y i M) :=
  (Numbering.fin (2 ^ rQ G sourceConstant b y i M)).prod
    ((nColNumbering G sourceConstant b y i M).tuple (2 ^ rq G sourceConstant b y i M))

set_option maxHeartbeats 1000000 in
def step : Matrix := number (rawOutput G sourceConstant b y i M)
  (outputRowNumbering G sourceConstant b y i M) (outputColNumbering G sourceConstant b y i M)

section EntryEvaluation

-- Keep the finite enumerations opaque during this definitional calculation.
-- Unfolding their astronomical numeric domains cannot help identify the entry.
attribute [local irreducible] outputRowNumbering outputColNumbering

theorem step_entry (x : Fin (step G sourceConstant b y i M).rows)
    (z : Fin (step G sourceConstant b y i M).columns) :
    (step G sourceConstant b y i M).entry x z =
      rawOutput G sourceConstant b y i M
        ((outputRowNumbering G sourceConstant b y i M).equiv x)
        ((outputColNumbering G sourceConstant b y i M).equiv z) := rfl

end EntryEvaluation

theorem step_cost : D (step G sourceConstant b y i M).entry =
    D (rawOutput G sourceConstant b y i M) := number_cost _ _ _

theorem step_robust : IsRobustAt (step G sourceConstant b y i M).entry b ↔
    IsRobustAt (rawOutput G sourceConstant b y i M) b := number_robust _ _ _ _

theorem step_lambda : LambdaGE (step G sourceConstant b y i M).entry 1
    (2 ^ (-(b : ℝ))) (3 / 5) =
    LambdaGE (rawOutput G sourceConstant b y i M) 1 (2 ^ (-(b : ℝ))) (3 / 5) :=
  number_lambda _ _ _ _ _ _

/-- The exact dimensions of the SAME constructed matrix, in either promise case. -/
theorem step_dimensions :
    (step G sourceConstant b y i M).rows =
      (2 ^ rq G sourceConstant b y i M * Fintype.card (NRow G sourceConstant b y i M)) ^
        (2 ^ rQ G sourceConstant b y i M) ∧
    (step G sourceConstant b y i M).columns =
      2 ^ rQ G sourceConstant b y i M *
        Fintype.card (NCol G sourceConstant b y i M) ^ (2 ^ rq G sourceConstant b y i M) := by
  constructor
  · change (2 ^ rq G sourceConstant b y i M * (nRowNumbering G sourceConstant b y i M).size) ^ _ = _
    rw [← Numbering.card_eq]
  · change 2 ^ rQ G sourceConstant b y i M * (nColNumbering G sourceConstant b y i M).size ^ _ = _
    rw [← Numbering.card_eq]

def overhead : ℕ := a G sourceConstant b y i M +
  Parameters.secondExponent (stepParameters G sourceConstant b y i M) +
  Parameters.binExponent (stepParameters G sourceConstant b y i M) +
  rq G sourceConstant b y i M + rQ G sourceConstant b y i M

def baseOverhead : ℕ := a G sourceConstant b y i M +
  Parameters.secondExponent (stepParameters G sourceConstant b y i M) +
  Parameters.binExponent (stepParameters G sourceConstant b y i M)

def alignedCost : ℕ := y + i + baseOverhead G sourceConstant b y i M +
  rq G sourceConstant b y i M + 1

abbrev WRow := Fin (2 ^ rq G sourceConstant b y i M) → NCol G sourceConstant b y i M
abbrev WCol := Fin (2 ^ rq G sourceConstant b y i M) × NRow G sourceConstant b y i M

/-- The upstream conclusions still needed for the actual scale-aligned matrix.
These are exposed hypotheses, not a certificate claimed proved by iteration. -/
def AlignedProfiles : Prop :=
  let W := aligned G sourceConstant b y i M
  let C := alignedCost G sourceConstant b y i M
  let θ : ℝ := Parameters.retainedFraction (stepParameters G sourceConstant b y i M)
  let δ : ℝ := Parameters.columnLoss (stepParameters G sourceConstant b y i M)
  D W = C ∧
  C ≤ Dfamily (interlaceFun W 1)
    (bracketGE (WRow G sourceConstant b y i M) (WCol G sourceConstant b y i M) 1 θ (1 - δ)) ∧
  C - 1 ≤ Dfamily (interlaceFun W 1)
    (bracketGE (WRow G sourceConstant b y i M) (WCol G sourceConstant b y i M) 1 θ (3 / 5)) ∧
  C - 2 ≤ Dfamily (interlaceFun W 1)
    (bracketGE (WRow G sourceConstant b y i M) (WCol G sourceConstant b y i M) 1 θ (3 / 10))

theorem step_yes_upper
    (hyes : D (protectedMatrix G sourceConstant b y i M) ≤
      y + baseOverhead G sourceConstant b y i M) :
    D (step G sourceConstant b y i M).entry ≤ y + overhead G sourceConstant b y i M := by
  rw [step_cost]
  have h1 := Restoration.output_upper_of_bound (protectedMatrix G sourceConstant b y i M)
    (rq G sourceConstant b y i M) _ hyes
  have h2 := Restoration.output_upper_of_bound (aligned G sourceConstant b y i M)
    (rQ G sourceConstant b y i M) _ h1
  change D (rawOutput G sourceConstant b y i M) ≤ _ at h2
  simpa only [baseOverhead, overhead, Nat.add_assoc] using h2

theorem step_no_of_profiles (hc : 0 < sourceConstant) (hb : 1 ≤ b) (hD : 3 ≤ y + i)
    (hprofiles : AlignedProfiles G sourceConstant b y i M) :
    D (step G sourceConstant b y i M).entry = y + i + overhead G sourceConstant b y i M + 1 ∧
    IsRobustAt (step G sourceConstant b y i M).entry b ∧
    y + i + overhead G sourceConstant b y i M + 1 ≤
      LambdaGE (step G sourceConstant b y i M).entry 1 (2 ^ (-(b : ℝ))) (3 / 5) := by
  let p := stepParameters G sourceConstant b y i M
  obtain ⟨hδ0, hδ, hwidth, _, hscale⟩ := Parameters.restoration_gates p hc
  have hθ0 := Parameters.retainedFraction_pos p
  have hδR : (Parameters.columnLoss p : ℝ) ≤ (1 : ℝ) / 64 := by
    have hcast := (Rat.cast_le (K := ℝ)).2 hδ.le
    norm_num at hcast ⊢
    exact hcast
  have hwidthR : 80 * (b : ℝ) ≤ (2 : ℝ) ^ rQ G sourceConstant b y i M *
      (Parameters.columnLoss p : ℝ) := by
    exact_mod_cast hwidth
  have hscaleR : (2 : ℝ) ^ rQ G sourceConstant b y i M *
      (Parameters.retainedFraction p : ℝ) < 1 / 20 := by
    change ((2 ^ rQ G sourceConstant b y i M : ℕ) : ℚ) * Parameters.retainedFraction p < 1 / 20 at hscale
    have hcast := (Rat.cast_lt (K := ℝ)).2 hscale
    simpa only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
      Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hcast
  obtain ⟨hcost, hnear, hmod, hhalf⟩ := hprofiles
  have hC : 3 ≤ alignedCost G sourceConstant b y i M := by
    unfold alignedCost
    omega
  have h := Restoration.restore (aligned G sourceConstant b y i M)
    (alignedCost G sourceConstant b y i M) b (rQ G sourceConstant b y i M)
    hcost hC hb (by exact_mod_cast hδ0) hδR
    (by exact_mod_cast hθ0) hwidthR hscaleR hnear hmod hhalf
  rw [step_cost, step_robust, step_lambda]
  convert h using 1 <;> simp only [rawOutput, alignedCost, overhead, baseOverhead, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm]

/-- Balance of the exact family used by this step, not an existence premise. -/
theorem step_family_balanced
    (htq : t₂ G sourceConstant b y i M ≤ q₂ G sourceConstant b y i M) :
    IsBalancedFamily (t₂ G sourceConstant b y i M) (secondFamily G sourceConstant b y i M)
      (1 / (100 * (t₂ G sourceConstant b y i M : ℝ))) := by
  exact PrimeSampler.canonicalSecondFamily_balanced _ _ _ _
    (alphabet_pos G sourceConstant b y i M) (Parameters.balanceOrder_pos _) htq

theorem step_width_matches : q₂ G sourceConstant b y i M =
    Parameters.secondWidth (stepParameters G sourceConstant b y i M) := rfl

theorem step_family_balanced_of_accepted (hc : 0 < sourceConstant)
    (ha : Parameters.Accepted (stepParameters G sourceConstant b y i M)) :
    IsBalancedFamily (t₂ G sourceConstant b y i M) (secondFamily G sourceConstant b y i M)
      (1 / (100 * (t₂ G sourceConstant b y i M : ℝ))) := by
  apply step_family_balanced
  rw [step_width_matches]
  have h := Parameters.accepted_balance_four_le_second _ hc ha
  change Parameters.balanceOrder (stepParameters G sourceConstant b y i M) ≤ _
  omega

end Step

section Repetition

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The matrix and its public YES budget are computed together. -/
structure State where
  matrix : Matrix
  budget : ℕ

/-- Iterate the literal constructor on one fixed graph.  Neither a graph
promise nor a communication lower bound occurs in this definition. -/
def run (G : EndpointGraph V E) (sourceConstant b : ℕ) (initial : State) : ℕ → State
  | 0 => initial
  | i + 1 =>
    let current := run G sourceConstant b initial i
    ⟨step G sourceConstant b current.budget i current.matrix,
      current.budget + overhead G sourceConstant b current.budget i current.matrix⟩

variable (G : EndpointGraph V E) (sourceConstant b : ℕ) (initial : State)

@[simp] theorem run_zero : run G sourceConstant b initial 0 = initial := rfl

@[simp] theorem run_succ_matrix (i : ℕ) :
    (run G sourceConstant b initial (i + 1)).matrix =
      step G sourceConstant b (run G sourceConstant b initial i).budget i
        (run G sourceConstant b initial i).matrix := rfl

@[simp] theorem run_succ_budget (i : ℕ) :
    (run G sourceConstant b initial (i + 1)).budget =
      (run G sourceConstant b initial i).budget +
        overhead G sourceConstant b (run G sourceConstant b initial i).budget i
          (run G sourceConstant b initial i).matrix := rfl

theorem run_budget_ge_initial (i : ℕ) :
    initial.budget ≤ (run G sourceConstant b initial i).budget := by
  induction i with
  | zero => exact le_rfl
  | succ i ih =>
    rw [run_succ_budget]
    exact le_trans ih (Nat.le_add_right _ _)

/-- Exact carrier recurrence for these very matrices, independently of the
promise and of any lower-bound or parameter-acceptance hypotheses. -/
theorem run_dimensions (i : ℕ) :
    let current := run G sourceConstant b initial i
    (run G sourceConstant b initial (i + 1)).matrix.rows =
      (2 ^ rq G sourceConstant b current.budget i current.matrix *
        Fintype.card (NRow G sourceConstant b current.budget i current.matrix)) ^
          (2 ^ rQ G sourceConstant b current.budget i current.matrix) ∧
    (run G sourceConstant b initial (i + 1)).matrix.columns =
      2 ^ rQ G sourceConstant b current.budget i current.matrix *
        Fintype.card (NCol G sourceConstant b current.budget i current.matrix) ^
          (2 ^ rq G sourceConstant b current.budget i current.matrix) :=
  step_dimensions G sourceConstant b _ i _

/-- Section 7's YES induction.  The only step hypothesis is the protected
matrix upper bound, supplied from the preceding actual matrix's YES bound. -/
theorem run_yes (k : ℕ)
    (hinitial : D initial.matrix.entry ≤ initial.budget)
    (hstep : ∀ i < k,
      D (run G sourceConstant b initial i).matrix.entry ≤
          (run G sourceConstant b initial i).budget →
      D (protectedMatrix G sourceConstant b (run G sourceConstant b initial i).budget i
          (run G sourceConstant b initial i).matrix) ≤
        (run G sourceConstant b initial i).budget +
          baseOverhead G sourceConstant b (run G sourceConstant b initial i).budget i
            (run G sourceConstant b initial i).matrix) :
    ∀ i ≤ k, D (run G sourceConstant b initial i).matrix.entry ≤
      (run G sourceConstant b initial i).budget := by
  intro i
  induction i with
  | zero => intro _; exact hinitial
  | succ i ih =>
    intro hik
    have hi : i < k := by omega
    exact step_yes_upper G sourceConstant b _ i _
      (hstep i hi (ih (by omega)))

/-- Section 7's NO induction on the same constructed sequence.  The actual
scale-aligned profiles remain a step premise, with the preceding exact cost
and robustness supplied by induction rather than assumed at every level. -/
theorem run_no (k : ℕ) (hc : 0 < sourceConstant) (hb : 1 ≤ b)
    (hcost : D initial.matrix.entry = initial.budget)
    (hrobust : IsRobustAt initial.matrix.entry b)
    (hminimum : ∀ i < k, 3 ≤ (run G sourceConstant b initial i).budget + i)
    (hstep : ∀ i < k,
      D (run G sourceConstant b initial i).matrix.entry =
          (run G sourceConstant b initial i).budget + i →
      IsRobustAt (run G sourceConstant b initial i).matrix.entry b →
      AlignedProfiles G sourceConstant b (run G sourceConstant b initial i).budget i
        (run G sourceConstant b initial i).matrix) :
    ∀ i ≤ k,
      D (run G sourceConstant b initial i).matrix.entry =
          (run G sourceConstant b initial i).budget + i ∧
      IsRobustAt (run G sourceConstant b initial i).matrix.entry b := by
  intro i
  induction i with
  | zero => intro _; exact ⟨by simpa using hcost, hrobust⟩
  | succ i ih =>
    intro hik
    have hi : i < k := by omega
    obtain ⟨hpreviousCost, hpreviousRobust⟩ := ih (by omega)
    obtain ⟨hnextCost, hnextRobust, _⟩ := step_no_of_profiles G sourceConstant b _ i _
      hc hb (hminimum i hi) (hstep i hi hpreviousCost hpreviousRobust)
    constructor
    · simpa only [run_succ_matrix, run_succ_budget, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hnextCost
    · exact hnextRobust

/-- The stronger three-bound statement is supplied by every positive level;
no such initial hypothesis is silently inferred from two-bound robustness. -/
theorem run_no_lambda (k : ℕ) (hc : 0 < sourceConstant) (hb : 1 ≤ b)
    (hcost : D initial.matrix.entry = initial.budget)
    (hrobust : IsRobustAt initial.matrix.entry b)
    (hminimum : ∀ i < k, 3 ≤ (run G sourceConstant b initial i).budget + i)
    (hstep : ∀ i < k,
      D (run G sourceConstant b initial i).matrix.entry =
          (run G sourceConstant b initial i).budget + i →
      IsRobustAt (run G sourceConstant b initial i).matrix.entry b →
      AlignedProfiles G sourceConstant b (run G sourceConstant b initial i).budget i
        (run G sourceConstant b initial i).matrix) :
    ∀ i, 1 ≤ i → i ≤ k →
      (run G sourceConstant b initial i).budget + i ≤
        LambdaGE (run G sourceConstant b initial i).matrix.entry 1
          (2 ^ (-(b : ℝ))) (3 / 5) := by
  intro i hi hik
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  have hj : j < k := by omega
  obtain ⟨hpreviousCost, hpreviousRobust⟩ :=
    run_no G sourceConstant b initial k hc hb hcost hrobust hminimum hstep j (by omega)
  have hnext := (step_no_of_profiles G sourceConstant b _ j _ hc hb (hminimum j hj)
    (hstep j hj hpreviousCost hpreviousRobust)).2.2
  simpa only [Nat.succ_eq_add_one, run_succ_matrix, run_succ_budget, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hnext

end Repetition

private instance seedColumn_nonempty (b : ℕ) : Nonempty (Fin (IndexSeed.width b)) :=
  ⟨⟨0, by unfold IndexSeed.width; positivity⟩⟩

/-- Numeric input labels for the manuscript's full-cube indexing seed. -/
def seedMatrix (b : ℕ) : Matrix :=
  number (IndexSeed.seed b)
    ((⟨2, finTwoEquiv⟩ : Numbering Bool).tuple (IndexSeed.width b))
    (Numbering.fin (IndexSeed.width b))

theorem seedMatrix_cost (b : ℕ) : D (seedMatrix b).entry = IndexSeed.exponent b + 1 := by
  rw [seedMatrix, number_cost, IndexSeed.seed_D_eq]

theorem seedMatrix_robust (b : ℕ) (hb : 1 ≤ b) : IsRobustAt (seedMatrix b).entry b :=
  (number_robust _ _ _ _).2 (IndexSeed.seed_isRobustAt b hb)

theorem seedMatrix_lambda (b : ℕ) : IndexSeed.exponent b + 1 ≤
    LambdaGE (seedMatrix b).entry 1 (2 ^ (-(b : ℝ))) (3 / 5) := by
  rw [seedMatrix, number_lambda]
  exact IndexSeed.seed_lambda b

/-- The initial public budget is derived from the actual indexing cost. -/
def seedState (b : ℕ) : State := ⟨seedMatrix b, IndexSeed.exponent b + 1⟩

theorem seedState_minimum (b : ℕ) : 3 ≤ (seedState b).budget := by
  have h := IndexSeed.exponent_ge_six b
  change 3 ≤ IndexSeed.exponent b + 1
  omega

/-- The manuscript's indexing initialisation supplies the zero-level cost,
robustness, three-bound statement, and every minimum-cost guard.  The only
mathematical step premise left here is the scale-aligned profile theorem. -/
theorem run_indexing_no {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EndpointGraph V E) (sourceConstant b k : ℕ)
    (hc : 0 < sourceConstant) (hb : 1 ≤ b)
    (hstep : ∀ i < k,
      D (run G sourceConstant b (seedState b) i).matrix.entry =
          (run G sourceConstant b (seedState b) i).budget + i →
      IsRobustAt (run G sourceConstant b (seedState b) i).matrix.entry b →
      AlignedProfiles G sourceConstant b (run G sourceConstant b (seedState b) i).budget i
        (run G sourceConstant b (seedState b) i).matrix) :
    ∀ i ≤ k,
      D (run G sourceConstant b (seedState b) i).matrix.entry =
          (run G sourceConstant b (seedState b) i).budget + i ∧
      IsRobustAt (run G sourceConstant b (seedState b) i).matrix.entry b ∧
      (run G sourceConstant b (seedState b) i).budget + i ≤
        LambdaGE (run G sourceConstant b (seedState b) i).matrix.entry 1
          (2 ^ (-(b : ℝ))) (3 / 5) := by
  have hcost : D (seedState b).matrix.entry = (seedState b).budget := seedMatrix_cost b
  have hrobust : IsRobustAt (seedState b).matrix.entry b := seedMatrix_robust b hb
  have hminimum : ∀ i < k, 3 ≤ (run G sourceConstant b (seedState b) i).budget + i := by
    intro i _
    exact le_trans (seedState_minimum b)
      (le_trans (run_budget_ge_initial G sourceConstant b (seedState b) i)
        (Nat.le_add_right _ _))
  intro i hik
  obtain ⟨hC, hR⟩ :=
    run_no G sourceConstant b (seedState b) k hc hb hcost hrobust hminimum hstep i hik
  refine ⟨hC, hR, ?_⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simpa only [run_zero, seedState, Nat.add_zero] using seedMatrix_lambda b
  · exact run_no_lambda G sourceConstant b (seedState b) k hc hb hcost hrobust
      hminimum hstep i hi hik

theorem run_indexing_yes {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EndpointGraph V E) (sourceConstant b k : ℕ)
    (hstep : ∀ i < k,
      D (run G sourceConstant b (seedState b) i).matrix.entry ≤
          (run G sourceConstant b (seedState b) i).budget →
      D (protectedMatrix G sourceConstant b (run G sourceConstant b (seedState b) i).budget i
          (run G sourceConstant b (seedState b) i).matrix) ≤
        (run G sourceConstant b (seedState b) i).budget +
          baseOverhead G sourceConstant b (run G sourceConstant b (seedState b) i).budget i
            (run G sourceConstant b (seedState b) i).matrix) :
    ∀ i ≤ k, D (run G sourceConstant b (seedState b) i).matrix.entry ≤
      (run G sourceConstant b (seedState b) i).budget :=
  run_yes G sourceConstant b (seedState b) k (seedMatrix_cost b).le hstep

end
end EthInapproximability.CurrentPaper.Iteration
