import EthInapproximability.CurrentPaper.EncodedCNF

/-!
# Ordered bounded-width OR clauses and their literal three-CNF translation

Source: frozen v8 `06-eth.tex`, `thm:paper-sparse-gap-source`, the Boolean
encoding between Dinur's finite-alphabet constraints and the bounded-degree
three-colouring source. Clauses retain OR semantics and list positions.
The prefix-OR construction below is total even for an empty clause.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseEncoding

open EncodedCNF

structure LongFormula where
  «variables» : ℕ
  clauses : List (List Literal)
  deriving DecidableEq

def fromIndexed (nvars n : ℕ) (clause : Fin n → List Literal) : LongFormula :=
  ⟨nvars, List.ofFn clause⟩

@[simp] theorem fromIndexed_variables (nvars n : ℕ) (clause : Fin n → List Literal) :
    (fromIndexed nvars n clause).variables = nvars := rfl

@[simp] theorem fromIndexed_length (nvars n : ℕ) (clause : Fin n → List Literal) :
    (fromIndexed nvars n clause).clauses.length = n := List.length_ofFn

def LongFormula.Valid (f : LongFormula) : Prop :=
  ∀ c ∈ f.clauses, ∀ l ∈ c, l.variable < f.variables

def LongFormula.WidthAtMost (f : LongFormula) (K : ℕ) : Prop :=
  ∀ c ∈ f.clauses, c.length ≤ K

def longClauseEval (c : List Literal) (assignment : List Bool) : Bool :=
  c.any fun l => l.eval assignment

def LongFormula.eval (f : LongFormula) (assignment : List Bool) : Bool :=
  f.clauses.all fun c => longClauseEval c assignment

def LongFormula.Satisfiable (f : LongFormula) : Prop :=
  ∃ assignment : List Bool, assignment.length = f.variables ∧ f.eval assignment = true

def falseClauses (f : LongFormula) (assignment : List Bool) : Finset (Fin f.clauses.length) :=
  Finset.univ.filter fun i => longClauseEval (f.clauses.get i) assignment = false

def FormulaGap (f : LongFormula) (ρ : ℚ) : Prop :=
  ∀ assignment : List Bool, assignment.length = f.variables →
    ρ * f.clauses.length ≤ ((falseClauses f assignment).card : ℚ)

def occurrenceCount (f : LongFormula) (v : ℕ) : ℕ :=
  ((f.clauses.flatten).map Literal.variable).count v

def BoundedOccurrence (f : LongFormula) (d : ℕ) : Prop :=
  ∀ v < f.variables, occurrenceCount f v ≤ d

def positive (v : ℕ) : Literal := ⟨v, true⟩
def negative (v : ℕ) : Literal := ⟨v, false⟩
def negate (l : Literal) : Literal := ⟨l.variable, !l.positive⟩

def unit (l : Literal) : Clause := ⟨l, l, l⟩

/-- Three OR clauses assert that bit `p+1` is the OR of bit `p` and `l`.
Repeated literals pad binary clauses to the ordered three-literal format. -/
def orGate (p : ℕ) (l : Literal) : List Clause :=
  [⟨negate l, positive (p + 1), positive (p + 1)⟩,
   ⟨negative p, positive (p + 1), positive (p + 1)⟩,
   ⟨l, positive p, negative (p + 1)⟩]

/-- One fresh prefix-OR bit for each input prefix, including the empty
prefix. The first bit is false and the last is required true. -/
def chain (base : ℕ) (c : List Literal) : List Clause :=
  [unit (negative base)] ++
    (c.zipIdx.flatMap fun (l, t) => orGate (base + t) l) ++
      [unit (positive (base + c.length))]

/-- For clauses of width at most `K`, fixed-size fresh-variable blocks make
different clause occurrences disjoint even when their syntax is identical.
The list-valued construction is total without that validity hypothesis. -/
def translate (K : ℕ) (f : LongFormula) : Formula where
  «variables» := f.variables + (K + 1) * f.clauses.length
  clauses := f.clauses.zipIdx.flatMap fun (c, j) => chain (f.variables + j * (K + 1)) c

@[simp] theorem positive_eval (v : ℕ) (a : List Bool) :
    (positive v).eval a = a.getD v false := rfl

@[simp] theorem negative_eval (v : ℕ) (a : List Bool) :
    (negative v).eval a = !(a.getD v false) := rfl

@[simp] theorem negate_eval (l : Literal) (a : List Bool) :
    (negate l).eval a = !(l.eval a) := by
  cases l with
  | mk v p => cases p <;> simp [negate, Literal.eval]

@[simp] theorem unit_eval (l : Literal) (a : List Bool) :
    (unit l).eval a = l.eval a := by simp [unit, Clause.eval]

@[simp] theorem orGate_length (p : ℕ) (l : Literal) : (orGate p l).length = 3 := rfl

/-- This equivalence is the complete local truth table of the gadget. -/
theorem orGate_eval (p : ℕ) (l : Literal) (a : List Bool) :
    ((orGate p l).all fun c => c.eval a) = true ↔
      a.getD (p + 1) false = (a.getD p false || l.eval a) := by
  simp only [orGate, List.all_cons, List.all_nil, Bool.and_true, Clause.eval,
    negate_eval, positive_eval, negative_eval]
  cases a.getD p false <;> cases a.getD (p + 1) false <;> cases l.eval a <;> decide

end EthInapproximability.CurrentPaper.SourceClauseEncoding
