import Paper2.SelectedTape
import Paper2.A4PolyIn

/-!
# Fixed outer tape envelope for two selected-tape algorithms

The first algorithm's output-size bound comes from its actual selected-tape
machine run and the finite machine's push bound. The second algorithm receives
only the first `B.tapeLength y` bits of an independent suffix block, where
`y` is the first machine's actual output. One fixed monomial outer tape is
chosen before `x`, `y`, or either random block is known.
-/

noncomputable section

namespace Paper2.SelectedTape.Bind

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedComplexity
open Paper2.Unit4Shell.Poly

def sourceBound (A : Algorithm) (n : ℕ) : ℕ :=
  2 * n + 1 + A.cR * (n + 1) ^ A.dR +
    A.cT * (n + 1) ^ A.dT * A.machine.pushBound

theorem source_output_length (A : Algorithm) (x : List Bool)
    (t : Fin (A.tapeLength x) → Bool) :
    (A.output x (List.ofFn t)).length ≤ sourceBound A x.length := by
  have h := BitMachine.output_length_bound A.machine (A.runs x t)
  simpa [sourceBound, Algorithm.tapeLength, pair_length] using h

theorem sourceBound_poly (A : Algorithm) : PolyIn id (sourceBound A) := by
  unfold sourceBound
  repeat (first
    | exact self
    | exact const _
    | apply add
    | apply mul
    | apply pow)

def classifierBlock (A B : Algorithm) (n : ℕ) : ℕ :=
  B.cR * (sourceBound A n + 1) ^ B.dR

theorem classifier_tape_le_block (A B : Algorithm) (x : List Bool)
    (t : Fin (A.tapeLength x) → Bool) :
    B.tapeLength (A.output x (List.ofFn t)) ≤ classifierBlock A B x.length := by
  change B.cR * ((A.output x (List.ofFn t)).length + 1) ^ B.dR ≤
    B.cR * (sourceBound A x.length + 1) ^ B.dR
  gcongr
  exact source_output_length A x t

theorem classifierBlock_poly (A B : Algorithm) : PolyIn id (classifierBlock A B) := by
  unfold classifierBlock
  exact mul (const _) (pow (add (sourceBound_poly A) (const 1)) B.dR)

theorem needed_poly (A B : Algorithm) :
    PolyIn id (fun n => A.cR * (n + 1) ^ A.dR + classifierBlock A B n) := by
  exact add (mul (const _) (pow (add self (const 1)) A.dR))
    (classifierBlock_poly A B)

def outerC (A B : Algorithm) : ℕ := Classical.choose (needed_poly A B)
def outerD (A B : Algorithm) : ℕ :=
  Classical.choose (Classical.choose_spec (needed_poly A B))
def outerLength (A B : Algorithm) (n : ℕ) : ℕ :=
  outerC A B * (n + 1) ^ outerD A B

theorem needed_le_outer (A B : Algorithm) (n : ℕ) :
    A.cR * (n + 1) ^ A.dR + classifierBlock A B n ≤ outerLength A B n :=
  Classical.choose_spec (Classical.choose_spec (needed_poly A B)) n

def suffixLength (A B : Algorithm) (n : ℕ) : ℕ :=
  outerLength A B n - A.cR * (n + 1) ^ A.dR

theorem source_plus_suffix (A B : Algorithm) (n : ℕ) :
    A.cR * (n + 1) ^ A.dR + suffixLength A B n = outerLength A B n := by
  have := needed_le_outer A B n
  unfold suffixLength
  omega

theorem classifier_le_suffix (A B : Algorithm) (x : List Bool)
    (t : Fin (A.tapeLength x) → Bool) :
    B.tapeLength (A.output x (List.ofFn t)) ≤ suffixLength A B x.length := by
  have h1 := classifier_tape_le_block A B x t
  have h2 := needed_le_outer A B x.length
  unfold suffixLength
  omega

#print axioms source_output_length
#print axioms sourceBound_poly
#print axioms classifier_tape_le_block
#print axioms needed_le_outer
#print axioms classifier_le_suffix

end Paper2.SelectedTape.Bind
