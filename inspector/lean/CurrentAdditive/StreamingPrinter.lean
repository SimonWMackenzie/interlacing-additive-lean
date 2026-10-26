import CurrentAdditive.BitPrinter

/-!
Linear-pass printer for the literal bit-polynomial list. Unlike BitPrinter.word,
this updates the power after each output coordinate and does not recompute
`y^j` from scratch. Correctness as a finite-field list still requires a
certified irreducible modulus and a bridge to the algebraic bias proof.
-/

namespace CurrentAdditive.FiniteFieldConstructor.StreamingPrinter

open CurrentAdditive.FiniteFieldConstructor.BitPrinter

/-- Output `n` bits from the current power, accumulating in reverse order. -/
def run (d modulus x y : ℕ) : ℕ → ℕ → List Bool → List Bool × ℕ
  | 0, p, acc => (acc.reverse, p)
  | n + 1, p, acc =>
      run d modulus x y n (mul d modulus p y) (dot d x p :: acc)

def word (d modulus n x y : ℕ) : List Bool :=
  (run d modulus x y n 1 []).1

def labelledWords (d modulus n : ℕ) : List (ℕ × ℕ × List Bool) :=
  ((List.range (2 ^ d)).flatMap fun x =>
    (List.range (2 ^ d)).map fun y => (x, y, word d modulus n x y))

theorem run_length (d modulus x y n p : ℕ) (acc : List Bool) :
    (run d modulus x y n p acc).1.length = acc.length + n := by
  induction n generalizing p acc with
  | zero => simp [run]
  | succ n ih =>
      rw [run]
      rw [ih]
      simp only [List.length_cons]
      omega

theorem word_length (d modulus n x y : ℕ) :
    (word d modulus n x y).length = n := by
  simpa [word] using run_length d modulus x y n 1 []

theorem labelledWords_length (d modulus n : ℕ) :
    (labelledWords d modulus n).length = (2 ^ d) ^ 2 := by
  simp [labelledWords, pow_two]

theorem labelledWords_labels (d modulus n : ℕ) (x y : ℕ)
    (hx : x < 2 ^ d) (hy : y < 2 ^ d) :
    (x, y, word d modulus n x y) ∈ labelledWords d modulus n := by
  simp only [labelledWords, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨x, hx, y, hy, rfl⟩

#eval labelledWords 1 3 2
#print axioms word_length
#print axioms labelledWords_length
#print axioms labelledWords_labels

end CurrentAdditive.FiniteFieldConstructor.StreamingPrinter
