import Mathlib

/-!
Executable representation of the v27 seed enumeration. Integers encode binary
polynomials by their coefficient bits. `modulus` must eventually be certified
irreducible and monic of degree `d`; this file makes no such assertion.
-/

namespace CurrentAdditive.FiniteFieldConstructor.BitPrinter

/-- Carryless polynomial product over F₂. Both loops have fixed bounds. -/
def rawProduct (d : ℕ) (a b : ℕ) : ℕ :=
  (List.range d).foldl
    (fun acc i => if a.testBit i then Nat.xor acc (b <<< i) else acc) 0

/-- Cancel high coefficients from degree `2d-2` down to `d`. -/
def reduce (d modulus p : ℕ) : ℕ :=
  (List.range d).reverse.foldl
    (fun acc i => if acc.testBit (d + i) then Nat.xor acc (modulus <<< i) else acc) p

/-- Multiplication of encoded residues, pending a valid modulus certificate. -/
def mul (d modulus a b : ℕ) : ℕ := reduce d modulus (rawProduct d a b)

/-- The `j`th successive power, with zero exponent equal to one. -/
def power (d modulus y : ℕ) : ℕ → ℕ
  | 0 => 1
  | j + 1 => mul d modulus (power d modulus y j) y

/-- Binary dot product on exactly `d` coordinates. -/
def dot (d x z : ℕ) : Bool :=
  (List.range d).foldl
    (fun acc i => acc ^^ (x.testBit i && z.testBit i)) false

def bit (d modulus x y j : ℕ) : Bool := dot d x (power d modulus y j)

def word (d modulus n x y : ℕ) : List Bool :=
  (List.range n).map (bit d modulus x y)

/-- All `2^d` binary-vector labels paired with all `2^d` field-residue labels. -/
def labelledWords (d modulus n : ℕ) : List (ℕ × ℕ × List Bool) :=
  ((List.range (2 ^ d)).flatMap fun x =>
    (List.range (2 ^ d)).map fun y => (x, y, word d modulus n x y))

theorem word_length (d modulus n x y : ℕ) :
    (word d modulus n x y).length = n := by
  simp [word]

theorem labelledWords_length (d modulus n : ℕ) :
    (labelledWords d modulus n).length = (2 ^ d) ^ 2 := by
  simp [labelledWords, pow_two]

theorem labelledWords_labels (d modulus n : ℕ) (x y : ℕ)
    (hx : x < 2 ^ d) (hy : y < 2 ^ d) :
    (x, y, word d modulus n x y) ∈ labelledWords d modulus n := by
  simp only [labelledWords, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨x, hx, y, hy, rfl⟩

#eval (labelledWords 1 3 2).length
#eval labelledWords 1 3 2
#print axioms word_length
#print axioms labelledWords_length
#print axioms labelledWords_labels

end CurrentAdditive.FiniteFieldConstructor.BitPrinter
