import CurrentAdditive.StreamingPrinter

/-!
Literal finite trial division for a monic binary polynomial. Every candidate
and every positive-degree monic divisor through `floor(d/2)` is tested. The
search returns `Option`: no existence or correctness is inferred merely from
the computation. The bridge from bit remainder to polynomial divisibility
is a separate unfinished proof obligation.
-/

namespace CurrentAdditive.FiniteFieldConstructor.TrialSearch

open CurrentAdditive.FiniteFieldConstructor.BitPrinter

/-- Encoding of a monic polynomial of degree `d` with low bits `tail`. -/
def monicBits (d tail : ℕ) : ℕ := 2 ^ d + tail

/-- Long division over F₂, assuming the dividend's degree is at most `d`
and `divisor` is monic of degree `e`. -/
def remainder (d e divisor dividend : ℕ) : ℕ :=
  (List.range (d - e + 1)).reverse.foldl
    (fun acc i => if acc.testBit (e + i) then Nat.xor acc (divisor <<< i) else acc)
    dividend

/-- Exhaustive divisibility check over the manuscript's divisor range. -/
def trialIrreducible (d tail : ℕ) : Bool :=
  (List.range (d / 2)).all fun e0 =>
    let e := e0 + 1
    (List.range (2 ^ e)).all fun divisorTail =>
      remainder d e (monicBits e divisorTail) (monicBits d tail) != 0

/-- First passing candidate among the `2^d` monic degree-`d` encodings. -/
def firstPassing (d : ℕ) : Option ℕ :=
  ((List.range (2 ^ d)).map (monicBits d)).find?
    (fun candidate => trialIrreducible d (candidate - 2 ^ d))

/-- The end-to-end list printer remains option-valued until existence and
correctness of the search are proved. -/
def makeList (d n : ℕ) : Option (List (ℕ × ℕ × List Bool)) :=
  (firstPassing d).map fun modulus =>
    CurrentAdditive.FiniteFieldConstructor.StreamingPrinter.labelledWords d modulus n

#eval firstPassing 1
#eval firstPassing 2
#eval (makeList 1 2).map List.length

end CurrentAdditive.FiniteFieldConstructor.TrialSearch
