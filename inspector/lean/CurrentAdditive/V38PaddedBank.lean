import CurrentAdditive.ZeroPadMachine
import CurrentAdditive.V38ExecutableEntry

/-!
Private adapter for reusing the old K+1-position table-lookup callback.
The selected mathematical array is still exactly H×K. This file creates
only an internal packed bank, with a zero sentinel preceding each H×K block.
The bank is a computable finite list and is not an asserted pattern array.
-/

namespace CurrentAdditive.V38Machine

open CurrentAdditive.SmallBias
open CurrentAdditive.V38Executable
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable
open Paper2.YaoLookup

def paddedPositionCount (b t : ℕ) : ℕ :=
  2 ^ b * (2 ^ t * 2 ^ t + 1)

def paddedIndex (b t d : ℕ)
    (ℓ : Fin ((2 ^ d) ^ 2))
    (a : Fin (2 ^ b))
    (p : Fin (2 ^ t * 2 ^ t + 1)) :
    Fin (((2 ^ d) ^ 2) * paddedPositionCount b t) :=
  finProdFinEquiv
    (ℓ, finProdFinEquiv (a, p))

/-- Each old callback coordinate sees zero at `p=0` and the genuine
v38 printed bit at `p=i+1`. -/
def paddedBits (b t d modulus : ℕ) : List Bool :=
  List.ofFn (fun q : Fin (((2 ^ d) ^ 2) * paddedPositionCount b t) =>
    let lp := finProdFinEquiv.symm q
    let ap := finProdFinEquiv.symm lp.2
    wordAtPosition (v38PrintedPairWord b t d modulus) lp.1 ap.1 ap.2)

theorem paddedBits_length (b t d modulus : ℕ) :
    (paddedBits b t d modulus).length =
      ((2 ^ d) ^ 2) * paddedPositionCount b t := by
  simp [paddedBits]

theorem paddedBits_get (b t d modulus : ℕ)
    (ℓ : Fin ((2 ^ d) ^ 2)) (a : Fin (2 ^ b))
    (p : Fin (2 ^ t * 2 ^ t + 1)) :
    (paddedBits b t d modulus).get
      ⟨(paddedIndex b t d ℓ a p).val,
        by rw [paddedBits_length]; exact (paddedIndex b t d ℓ a p).isLt⟩ =
      wordAtPosition (v38PrintedPairWord b t d modulus) ℓ a p := by
  simp only [paddedBits, List.get_ofFn, paddedIndex, Fin.cast_mk]
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem paddedBits_zero (b t d modulus : ℕ)
    (ℓ : Fin ((2 ^ d) ^ 2)) (a : Fin (2 ^ b)) :
    (paddedBits b t d modulus).get
      ⟨(paddedIndex b t d ℓ a 0).val,
        by rw [paddedBits_length]; exact (paddedIndex b t d ℓ a 0).isLt⟩ =
      false := by
  rw [paddedBits_get]
  simp [wordAtPosition]

theorem paddedBits_real (b t d modulus : ℕ)
    (ℓ : Fin ((2 ^ d) ^ 2)) (a : Fin (2 ^ b))
    (i : Fin (2 ^ t * 2 ^ t)) :
    (paddedBits b t d modulus).get
      ⟨(paddedIndex b t d ℓ a i.succ).val,
        by rw [paddedBits_length]; exact (paddedIndex b t d ℓ a i.succ).isLt⟩ =
      v38PrintedPairWord b t d modulus ℓ (a, i) := by
  rw [paddedBits_get]
  simp [wordAtPosition]

/-- The internal bank is bounded by one padded coordinate per genuine
bit plus one sentinel per public address and seed. -/
theorem paddedBits_size (b t d modulus : ℕ) :
    (paddedBits b t d modulus).length =
      ((2 ^ d) ^ 2) *
        (v38PositionCount b t + 2 ^ b) := by
  rw [paddedBits_length]
  simp [paddedPositionCount, v38PositionCount]
  ring

#print axioms paddedBits_get
#print axioms paddedBits_zero
#print axioms paddedBits_real
#print axioms paddedBits_size

end CurrentAdditive.V38Machine
