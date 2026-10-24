import EthInapproximability.CurrentPaper.PrimeSamplerBinaryEntryInterface
import EthInapproximability.CurrentPaper.MatrixStage4FamilyData

/-!
# Exact ordinal coordinate semantics for the Stage--4 prime family tables

The indexed polynomial value is an ordinal in the first-row alphabet,
enumerated lexicographically as `(first-coordinate, source-row)`. Splitting
that ordinal by the source-row count gives the two one-hot field positions.
-/

namespace EthInapproximability.CurrentPaper.PrimeSamplerFamilyTableCoordinate

open Construction MatrixStage4FamilyData

theorem canonical_split (a rx : Nat)
    (c : Fin (qOne a * rx)) (hrx : 0 < rx) :
    ((PrimeSampler.canonicalFirstRowsEquiv a rx) c).1.val = c.val / rx ∧
    ((PrimeSampler.canonicalFirstRowsEquiv a rx) c).2.val = c.val % rx := by
  let pair := (PrimeSampler.canonicalFirstRowsEquiv a rx) c
  have he : (finProdFinEquiv pair).val = c.val := by
    have h := (PrimeSampler.canonicalFirstRowsEquiv a rx).symm_apply_apply c
    simpa only [PrimeSampler.canonicalFirstRowsEquiv] using congrArg Fin.val h
  have hordinal : pair.2.val + rx * pair.1.val = c.val := by
    simpa only [finProdFinEquiv_apply_val] using he
  have hdiv : c.val / rx = pair.1.val := by
    rw [← hordinal]
    simp [Nat.add_mul_div_left, Nat.div_eq_of_lt pair.2.isLt, hrx]
  have hmod : c.val % rx = pair.2.val := by
    rw [← hordinal]
    simp [Nat.add_mod, Nat.mod_eq_of_lt pair.2.isLt]
  exact ⟨hdiv.symm, hmod.symm⟩

def actualFamily (a q t rx : Nat)
    (hm : 0 < qOne a * rx) :
    SecondFamily a q (PrimeSampler.size q t (qOne a * rx)) (Fin rx) :=
  PrimeSampler.secondFamily a q t (qOne a * rx) hm
    (PrimeSampler.canonicalFirstRowsEquiv a rx)

theorem field_coordinates (a q t rx : Nat)
    (hm : 0 < qOne a * rx) (hrx : 0 < rx)
    (ℓ : Fin (PrimeSampler.size q t (qOne a * rx))) (α : Fin q) :
    let family := actualFamily a q t rx hm
    (familyFirst family (finProdFinEquiv (ℓ, α))).val =
      PrimeSampler.entry (PrimeSampler.prime q t (qOne a * rx)) t
        (qOne a * rx) ℓ.val α.val / rx ∧
    (familyRow family (finProdFinEquiv (ℓ, α))).val =
      PrimeSampler.entry (PrimeSampler.prime q t (qOne a * rx)) t
        (qOne a * rx) ℓ.val α.val % rx := by
  dsimp only
  simp only [familyFirst_at, familyRow_at, actualFamily,
    PrimeSampler.secondFamily]
  simpa only [PrimeSampler.family_entry] using
    (canonical_split a rx
      (PrimeSampler.family q t (qOne a * rx) hm ℓ α) hrx)

theorem entry_word_coordinates (a q t rx : Nat)
    (hm : 0 < qOne a * rx) (hrx : 0 < rx)
    (ℓ : Fin (PrimeSampler.size q t (qOne a * rx))) (α : Fin q) :
    let family := actualFamily a q t rx hm
    let p := PrimeSampler.prime q t (qOne a * rx)
    let word := PrimeSamplerBinaryEntryInterface.entryWord
      ℓ.val.bits p.bits α.val.bits (qOne a * rx).bits
    (familyFirst family (finProdFinEquiv (ℓ, α))).val =
      EncodedCommunication.bitsValue word / rx ∧
    (familyRow family (finProdFinEquiv (ℓ, α))).val =
      EncodedCommunication.bitsValue word % rx := by
  have hp : 2 ≤ PrimeSampler.prime q t (qOne a * rx) :=
    (PrimeSampler.prime_isPrime q t (qOne a * rx)).two_le
  have hlabel : ℓ.val <
      PrimeSampler.prime q t (qOne a * rx) ^ t := by
    simpa only [← PrimeSampler.size_exact] using ℓ.isLt
  have hentry := PrimeSamplerBinaryEntryInterface.entry_value
    ℓ.val.bits (PrimeSampler.prime q t (qOne a * rx)).bits
    α.val.bits (qOne a * rx).bits
    (by simpa only [EncodedCommunication.bitsValue_bits] using hp)
    (by simpa only [EncodedCommunication.bitsValue_bits] using hm)
    t (by simpa only [EncodedCommunication.bitsValue_bits] using hlabel)
  have hcoord := field_coordinates a q t rx hm hrx ℓ α
  simp only [EncodedCommunication.bitsValue_bits] at hentry
  simpa only [hentry] using hcoord

end EthInapproximability.CurrentPaper.PrimeSamplerFamilyTableCoordinate
