import CurrentAdditive.CanonicalPhysicalWordBit

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open CurrentAdditive.SmallBias
open CurrentAdditive.FiniteFieldConstructor
open EthInapproximability.CurrentPaper

/-- Executable row-major bit array for the R² labelled finite-field words.
The pair label is slow and the word coordinate is fast. -/
def packedFieldBits (d modulus n : ℕ) : List Bool :=
  List.ofFn fun k : Fin ((2 ^ d) ^ 2 * n) =>
    let lj := finProdFinEquiv.symm k
    let xy := (printerPairLabel d).symm lj.1
    BitPrinter.bit d modulus xy.1.val xy.2.val lj.2.val

theorem packedFieldBits_length (d modulus n : ℕ) :
    (packedFieldBits d modulus n).length = (2 ^ d) ^ 2 * n := by
  simp [packedFieldBits]

theorem packedFieldBits_get (d modulus n : ℕ)
    (ℓ : Fin ((2 ^ d) ^ 2)) (j : Fin n) :
    (packedFieldBits d modulus n)[ℓ.val * n + j.val]?.getD false =
      BitPrinter.bit d modulus
        (((printerPairLabel d).symm ℓ).1).val
        (((printerPairLabel d).symm ℓ).2).val j.val := by
  let k : Fin ((2 ^ d) ^ 2 * n) := finProdFinEquiv (ℓ, j)
  have hkval : k.val = ℓ.val * n + j.val := by
    simp [k, finProdFinEquiv]
    ring
  rw [← hkval]
  have hk : k.val < (packedFieldBits d modulus n).length := by
    rw [packedFieldBits_length]
    exact k.isLt
  rw [List.getElem?_eq_getElem hk]
  simp only [packedFieldBits, List.getElem_ofFn, Option.getD_some]
  change BitPrinter.bit d modulus
    (((printerPairLabel d).symm (finProdFinEquiv.symm k).1).1).val
    (((printerPairLabel d).symm (finProdFinEquiv.symm k).1).2).val
    (finProdFinEquiv.symm k).2.val = _
  have hpair : finProdFinEquiv.symm k = (ℓ, j) := by
    exact Equiv.symm_apply_apply finProdFinEquiv (ℓ, j)
  rw [hpair]

/-- Physical row/column lookup on a prepared packed field-bit array reads
the exact labelled seed bit. The packed array's physical producer is a
separate obligation. -/
theorem physical_packed_field_bit (d modulus n : ℕ)
    (ℓ : Fin ((2 ^ d) ^ 2)) (j : Fin n) (out : List Bool) :
    ∃ steps ≤ 32 * (ℓ.val + n + j.val +
        (packedFieldBits d modulus n).length + 1) ^ 2,
      MatrixTableLookup.run steps
        (MatrixTableLookup.cfg (some MatrixTableLookup.start)
          MatrixTableLookup.initial (List.replicate ℓ.val true)
          (List.replicate n true) (List.replicate j.val true) []
          (packedFieldBits d modulus n) out) =
      MatrixTableLookup.cfg none MatrixTableLookup.initial
        (List.replicate ℓ.val true) (List.replicate n true)
        (List.replicate j.val true) [] (packedFieldBits d modulus n)
        (BitPrinter.bit d modulus
          (((printerPairLabel d).symm ℓ).1).val
          (((printerPairLabel d).symm ℓ).2).val j.val :: out) := by
  obtain ⟨steps, hsteps, hrun⟩ := MatrixTableLookup.lookup_run
    ℓ.val n j.val (packedFieldBits d modulus n) out
  refine ⟨steps, hsteps, ?_⟩
  simpa only [packedFieldBits_get] using hrun

#print axioms packedFieldBits_get
#print axioms physical_packed_field_bit

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
