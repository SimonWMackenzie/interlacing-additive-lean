import CurrentAdditive.WholeSequentialDenominator

set_option maxHeartbeats 1000000

namespace CurrentAdditive.RationalCandidateCompletion

open CurrentAdditive.SequentialCode
open CurrentAdditive.SequentialSourceCode
open CurrentAdditive.SequentialSourceResource
open CurrentAdditive.RationalBitBounds

private theorem generatedFeatures_size_le {Y : Type*}
    (t q D : Nat) (alphabet : Array Y) (ht : t ≤ q) :
    (generatedFeatures t D alphabet).size ≤
      (generatedFeatures q D alphabet).size := by
  induction q with
  | zero =>
      have : t = 0 := by omega
      subst t
      rfl
  | succ q ih =>
      by_cases h : t ≤ q
      · exact (ih h).trans (generatedFeatures_size_mono q D alphabet)
      · have : t = q + 1 := by omega
        subst t
        rfl

/-- The actual final feature count, rather than an abstract cap, controls
the common denominator produced by the literal sequential routine. -/
theorem sequentialMaterialized_denominator_final {Y : Type*}
    [DecidableEq Y] (D : Nat) (alphabet : Array (Y × ℚ))
    (ea : CommonDenominator
      (fun j : Fin alphabet.size => alphabet[j].2))
    (q : Nat) (out : Array ((Fin q → Y) × ℚ))
    (hrun : sequentialMaterialized D alphabet q = some out) :
    ∃ enc : CommonDenominator (fun i : Fin out.size => out[i].2),
      enc.denominator ≤ ea.denominator ^ q *
        (2 ^ (4 * (generatedFeatures q D (alphabet.map Prod.fst)).size *
            Nat.size ((generatedFeatures q D (alphabet.map Prod.fst)).size + 1))) ^
          (q * alphabet.size *
            (generatedFeatures q D (alphabet.map Prod.fst)).size) := by
  exact sequentialMaterialized_denominator_bounded D alphabet ea q
    (generatedFeatures q D (alphabet.map Prod.fst)).size
    (by intro t ht; exact generatedFeatures_size_le t q D _ ht)
    q (le_refl q) out hrun

/-- An exact binary-length bound on one shared denominator of all output
weights. The input law contributes q times its own denominator length;
the rational support reductions contribute the displayed manuscript-scale
q·m·M²·log(M+1) term. -/
theorem sequentialMaterialized_denominator_bits {Y : Type*}
    [DecidableEq Y] (D : Nat) (alphabet : Array (Y × ℚ))
    (ea : CommonDenominator
      (fun j : Fin alphabet.size => alphabet[j].2))
    (q : Nat) (out : Array ((Fin q → Y) × ℚ))
    (hrun : sequentialMaterialized D alphabet q = some out) :
    ∃ enc : CommonDenominator (fun i : Fin out.size => out[i].2),
      Nat.size enc.denominator ≤
        q * Nat.size ea.denominator +
        4 * q * alphabet.size *
          (generatedFeatures q D (alphabet.map Prod.fst)).size ^ 2 *
          Nat.size ((generatedFeatures q D (alphabet.map Prod.fst)).size + 1) + 1 := by
  let M := (generatedFeatures q D (alphabet.map Prod.fst)).size
  obtain ⟨enc, henc⟩ :=
    sequentialMaterialized_denominator_final D alphabet ea q out hrun
  refine ⟨enc, ?_⟩
  have hB : ea.denominator ≤ 2 ^ Nat.size ea.denominator :=
    le_of_lt (Nat.lt_size_self _)
  have hpow : ea.denominator ^ q ≤
      2 ^ (q * Nat.size ea.denominator) := by
    rw [mul_comm, pow_mul]
    exact Nat.pow_le_pow_left hB _
  have hupper : enc.denominator ≤
      2 ^ (q * Nat.size ea.denominator +
        4 * q * alphabet.size * M ^ 2 * Nat.size (M + 1)) := by
    calc
      enc.denominator ≤ ea.denominator ^ q *
          (2 ^ (4 * M * Nat.size (M + 1))) ^
            (q * alphabet.size * M) := by simpa [M] using henc
      _ ≤ 2 ^ (q * Nat.size ea.denominator) *
          (2 ^ (4 * M * Nat.size (M + 1))) ^
            (q * alphabet.size * M) :=
        Nat.mul_le_mul_right _ hpow
      _ = 2 ^ (q * Nat.size ea.denominator +
          4 * q * alphabet.size * M ^ 2 * Nat.size (M + 1)) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        ring
  have hb : enc.denominator <
      2 ^ (q * Nat.size ea.denominator +
        4 * q * alphabet.size * M ^ 2 * Nat.size (M + 1) + 1) := by
    calc
      enc.denominator ≤ 2 ^ (q * Nat.size ea.denominator +
          4 * q * alphabet.size * M ^ 2 * Nat.size (M + 1)) := hupper
      _ < 2 ^ (q * Nat.size ea.denominator +
          4 * q * alphabet.size * M ^ 2 * Nat.size (M + 1) + 1) := by
        exact Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)
  have hbits := (Nat.size_le).mpr hb
  simpa [M, pow_two, mul_assoc] using hbits

#print axioms sequentialMaterialized_denominator_final
#print axioms sequentialMaterialized_denominator_bits

end CurrentAdditive.RationalCandidateCompletion
