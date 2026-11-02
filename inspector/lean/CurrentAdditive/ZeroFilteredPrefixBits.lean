import CurrentAdditive.ZeroFilteredWeightBits

set_option maxHeartbeats 1000000

namespace CurrentAdditive.ZeroFilteredWeightBits

open SequentialCode SequentialSourceCode RationalBitBounds IntegerBitSupport
open LabelTrace IndependentSupport TransientArithmetic
open RationalCandidateCompletion SequentialSourceResource

/-- A finite path of actual successful deletions cannot be longer than its
starting support. This charges the prefix without a supplied loop count. -/
theorem eliminationTrace_length_le {α : Type*} (n : Nat) (φ : α → Fin n → ℚ)
    (source current : Array (α × ℚ)) (t : Nat)
    (htrace : EliminationTrace n φ t source current) : t ≤ source.size := by
  induction htrace with
  | refl => omega
  | step source next current f t hfree hstep hrest ih =>
      have hshrink := compressSourceOnceMaterialized_size_lt n φ source next hstep
      omega

theorem generatedFeatures_original_cap (D Q : Nat) (alphabet : Array (Nat × ℚ))
    (hmass : sourceMass alphabet = 1) (q : Nat) (hq : q ≤ Q) :
    (generatedFeatures q D ((positiveLaw alphabet).map Prod.fst)).size ≤
      (1 + Q * alphabet.size) ^ D := by
  obtain ⟨trace, _, _⟩ := positiveLaw_trace_exact alphabet hmass
  have hsize : (positiveLaw alphabet).size ≤ alphabet.size := by
    simpa using Fintype.card_le_of_injective trace trace.injective
  have hh := SequentialDimensionPolynomialProduction.generatedFeatures_size_le_polynomial
    q D ((positiveLaw alphabet).map Prod.fst)
  have hbase : 1 + q * (positiveLaw alphabet).size ≤ 1 + Q * alphabet.size :=
    Nat.add_le_add_left (Nat.mul_le_mul hq hsize) 1
  have hh' : (generatedFeatures q D ((positiveLaw alphabet).map Prod.fst)).size ≤
      (1 + q * (positiveLaw alphabet).size) ^ D := by simpa using hh
  exact hh'.trans (Nat.pow_le_pow_left hbase D)

/-- Every retained array reached inside any stage up to Q has polynomial
canonical rational fields, measured in the ORIGINAL encoded law. The exact
trace itself supplies the deletion-count bound. -/
theorem sequentialPreprocessed_every_prefix_weights
    (D : Nat) (alphabet : Array (Nat × ℚ))
    (hnonneg : alphabet.all (fun e => decide (0 ≤ e.2)) = true)
    (hmass : sourceMass alphabet = 1) (Q q : Nat) (hq : q < Q)
    (prev : Array ((Fin q → Nat) × ℚ))
    (hprev : sequentialPreprocessed D alphabet q = some prev)
    (current : Array ((Fin (q + 1) → Nat) × ℚ)) (t : Nat)
    (htrace :
      let F := generatedFeatures (q + 1) D ((positiveLaw alphabet).map Prod.fst)
      EliminationTrace F.size (fun v j => generatedFeatureValue v F[j]) t
        (appendSource prev (positiveLaw alphabet)) current) :
    ∀ i : Fin current.size,
      Fits (2 * budget D Q alphabet.size
        (CodeDTargetV2.alphabetBytes alphabet).length + 1) current[i].2 := by
  let L := (CodeDTargetV2.alphabetBytes alphabet).length
  let P := (1 + Q * alphabet.size) ^ D
  let B := budget D Q alphabet.size L
  let F := generatedFeatures (q + 1) D ((positiveLaw alphabet).map Prod.fst)
  let n := F.size
  let φ : (Fin (q + 1) → Nat) → Fin n → ℚ :=
    fun v j => generatedFeatureValue v F[j]
  let extended := appendSource prev (positiveLaw alphabet)
  obtain ⟨encPrev, hprevBits, _⟩ := sequentialPreprocessed_all_stage_denominators
    D alphabet hnonneg hmass Q q (by omega) prev hprev
  let original := inputLawCommonDenominator
    (fun i : Fin alphabet.size => alphabet[i].2)
  obtain ⟨ea, hea⟩ := positiveLaw_commonDenominator alphabet hmass original
  have heaBits : Nat.size ea.denominator ≤ L := by
    rw [hea]
    exact inputLaw_denominator_le_alphabetBytes alphabet
  let encExtended := appendSource_commonDenominator prev (positiveLaw alphabet) encPrev ea
  have hextBits : Nat.size encExtended.denominator ≤ B + L + 1 := by
    have hh := size_le_of_pow_bound (mul_fits_bits
      (le_of_lt (Nat.lt_size_self encPrev.denominator))
      (le_of_lt (Nat.lt_size_self ea.denominator)))
    change Nat.size (encPrev.denominator * ea.denominator) ≤ B + L + 1
    dsimp only [B, L] at *
    omega
  have hprevPos : SourcePositive prev := by
    obtain ⟨other, hother, hpos⟩ := sequentialPreprocessed_total D alphabet q
    rw [hprev] at hother
    cases Option.some.inj hother
    exact hpos
  have hextPos : SourcePositive extended :=
    appendSource_positive prev (positiveLaw alphabet) hprevPos
      (positiveLaw_positive alphabet)
  have hfilteredMass : sourceMass (positiveLaw alphabet) = 1 := by
    rw [← (positiveLaw_mass_moments alphabet hnonneg
      (n := 0) (fun _ i => Fin.elim0 i)).1]
    exact hmass
  have hextMass : sourceMass extended = 1 := by
    rw [SequentialAppendMoments.sourceMass_appendSource,
      sequentialPreprocessed_mass D alphabet hnonneg hmass q prev hprev,
      hfilteredMass, one_mul]
  have hn : 0 < n := generatedFeatures_pos _ _ _
  have hφ : ∀ x j, φ x j = 0 ∨ φ x j = 1 := by
    intro x j
    dsimp [φ, generatedFeatureValue]
    split_ifs <;> simp
  have hnP : n ≤ P := generatedFeatures_original_cap D Q alphabet hmass
    (q + 1) (by omega)
  have hprevCap : prev.size ≤ P :=
    (sequentialIndependent_size_le_features_all D (positiveLaw alphabet) q prev hprev).trans
      (generatedFeatures_original_cap D Q alphabet hmass q (by omega))
  obtain ⟨trace, _, _⟩ := positiveLaw_trace_exact alphabet hmass
  have hfilteredSize : (positiveLaw alphabet).size ≤ alphabet.size := by
    simpa using Fintype.card_le_of_injective trace trace.injective
  have ht : t ≤ alphabet.size * P := by
    have hlen := eliminationTrace_length_le n φ extended current t htrace
    have hex : extended.size ≤ alphabet.size * P := by
      rw [appendSource_size]
      exact (Nat.mul_le_mul hprevCap hfilteredSize).trans_eq (Nat.mul_comm _ _)
    exact hlen.trans hex
  have hterm : 4 * t * n * Nat.size (n + 1) ≤
      4 * alphabet.size * P ^ 2 * Nat.size (P + 1) := by
    have hh := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.mul_le_mul_left 4 ht) hnP)
      (Nat.size_le_size (by omega : n + 1 ≤ P + 1))
    convert hh using 1 <;> ring
  have hsmall : L + 4 * alphabet.size * P ^ 2 * Nat.size (P + 1) + 1 ≤ B := by
    have hQ : 1 ≤ Q := by omega
    have hL := Nat.mul_le_mul_right L hQ
    have hcharge := Nat.mul_le_mul_left
      (4 * alphabet.size * P ^ 2 * Nat.size (P + 1)) hQ
    dsimp [B, budget]
    dsimp only [P] at *
    nlinarith
  have hall := traced_weights_fit n φ hn hφ extended current t htrace
    hextPos hextMass encExtended
  intro i
  apply fits_mono (hall i)
  change Nat.size encExtended.denominator +
    4 * t * n * Nat.size (n + 1) + 1 ≤ 2 * B + 1
  omega

#print axioms eliminationTrace_length_le
#print axioms sequentialPreprocessed_every_prefix_weights

end CurrentAdditive.ZeroFilteredWeightBits
