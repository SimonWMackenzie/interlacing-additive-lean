import CurrentAdditive.V42FiniteFieldTheorem

namespace CurrentAdditive.V42FiniteFieldComplete

open Paper2 CurrentAdditive.SmallBias CurrentAdditive.FiniteFieldConstructor
open CurrentAdditive.FiniteFieldMachine CurrentAdditive.V42FiniteFieldList
open EthInapproximability.CurrentPaper

set_option maxHeartbeats 1500000

/-- The complete packed output has polynomially many actual bits. Labels
are its fixed row positions, so repeated arrays remain separate rows. -/
theorem complete_output_length_le (n r modulus : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    (CanonicalTable.packedFieldBits (degree n r) modulus n).length ≤
      4 * (target n r+1)^3 := by
  rw [CanonicalTable.packedFieldBits_length]
  have hR : order n r ≤ 2*(target n r+1) := (order_lt n r hn hr).le.trans (by omega)
  have hnN : n ≤ target n r+1 := by
    have hp : 1 ≤ 2 ^ r := Nat.one_le_two_pow
    unfold target
    nlinarith
  calc
    _ ≤ (2*(target n r+1))^2*(target n r+1) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hR 2) hnN
    _ = _ := by ring

/-- Generic v42 `yao:finite-field-list`: a single actual algorithm and
list work for all n,r>=1. Search, field choice, and the polynomial clock
are conclusions. The uniform law ranges over the complete printed row
labels, and the bit identity is pointwise on those same output rows. -/
theorem finite_field_list_unary (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    ∃ c < order n r,
      TrialSearch.firstPassing (degree n r) = some (TrialSearch.monicBits (degree n r) c) ∧
      let modulus := TrialSearch.monicBits (degree n r) c
      let arrays := StreamingPrinter.labelledWords (degree n r) modulus n
      let packed := CanonicalTable.packedFieldBits (degree n r) modulus n
      TrialSearch.makeList (degree n r) n = some arrays ∧
      arrays.length = (order n r)^2 ∧ arrays ≠ [] ∧
      packed.length = (order n r)^2*n ∧
      packed.length ≤ 4*(target n r+1)^3 ∧
      V42FiniteFieldTheorem.machine.OutputsWithin (V42FiniteFieldTheorem.input n r) packed
        (V42FiniteFieldTheorem.coefficient*(target n r+1)^5) ∧
      (∀ ℓ : Fin ((order n r)^2),
        let xy := (printerPairLabel (degree n r)).symm ℓ
        arrays[ℓ.val]? = some (xy.1.val, xy.2.val,
          StreamingPrinter.word (degree n r) modulus n xy.1.val xy.2.val)) ∧
      (∀ ℓ : Fin ((order n r)^2), ∀ j : Fin n,
        packed[ℓ.val*n+j.val]?.getD false = word (degree n r) modulus n ℓ j) ∧
      (∀ ℓ : Fin ((order n r)^2), ∀ j : Fin n,
        let xy := (printerPairLabel (degree n r)).symm ℓ
        (StreamingPrinter.word (degree n r) modulus n xy.1.val xy.2.val)[j.val]? =
          some (word (degree n r) modulus n ℓ j)) ∧
      (∀ x y, (StreamingPrinter.word (degree n r) modulus n x y).length = n) ∧
      (∀ (I : Finset (Fin n)) (z : Fin n → Bool),
        (FiniteLaw.uniform (Fin ((order n r)^2))).prob
          (fun ℓ => ∀ j ∈ I, word (degree n r) modulus n ℓ j = z j) ≤
            (1/2 : ℝ)^I.card + (1/2 : ℝ)^r) := by
  obtain ⟨c, hc, hfirst, hm⟩ := V42FiniteFieldTheorem.machine_outputs n r hn hr
  refine ⟨c, hc, hfirst, ?_⟩
  dsimp only
  have hlen := StreamingPrinter.labelledWords_length (degree n r)
    (TrialSearch.monicBits (degree n r) c) n
  have hnonempty : StreamingPrinter.labelledWords (degree n r)
      (TrialSearch.monicBits (degree n r) c) n ≠ [] := by
    intro he
    rw [he, List.length_nil] at hlen
    have hp : 0 < (2^degree n r)^2 := by positivity
    omega
  refine ⟨by simp [TrialSearch.makeList, hfirst], hlen, hnonempty,
    CanonicalTable.packedFieldBits_length _ _ _, complete_output_length_le n r _ hn hr,
    hm, ?_, ?_, ?_, StreamingPrinter.word_length _ _ _, ?_⟩
  · intro ℓ
    let xy := (printerPairLabel (degree n r)).symm ℓ
    have hxy : printerPairLabel (degree n r) xy = ℓ := Equiv.apply_symm_apply _ _
    simpa only [hxy] using
      streaming_labelledWords_getElem? (degree n r)
        (TrialSearch.monicBits (degree n r) c) n xy.1 xy.2
  · intro ℓ j
    exact CanonicalTable.packedFieldBits_get _ _ _ ℓ j
  · intro ℓ j
    exact streaming_word_getElem? _ _ _ _ _ j
  · intro I z
    exact pattern_prob_le _ _ _ (by positivity)
      (source_bias n r _ hn hr hfirst) I z

#print axioms complete_output_length_le
#print axioms finite_field_list_unary

end CurrentAdditive.V42FiniteFieldComplete
