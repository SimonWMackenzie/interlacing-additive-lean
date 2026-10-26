import CurrentAdditive.RationalSubtractRouteSpec

namespace EthInapproximability.CurrentPaper.RationalSubtractRouteClock

open RationalSubtractRoute RationalSubtractRouteRun

abbrev Bank := RationalSubtractCore.Bank

def WordBound (S : Bank) (B : Nat) : Prop :=
  ∀ j : Fin 32, (S j).length ≤ B

theorem precleared_bound (S : Bank) (B : Nat) (h : WordBound S B) :
    WordBound (precleared S) B := by
  intro j
  by_cases hj : ∃ i : Fin 2, preSlots i = j
  · simp [precleared, BitMachineClearBank.cleared, hj]
  · simpa [precleared, BitMachineClearBank.cleared, hj] using h j

theorem copy_bound (phase : Fin 7) (S : Bank) (B : Nat)
    (h : WordBound S B) : WordBound (copied phase S) (2*B) := by
  intro j
  rw [RationalSubtractRouteSpec.copied_update]
  by_cases ht : j = (26 : Fin 32)
  · subst j
    simp
  · rw [Function.update_of_ne ht]
    by_cases hd : j = copySlots phase 1
    · subst j
      simp
      have ha := h (copySlots phase 0)
      have hb := h (copySlots phase 1)
      simp only [List.length_append] at *
      omega
    · rw [Function.update_of_ne hd]
      have hj := h j
      omega

theorem reverse_bound (S : Bank) (B : Nat) (h : WordBound S B) :
    WordBound
      (BitMachineBroadcast.contents (2 : Fin 32) 15 S [] (S 2).reverse) B := by
  intro j
  by_cases h15 : j = (15 : Fin 32)
  · subst j
    simp [BitMachineBroadcast.contents]
    exact h 2
  · by_cases h2 : j = (2 : Fin 32)
    · subst j
      simp [BitMachineBroadcast.contents]
    · simpa [BitMachineBroadcast.contents,
        Function.update_of_ne h15, Function.update_of_ne h2] using h j

theorem cleared_bound (S : Bank) (B : Nat) (h : WordBound S B) :
    WordBound (BitMachineClearBank.cleared clearSlots S) B := by
  intro j
  by_cases hj : ∃ i : Fin 5, clearSlots i = j
  · simp [BitMachineClearBank.cleared, hj]
  · simpa [BitMachineClearBank.cleared, hj] using h j

theorem routed_bound (S : Bank) (B : Nat) (h : WordBound S B) :
    WordBound (routed S) (128*B) := by
  have h1 := copy_bound 0 S B h
  have h2 := copy_bound 1 (copied 0 S) (2*B) h1
  have h3 := copy_bound 2 (copied 1 (copied 0 S)) (4*B)
    (by simpa only [← Nat.mul_assoc, Nat.reduceMul] using h2)
  have h4 := copy_bound 3 (copied 2 (copied 1 (copied 0 S))) (8*B)
    (by simpa only [← Nat.mul_assoc, Nat.reduceMul] using h3)
  have h5 := copy_bound 4 (copied 3 (copied 2 (copied 1 (copied 0 S)))) (16*B)
    (by simpa only [← Nat.mul_assoc, Nat.reduceMul] using h4)
  have h6 := copy_bound 5 (copied 4 (copied 3 (copied 2 (copied 1 (copied 0 S)))))
    (32*B) (by simpa only [← Nat.mul_assoc, Nat.reduceMul] using h5)
  have h7 := copy_bound 6
    (copied 5 (copied 4 (copied 3 (copied 2 (copied 1 (copied 0 S))))))
    (64*B) (by simpa only [← Nat.mul_assoc, Nat.reduceMul] using h6)
  have hr := reverse_bound _ (128*B)
    (by simpa only [← Nat.mul_assoc, Nat.reduceMul] using h7)
  simpa only [routed] using cleared_bound _ (128*B) hr

theorem routed_size (S : Bank) :
    (BitMachineBankCodec.encode (routed (precleared S))).length ≤
      8200*((BitMachineBankCodec.encode S).length+1) := by
  let B := (BitMachineBankCodec.encode S).length
  have h0 : WordBound S B := by
    intro j
    exact BitMachineBankCodec.word_length_le_encode S j
  have h1 := precleared_bound S B h0
  have h2 := routed_bound (precleared S) B h1
  have hsum : (∑ j : Fin 32, ((routed (precleared S)) j).length) ≤
      ∑ _j : Fin 32, 128*B := by
    apply Finset.sum_le_sum
    intro j _
    exact h2 j
  rw [BitMachineBankCodec.encode_length]
  simp only [Finset.sum_const_zero, Finset.sum_const, Finset.card_fin,
    nsmul_eq_mul] at hsum
  omega

noncomputable def result (input : List Bool) : List Bool :=
  BitMachineBankWrapper.result (fun S : Bank => routed (precleared S)) input

theorem polytime : BitMachine.Polytime result := by
  apply BitMachineBankWrapper.polytime program start initial
    (fun S : Bank => routed (precleared S)) 68 1 8200 1
  · intro S
    obtain ⟨t,ht,hr⟩ := full_run S
    refine ⟨t, ⟨none, initial, routed (precleared S)⟩, ?_, hr, rfl, rfl⟩
    simp only [pow_one]
    omega
  · intro S
    simpa only [pow_one] using routed_size S

end EthInapproximability.CurrentPaper.RationalSubtractRouteClock
