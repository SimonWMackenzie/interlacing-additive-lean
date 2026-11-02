import CurrentAdditive.RationalSubtractPairMachine
import EthInapproximability.CurrentPaper.BitMachineClearBank
import EthInapproximability.CurrentPaper.BitMachineBroadcast

/-! A literal packed-bank pass reverses the subtraction denominator into slot 11. -/

namespace EthInapproximability.CurrentPaper.RationalSubtractDenReverse

open Turing TM2.Stmt BitMachineEncoding

abbrev Bank := RationalSubtractCore.Bank
abbrev Control := Unit × Option Bool

inductive Label where
  | clear | reverse | done
  deriving DecidableEq, Fintype

def start : Label := .clear
def initial : Control := ((), none)

def program : Label → TM2.Stmt (fun _ : Fin 32 => Bool) Label Control
  | .clear => BitMachineClearBank.clearStep 11 .clear .reverse
  | .reverse => BitMachineBroadcast.scanStep 12 11 .reverse .done
  | .done => halt

def cleared (S : Bank) : Bank := Function.update S 11 []
def reversedBank (S : Bank) : Bank :=
  BitMachineBroadcast.contents (12 : Fin 32) 11 (cleared S) [] (S 12).reverse

theorem local_run (S : Bank) :
    ((advance program)^[(S 11).length + 1 + ((S 12).length+1) + 1])
      (⟨some start, initial, S⟩ :
        TM2.Cfg (fun _ : Fin 32 => Bool) Label Control) =
      ⟨none, initial, reversedBank S⟩ := by
  have hc := BitMachineClearBank.clear_one_run program (11 : Fin 32)
    .clear .reverse (by rfl) () S
  have hs : ((advance program)^[(S 12).length+1])
      (⟨some .reverse, initial, cleared S⟩ :
        TM2.Cfg (fun _ : Fin 32 => Bool) Label Control) =
      ⟨some .done, initial, reversedBank S⟩ := by
    have h := BitMachineBroadcast.scan_run program (12 : Fin 32) 11
      (by decide) .reverse .done (by rfl) () none (S 12) [] (cleared S)
    have hi : BitMachineBroadcast.contents (12 : Fin 32) 11
        (cleared S) (S 12) [] = cleared S := by
      have hsrc : (cleared S) 12 = S 12 := by simp [cleared]
      have htmp : (cleared S) 11 = [] := by simp [cleared]
      simp only [BitMachineBroadcast.contents, ← hsrc,
        Function.update_eq_self, ← htmp]
    rw [hi] at h
    simpa [BitMachineBroadcast.run, reversedBank, cleared] using h
  have hd : advance program
      (⟨some .done, initial, reversedBank S⟩ :
        TM2.Cfg (fun _ : Fin 32 => Bool) Label Control) =
      ⟨none, initial, reversedBank S⟩ := rfl
  have hcs : ((advance program)^[(S 11).length+1])
      (⟨some start, initial, S⟩ :
        TM2.Cfg (fun _ : Fin 32 => Bool) Label Control) =
      ⟨some .reverse, initial, cleared S⟩ := by
    simpa only [start, initial, cleared] using hc
  rw [Nat.add_comm ((S 11).length+1+((S 12).length+1)) 1,
    Function.iterate_add_apply, Function.iterate_one]
  rw [Nat.add_comm ((S 11).length+1) ((S 12).length+1),
    Function.iterate_add_apply, hcs, hs]
  exact hd

theorem word_bound (S : Bank) (j : Fin 32) :
    ((reversedBank S) j).length ≤
      (BitMachineBankCodec.encode S).length := by
  let B := (BitMachineBankCodec.encode S).length
  have h := BitMachineBankCodec.word_length_le_encode S
  by_cases hj11 : j = 11
  · subst j
    simpa [reversedBank, BitMachineBroadcast.contents, cleared] using h (12 : Fin 32)
  · by_cases hj12 : j = 12
    · subst j
      simp [reversedBank, BitMachineBroadcast.contents, cleared]
    · simpa [reversedBank, BitMachineBroadcast.contents, cleared,
        Function.update_of_ne hj11, Function.update_of_ne hj12] using h j

theorem output_size (S : Bank) :
    (BitMachineBankCodec.encode (reversedBank S)).length ≤
      65*((BitMachineBankCodec.encode S).length+1) := by
  rw [BitMachineBankCodec.encode_length]
  have hsum : (∑ j : Fin 32, ((reversedBank S) j).length) ≤
      ∑ _j : Fin 32, (BitMachineBankCodec.encode S).length := by
    apply Finset.sum_le_sum
    intro j _
    exact word_bound S j
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at hsum
  omega

noncomputable def machine : BitMachine.Machine :=
  BitMachineBankWrapper.machine program start initial

noncomputable def result (input : List Bool) : List Bool :=
  BitMachineBankWrapper.result reversedBank input

theorem polytime : BitMachine.Polytime result := by
  apply BitMachineBankWrapper.polytime program start initial reversedBank 4 1 65 1
  · intro S
    let t := (S 11).length + 1 + ((S 12).length+1) + 1
    refine ⟨t, ⟨none, initial, reversedBank S⟩, ?_, ?_, rfl, rfl⟩
    · have h11 := BitMachineBankCodec.word_length_le_encode S (11 : Fin 32)
      have h12 := BitMachineBankCodec.word_length_le_encode S (12 : Fin 32)
      simp only [pow_one]
      omega
    · exact local_run S
  · intro S
    simpa only [pow_one] using output_size S

theorem result_encode (S : Bank) :
    result (BitMachineBankCodec.encode S) =
      BitMachineBankCodec.encode (reversedBank S) := by
  simp [result, BitMachineBankWrapper.result]

end EthInapproximability.CurrentPaper.RationalSubtractDenReverse
