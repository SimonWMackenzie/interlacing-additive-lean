import CurrentAdditive.BinaryGCDPacket
import EthInapproximability.CurrentPaper.RegionClear
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! Scrub the five scratch banks before Euclid, including malformed but framed inputs. -/
namespace CurrentAdditive.BinaryGCDAllInput

open Turing
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper
open CurrentAdditive.BinaryGCDCore CurrentAdditive.BinaryGCDBound

def scratchBank (i : Fin 5) : Fin 7 := ⟨i.val + 2, by omega⟩

theorem scratchBank_injective : Function.Injective scratchBank := by
  intro i j h
  exact Fin.ext (by have := congrArg Fin.val h; simp [scratchBank] at this; omega)

def clearProgram := RegionClear.prog 5 scratchBank

def program := BitMachineRawSequence.program clearProgram
  BinaryGCDCore.program Label.checkDivisor ((), none) BinaryGCDCore.initial

def canonicalBank (S : Fin 7 → List Bool) : Fin 7 → List Bool :=
  BinaryGCDCore.bank (S 0) (S 1) [] [] [] [] []

theorem cleared_eq_canonical (S : Fin 7 → List Bool) :
    BitMachineClearBank.cleared scratchBank S = canonicalBank S := by
  funext j
  by_cases hj : j.val < 2
  · have hn : ¬∃ i : Fin 5, scratchBank i = j := by
      rintro ⟨i, hi⟩
      have hv := congrArg Fin.val hi
      simp [scratchBank] at hv
      omega
    fin_cases j <;>
      simp_all [BitMachineClearBank.cleared, scratchBank, canonicalBank,
        BinaryGCDCore.bank, BitMachineBinaryDivision.bank]
  · have he : ∃ i : Fin 5, scratchBank i = j := by
      refine ⟨⟨j.val - 2, by omega⟩, Fin.ext ?_⟩
      simp [scratchBank]
      omega
    fin_cases j <;>
      simp_all [BitMachineClearBank.cleared, scratchBank, canonicalBank,
        BinaryGCDCore.bank, BitMachineBinaryDivision.bank]

def clearClock (N : Nat) : Nat := 5 * N + 7

theorem clear_run (S : Fin 7 → List Bool) :
    ∃ t ≤ clearClock (BitMachineBankCodec.encode S).length,
      ((advance clearProgram)^[t])
        ⟨some 0, ((), none), S⟩ =
        ⟨none, ((), none), canonicalBank S⟩ := by
  obtain ⟨t, ht, hr⟩ := RegionClear.clear_run 5 scratchBank
    scratchBank_injective S (BitMachineBankCodec.encode S).length
    (fun i => BitMachineBankCodec.word_length_le_encode S (scratchBank i))
  refine ⟨t, by simpa [clearClock] using ht, ?_⟩
  simpa only [cleared_eq_canonical] using hr

def clock (N : Nat) : Nat := clearClock N + startClock (2 * N) + 1

theorem roundClock_mono {a b : Nat} (h : a ≤ b) :
    roundClock a ≤ roundClock b := by
  unfold roundClock
  gcongr

theorem startClock_mono {a b : Nat} (h : a ≤ b) :
    startClock a ≤ startClock b := by
  unfold startClock
  gcongr
  exact roundClock_mono h

theorem raw_total (S : Fin 7 → List Bool) :
    ∃ (t : Nat) (c : TM2.Cfg (fun _ : Fin 7 => Bool)
      (BitMachineRawSequence.Label (Fin 7) BinaryGCDCore.Label)
      ((Unit × Option Bool) × BinaryGCDCore.Control)),
      t ≤ clock (BitMachineBankCodec.encode S).length ∧
      ((advance program)^[t])
        ⟨some (BitMachineRawSequence.leftLabel (0 : Fin 7)),
          (((), none), BinaryGCDCore.initial), S⟩ = c ∧
      c.l = none ∧
      (0 < EncodedCommunication.bitsValue (S 1) →
        EncodedCommunication.bitsValue (c.stk 1) =
          Nat.gcd (BitMachineBinaryDivision.msbValue (S 0))
            (EncodedCommunication.bitsValue (S 1))) := by
  obtain ⟨ta, hta, ha⟩ := clear_run S
  obtain ⟨tb, c, htb, hb, hc, hv⟩ := BinaryGCDBound.raw_total (S 0) (S 1)
  have hbank : canonicalBank S =
      BinaryGCDCore.bank (S 0) (S 1) [] [] [] [] [] := rfl
  have hb' : ((advance BinaryGCDCore.program)^[tb])
      (⟨some Label.checkDivisor, BinaryGCDCore.initial, canonicalBank S⟩ :
        BinaryGCDCore.Config) = c := by
    simpa [BinaryGCDCore.run, BinaryGCDCore.cfg, hbank] using hb
  have hc' : c = ⟨none, c.var, c.stk⟩ := by
    cases c with
    | mk l v T => cases l <;> simp_all
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs
    clearProgram BinaryGCDCore.program (0 : Fin 7) Label.checkDivisor
    ((), none) ((), none) BinaryGCDCore.initial c.var S (canonicalBank S) c.stk
    ta tb ha (by rw [← hc']; exact hb')
  refine ⟨t, ⟨none, (((), none), c.var), c.stk⟩, ?_, hrun, rfl, ?_⟩
  · have h0 := BitMachineBankCodec.word_length_le_encode S (0 : Fin 7)
    have h1 := BitMachineBankCodec.word_length_le_encode S (1 : Fin 7)
    have hsize : (S 0).length + (S 1).length ≤
        2 * (BitMachineBankCodec.encode S).length := by omega
    have hm := startClock_mono hsize
    unfold clock
    omega
  · exact hv

end CurrentAdditive.BinaryGCDAllInput
