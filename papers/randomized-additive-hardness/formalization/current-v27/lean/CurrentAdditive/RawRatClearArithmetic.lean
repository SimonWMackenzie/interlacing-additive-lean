import CurrentAdditive.RawRatDivisionEmbedded
import EthInapproximability.CurrentPaper.RegionClear
import Mathlib.Tactic

/-! Clear every division scratch bank and the spent dividend, preserving GCD. -/
namespace CurrentAdditive.RawRatClearArithmetic

open Turing
open EthInapproximability.CurrentPaper
open BitMachineEncoding

abbrev Bank := RawRatPreparation.Bank

def location : Fin 6 ↪ Fin 13 where
  toFun i := if i = 0 then 3 else ⟨i.val + 7, by omega⟩
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [Fin.ext_iff]

def program := RegionClear.prog 6 location

def result (S : Bank) : Bank := BitMachineClearBank.cleared location S

def clock (S : Bank) : Nat :=
  6 * (BitMachineBankCodec.encode S).length + 8

theorem run (S : Bank) :
    ∃ t ≤ clock S,
      ((advance program)^[t])
        (⟨some (0 : Fin 8), ((), none), S⟩ :
          TM2.Cfg (fun _ : Fin 13 => Bool) _ _) =
        ⟨none, ((), none), result S⟩ := by
  obtain ⟨t, ht, hr⟩ := RegionClear.clear_run 6 location
    location.injective S (BitMachineBankCodec.encode S).length
    (fun i => BitMachineBankCodec.word_length_le_encode S (location i))
  exact ⟨t, ht, hr⟩

theorem cleared (S : Bank) (i : Fin 6) : result S (location i) = [] :=
  BitMachineClearBank.cleared_bank location S i

theorem gcd_preserved (S : Bank) : result S 4 = S 4 := by
  apply BitMachineClearBank.cleared_foreign
  intro i
  fin_cases i <;> simp [location]

theorem numerator_preserved (S : Bank) : result S 5 = S 5 := by
  apply BitMachineClearBank.cleared_foreign
  intro i
  fin_cases i <;> simp [location]

theorem denominator_preserved (S : Bank) : result S 6 = S 6 := by
  apply BitMachineClearBank.cleared_foreign
  intro i
  fin_cases i <;> simp [location]

end CurrentAdditive.RawRatClearArithmetic
