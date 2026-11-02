import CurrentAdditive.GaussPackedMachine64
import Mathlib.Tactic

set_option maxHeartbeats 1000000

namespace CurrentAdditive.GaussPackedClock64

open EthInapproximability.CurrentPaper

theorem parsed_reset_empty (bank : BitMachineBankCodec.Bank 3)
    (r : Fin 21) :
    GaussPackedFetch64.parsedStack bank
      (GaussGetterReset64.resetBank r) = [] := by
  unfold GaussPackedFetch64.parsedStack GaussPackedParse64.frame
  simp only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
  apply BitMachineStackEmbedding.bank_outside
  rintro ⟨q, hq⟩
  have hr : 32 ≤ (GaussGetterReset64.resetBank r).val ∧
      (GaussGetterReset64.resetBank r).val < 53 := by
    fin_cases r <;> decide
  cases q with
  | inl q =>
      fin_cases q <;> have hv := congrArg Fin.val hq <;>
        simp [GaussPackedParse64.locate] at hv <;> omega
  | inr q =>
      fin_cases q <;> have hv := congrArg Fin.val hq <;>
        simp [GaussPackedParse64.locate] at hv <;> omega

theorem preparation_clock (bank : BitMachineBankCodec.Bank 3)
    (row column : Nat) :
    GaussOneFetchProgram64.preparationClock
      (GaussPackedFetch64.parsedStack bank) row column =
      2 * row + 2 * column + 31 := by
  simp [GaussOneFetchProgram64.preparationClock,
    GaussOneFetchProgram64.resetClock,
    GaussOneFetchProgram64.copyClock, parsed_reset_empty]
  omega

theorem field_lengths {m k : Nat} (B : Fin m → Fin k → ℚ)
    (i : Fin m) (j : Fin k) :
    (GaussPhysical.encodeTypedMatrix B).length ≤
        (GaussPackedFetch64.input B i j).length ∧
      i.val ≤ (GaussPackedFetch64.input B i j).length ∧
      j.val ≤ (GaussPackedFetch64.input B i j).length := by
  have h0 := BitMachineBankCodec.word_length_le_encode
    (GaussPackedFetch64.packet B i j) (0 : Fin 3)
  have h1 := BitMachineBankCodec.word_length_le_encode
    (GaussPackedFetch64.packet B i j) (1 : Fin 3)
  have h2 := BitMachineBankCodec.word_length_le_encode
    (GaussPackedFetch64.packet B i j) (2 : Fin 3)
  simpa [GaussPackedFetch64.packet, GaussPackedFetch64.input] using
    And.intro h0 (And.intro h1 h2)

theorem valid_clock {m k : Nat} (B : Fin m → Fin k → ℚ)
    (i : Fin m) (j : Fin k) :
    let n := (GaussPackedFetch64.input B i j).length
    7 * (n + 1) +
      GaussOneFetchProgram64.preparationClock
        (GaussPackedFetch64.parsedStack (GaussPackedFetch64.packet B i j))
        i.val j.val +
      140 * ((GaussPhysical.encodeTypedMatrix B).length + 1)^3 + 2 ≤
      (n + 2)^12 := by
  dsimp only
  obtain ⟨hm, hi, hj⟩ := field_lengths B i j
  rw [preparation_clock]
  let n := (GaussPackedFetch64.input B i j).length
  have hp : ((GaussPhysical.encodeTypedMatrix B).length + 1)^3 ≤ (n+1)^3 := by
    exact Nat.pow_le_pow_left (by omega) 3
  have hlin : n + 1 ≤ (n + 1)^3 := by
    have h1 : 1 ≤ n + 1 := by omega
    nlinarith [sq_nonneg (n : ℤ)]
  have hbudget : 200 * (n+1)^3 ≤ (n+2)^12 := by
    have h9 : 200 ≤ (n+2)^9 := by
      calc 200 ≤ 512 := by omega
        _ = 2^9 := by norm_num
        _ ≤ (n+2)^9 := Nat.pow_le_pow_left (by omega) 9
    have h3 : (n+1)^3 ≤ (n+2)^3 := Nat.pow_le_pow_left (by omega) 3
    have hmul := Nat.mul_le_mul h9 h3
    calc
      200 * (n+1)^3 ≤ (n+2)^9 * (n+2)^3 := hmul
      _ = (n+2)^12 := by ring
  have hpre : 2*i.val + 2*j.val + 31 ≤ 4*n + 31 := by omega
  have htotal : 7*(n+1) + (4*n+31) + 140*(n+1)^3 + 2 ≤
      200*(n+1)^3 := by
    nlinarith
  exact le_trans (by nlinarith) (le_trans htotal hbudget)

theorem canonical_outputs_budget {m k : Nat}
    (B : Fin m → Fin k → ℚ) (i : Fin m) (j : Fin k) :
    GaussPackedMachine64.machine.OutputsWithin
      (GaussPackedFetch64.input B i j)
      (CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B i j)))
      (((GaussPackedFetch64.input B i j).length + 2)^12) := by
  exact BitMachine.outputsWithin_mono GaussPackedMachine64.machine
    (GaussPackedMachine64.canonical_outputs B i j)
    (valid_clock B i j)

#print axioms canonical_outputs_budget

end CurrentAdditive.GaussPackedClock64
