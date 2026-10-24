import CurrentAdditive.BinaryGCDCore
import CurrentAdditive.EuclidCount

/-! Uniform bit-length clock for the physical Euclidean controller. -/
namespace CurrentAdditive.BinaryGCDBound

open EthInapproximability.CurrentPaper
open CurrentAdditive.BinaryGCDCore

def roundClock (N : Nat) : Nat := (N + 1) * (8 * N + 9) + 12 * N + 7

private theorem run_add {c d : Config} {t : Nat} (h : run t c = d) (u : Nat) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

theorem cycleTimeBound_le (input divisor : List Bool) (N : Nat)
    (hi : input.length ≤ N) (hd : divisor.length ≤ N) :
    cycleTimeBound input divisor ≤ roundClock N := by
  have htime := BitMachineBinaryDivision.standard_time_bound input divisor
  have hq := BitMachineBinaryDivision.divideFrom_quotient_length
    input divisor [] []
  have hr := BitMachineBinaryDivision.divideFrom_remainder_length
    input divisor [] [] input.length (by simp) le_rfl
  have hinput : input.length + divisor.length ≤ 2 * N := by omega
  have hq' : (quotient input divisor).length ≤ N := by
    simpa [quotient] using (show
      (BitMachineBinaryDivision.divideFrom input divisor [] []).2.length ≤ N from by
        simpa using hq.le.trans hi)
  have hr' : (remainder input divisor).length ≤ 2 * N := by
    change (BitMachineBinaryDivision.divideFrom input divisor [] []).1.length ≤ 2 * N
    omega
  have houter : (input.length + 1) *
      (4 * (input.length + divisor.length + 1) + 5) ≤
      (N + 1) * (8 * N + 9) := by
    gcongr
    omega
  unfold cycleTimeBound roundClock
  omega

theorem euclid_bounded (input divisor : List Bool) (N : Nat)
    (hi : input.length ≤ N) (hd : divisor.length ≤ N)
    (hpos : 0 < EncodedCommunication.bitsValue divisor) :
    ∃ (t : Nat) (c : Config),
      t ≤ CurrentAdditive.EuclidCount.steps
        (BitMachineBinaryDivision.msbValue input)
        (EncodedCommunication.bitsValue divisor) * roundClock N ∧
      run t (cfg (some (.divide .outer)) initial input divisor [] [] [] [] []) = c ∧
      c.l = none ∧
      EncodedCommunication.bitsValue (c.stk 1) =
        Nat.gcd (BitMachineBinaryDivision.msbValue input)
          (EncodedCommunication.bitsValue divisor) := by
  have main : ∀ bval : Nat, ∀ (a b : List Bool),
      EncodedCommunication.bitsValue b = bval →
      a.length ≤ N → b.length ≤ N → 0 < bval →
      ∃ (t : Nat) (c : Config),
        t ≤ CurrentAdditive.EuclidCount.steps
          (BitMachineBinaryDivision.msbValue a)
          (EncodedCommunication.bitsValue b) * roundClock N ∧
        run t (cfg (some (.divide .outer)) initial a b [] [] [] [] []) = c ∧
        c.l = none ∧
        EncodedCommunication.bitsValue (c.stk 1) =
          Nat.gcd (BitMachineBinaryDivision.msbValue a)
            (EncodedCommunication.bitsValue b) := by
    intro bval
    induction bval using Nat.strong_induction_on with
    | h bval ih =>
        intro a b hval hla hlb hbval
        have hb : 0 < EncodedCommunication.bitsValue b := by omega
        have hclock := cycleTimeBound_le a b N hla hlb
        by_cases hz : (remainder a b).any id = false
        · obtain ⟨t, ht, hr⟩ := cycle_zero a b hz
          let c : Config := cfg none
            ⟨BitMachineBinaryDivision.initial, false, none⟩
            [] b (remainder a b) (quotient a b) [] [] []
          have hzero : EncodedCommunication.bitsValue (remainder a b) = 0 := by
            have hiff := any_iff_value_ne_zero (remainder a b)
            rw [hz] at hiff
            by_contra hn
            simp [hn] at hiff
          have hs : CurrentAdditive.EuclidCount.steps
              (BitMachineBinaryDivision.msbValue a)
              (EncodedCommunication.bitsValue b) = 1 := by
            rw [CurrentAdditive.EuclidCount.steps_pos _ _ hb,
              ← remainder_value a b hb, hzero,
              CurrentAdditive.EuclidCount.steps_zero]
          have hg := cycle_gcd_value a b hb
          rw [hzero] at hg
          simp at hg
          refine ⟨t, c, ?_, hr, rfl, ?_⟩
          · rw [hs]
            have hcyc : t ≤ cycleTimeBound a b := by
              unfold cycleTimeBound
              omega
            omega
          · simpa [c, cfg, bank, BitMachineBinaryDivision.bank] using hg.symm
        · have hn : (remainder a b).any id = true := by
            cases h : (remainder a b).any id <;> simp_all
          obtain ⟨t₁, ht₁, hfirst⟩ := cycle_nonzero a b hn
          have hnextlen := normalizedRemainder_length_le_divisor a b hb
          have hnextval := normalizedRemainder_value a b
          have hsmall : EncodedCommunication.bitsValue
              (normalizedRemainder a b) < bval := by
            rw [hnextval, remainder_value a b hb, ← hval]
            exact Nat.mod_lt _ hb
          have hnextpos : 0 < EncodedCommunication.bitsValue
              (normalizedRemainder a b) := by
            rw [hnextval]
            have hiff := any_iff_value_ne_zero (remainder a b)
            rw [hn] at hiff
            by_contra hzero
            have heq : EncodedCommunication.bitsValue (remainder a b) = 0 := by omega
            simp [heq] at hiff
          obtain ⟨t₂, c, ht₂, hsecond, hc, hcg⟩ := ih
            (EncodedCommunication.bitsValue (normalizedRemainder a b)) hsmall
            b.reverse (normalizedRemainder a b) rfl
            (by simpa using hlb) (hnextlen.trans hlb) hnextpos
          have hrev := PrimeSamplerBinaryDigit.msbValue_reverse b
          have hg := cycle_gcd_value a b hb
          rw [hrev, hnextval] at hcg
          have hsteps : CurrentAdditive.EuclidCount.steps
              (BitMachineBinaryDivision.msbValue a)
              (EncodedCommunication.bitsValue b) =
              1 + CurrentAdditive.EuclidCount.steps
                (EncodedCommunication.bitsValue b)
                (EncodedCommunication.bitsValue (normalizedRemainder a b)) := by
            rw [CurrentAdditive.EuclidCount.steps_pos _ _ hb,
              ← remainder_value a b hb, ← hnextval]
          refine ⟨t₁ + t₂, c, ?_, (run_add hfirst t₂).trans hsecond, hc,
            hcg.trans hg.symm⟩
          calc
            t₁ + t₂ ≤ roundClock N +
                CurrentAdditive.EuclidCount.steps
                  (EncodedCommunication.bitsValue b)
                  (EncodedCommunication.bitsValue (normalizedRemainder a b)) *
                    roundClock N := Nat.add_le_add (ht₁.trans hclock) (by simpa [hrev] using ht₂)
            _ = (1 + CurrentAdditive.EuclidCount.steps
                  (EncodedCommunication.bitsValue b)
                  (EncodedCommunication.bitsValue (normalizedRemainder a b))) *
                    roundClock N := by ring
            _ = CurrentAdditive.EuclidCount.steps
                  (BitMachineBinaryDivision.msbValue a)
                  (EncodedCommunication.bitsValue b) * roundClock N := by rw [hsteps]
  exact main (EncodedCommunication.bitsValue divisor) input divisor rfl hi hd hpos

theorem euclid_polynomial_clock (input divisor : List Bool)
    (hpos : 0 < EncodedCommunication.bitsValue divisor) :
    ∃ (t : Nat) (c : Config),
      t ≤ (2 * (input.length + divisor.length) + 1) *
        roundClock (input.length + divisor.length) ∧
      run t (cfg (some (.divide .outer)) initial input divisor [] [] [] [] []) = c ∧
      c.l = none ∧
      EncodedCommunication.bitsValue (c.stk 1) =
        Nat.gcd (BitMachineBinaryDivision.msbValue input)
          (EncodedCommunication.bitsValue divisor) := by
  let N := input.length + divisor.length
  obtain ⟨t, c, ht, hr, hc, hv⟩ := euclid_bounded input divisor N
    (by omega) (by omega) hpos
  refine ⟨t, c, ?_, hr, hc, hv⟩
  have hs := CurrentAdditive.EuclidCount.steps_bound
    (BitMachineBinaryDivision.msbValue input)
    (EncodedCommunication.bitsValue divisor)
  have hsize : Nat.size (EncodedCommunication.bitsValue divisor) ≤ divisor.length :=
    Nat.size_le.mpr (BitMachineBinarySubtract.bitsValue_lt_pow divisor)
  have hnonneg : 0 ≤ roundClock N := Nat.zero_le _
  nlinarith [Nat.mul_le_mul_right (roundClock N) hs]

def startClock (N : Nat) : Nat :=
  2 * N + 2 + (2 * N + 1) * roundClock N

/-- A finite input with a zero divisor halts after the guard.  A positive
divisor follows the polynomial Euclidean run; the guard restores it exactly. -/
theorem raw_total (input divisor : List Bool) :
    ∃ (t : Nat) (c : Config),
      t ≤ startClock (input.length + divisor.length) ∧
      run t (cfg (some .checkDivisor) initial input divisor [] [] [] [] []) = c ∧
      c.l = none ∧
      (0 < EncodedCommunication.bitsValue divisor →
        EncodedCommunication.bitsValue (c.stk 1) =
          Nat.gcd (BitMachineBinaryDivision.msbValue input)
            (EncodedCommunication.bitsValue divisor)) := by
  let N := input.length + divisor.length
  have hcheck := check_divisor input divisor
  by_cases hp : 0 < EncodedCommunication.bitsValue divisor
  · have hany : divisor.any id = true := by
      rw [any_iff_value_ne_zero]
      simp [Nat.ne_of_gt hp]
    rw [hany] at hcheck
    obtain ⟨t, c, ht, hr, hc, hv⟩ := euclid_polynomial_clock input divisor hp
    refine ⟨2 * divisor.length + 2 + t, c, ?_,
      (run_add hcheck t).trans hr, hc, ?_⟩
    · unfold startClock
      omega
    · intro _; exact hv
  · have hzero : EncodedCommunication.bitsValue divisor = 0 := by omega
    have hany : divisor.any id = false := by
      rw [any_iff_value_ne_zero]
      simp [hzero]
    rw [hany] at hcheck
    let c : Config := cfg none initial input divisor [] [] [] [] []
    refine ⟨2 * divisor.length + 2, c, ?_, hcheck, rfl, ?_⟩
    · unfold startClock
      omega
    · intro h; omega

end CurrentAdditive.BinaryGCDBound
