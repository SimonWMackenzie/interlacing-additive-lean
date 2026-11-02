import CurrentAdditive.CanonicalEncodedLengthAll
import CurrentAdditive.SmallBiasClonedOutputPullback

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open CurrentAdditive.SmallBias
open Paper2.YaoLookup Paper2.YaoSourceCodec
open EthInapproximability.CurrentPaper.EncodedCommunication

/-- The least power-of-two edge-address space is at most twice the
number of edges plus one, including the empty source. -/
theorem exact_address_capacity_linear (e : ℕ) :
    2 ^ exactAddressBits e ≤ 2 * (e + 1) := by
  by_cases he : e ≤ 1
  · interval_cases e <;> simp [exactAddressBits]
  · have he2 : 1 < e := by omega
    have hmax : max 1 e = e := max_eq_right (by omega)
    have hk : 0 < Nat.clog 2 e := Nat.clog_pos (by decide) he2
    have hprev : 2 ^ (Nat.clog 2 e).pred < e :=
      Nat.pow_pred_clog_lt_self (by decide) he2
    have hpow : 2 ^ Nat.clog 2 e =
        2 * 2 ^ (Nat.clog 2 e).pred := by
      cases h : Nat.clog 2 e with
      | zero => omega
      | succ k => simp [pow_succ, Nat.mul_comm]
    unfold exactAddressBits
    rw [hmax, hpow]
    omega

def cloneOutputCoefficient (t : ℕ) : ℕ :=
  5 * tableConstant t * 2 ^ tableExponent t

/-- Every accepted clone code, even with zero vertices, has output length
polynomial in its own literal input length for fixed `t`. -/
theorem canonical_clone_output_length (g : ℕ)
    (source : YaoSource (v27GapParameter g)) :
    let t := v27GapParameter g
    let N := (encode source).length + 1
    (encodeInstance (canonicalOfClone g source)).length ≤
      cloneOutputCoefficient t * N ^ (tableExponent t + 1) +
        8 * N + 8 * t + 7 := by
  dsimp only
  let t := v27GapParameter g
  let b := exactAddressBits source.2.1
  let N := (encode source).length + 1
  let H := 2 ^ b
  let E := tableExponent t
  let C := tableConstant t
  have ht : 4 ≤ t := v27GapParameter_ge_four g
  have hbase := encoded_instance_length_polynomial_all b t ht
    ((CurrentAdditive.FiniteFieldConstructor.TrialSearch.firstPassing
      (publicFieldDegree b t)).getD 0)
    (exactAddress_capacity source.2.1) source.2.2
  have hsize := encode_length source
  have hv : source.1 + 1 ≤ N := by
    dsimp [N]
    omega
  have he : source.2.1 + 1 ≤ N := by
    dsimp [N]
    omega
  have hH : H ≤ 2 * N := by
    exact (exact_address_capacity_linear source.2.1).trans
      (Nat.mul_le_mul_left 2 he)
  have hbH : b ≤ H := by
    dsimp [H, b]
    exact Nat.le_of_lt Nat.lt_two_pow_self
  have hbN : b ≤ 2 * N := hbH.trans hH
  have hpow : H ^ E ≤ (2 * N) ^ E := Nat.pow_le_pow_left hH E
  have hmain : 5 * C * (source.1 + 1) * H ^ E ≤
      cloneOutputCoefficient t * N ^ (E + 1) := by
    calc
      5 * C * (source.1 + 1) * H ^ E ≤
          5 * C * N * (2 * N) ^ E := by gcongr
      _ = cloneOutputCoefficient t * N ^ (E + 1) := by
        dsimp [cloneOutputCoefficient, C, E]
        rw [mul_pow, pow_succ]
        ring
  change (encodeInstance (canonicalOfClone g source)).length ≤
    cloneOutputCoefficient t * N ^ (E + 1) + 8 * N + 8 * t + 7
  have hrewrite : canonicalOfClone g source =
      instanceOfTable b t (publicFieldDegree b t)
        ((CurrentAdditive.FiniteFieldConstructor.TrialSearch.firstPassing
          (publicFieldDegree b t)).getD 0)
        (exactAddress_capacity source.2.1) source.2.2 := rfl
  rw [hrewrite]
  calc
    _ ≤ 5 * C * (source.1 + 1) * H ^ E +
          2 * (2 * b + 4 * t + 2) + 3 := by
      simpa only [C, E, H] using hbase
    _ ≤ cloneOutputCoefficient t * N ^ (E + 1) +
          8 * N + 8 * t + 7 := by omega

/-- On arbitrary input bits, rejected codes emit `[]`; accepted codes
obey the same fixed-parameter polynomial output bound. -/
theorem renderClone_length (g : ℕ) (bits : List Bool) :
    let t := v27GapParameter g
    let N := bits.length + 1
    (renderClone g bits).length ≤
      cloneOutputCoefficient t * N ^ (tableExponent t + 1) +
        8 * N + 8 * t + 7 := by
  dsimp only
  unfold renderClone
  cases hdecode : decodeAll (v27GapParameter g) bits with
  | none => simp
  | some source =>
      have hcode := (decodeAll_eq_some_iff bits source).mp hdecode
      subst bits
      simpa only [hdecode] using canonical_clone_output_length g source

#print axioms exact_address_capacity_linear
#print axioms canonical_clone_output_length
#print axioms renderClone_length

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
