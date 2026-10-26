import CurrentAdditive.V39SourceRenderer
import CurrentAdditive.V39SourceAddressResource
import CurrentAdditive.V38PublicClock
import EthInapproximability.CurrentPaper.UnaryBinaryEncoding

/-! Explicit output-length bounds for the actual chosen source instance.
The bound counts its three self-delimiting headers and every row-major table
bit. It is not a proof that a particular printer attains a runtime bound. -/

namespace CurrentAdditive.V39SourceOutputSize

open CurrentAdditive.V38Source CurrentAdditive.V38Encoded
open CurrentAdditive.V39SourceCompiler CurrentAdditive.V39SourceRenderer
open CurrentAdditive.V39SourceAddressResource
open CurrentAdditive.SmallBias CurrentAdditive.V38Clock
open Paper2.YaoSourceCodec
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication

set_option maxHeartbeats 1000000

def rowCoefficient (t : ℕ) : ℕ := 2 ^ (2 ^ (t - 1))
def columnCoefficient (t : ℕ) : ℕ :=
  2 ^ (t - 1) * (2 ^ (14 * t)) ^ 2 * 2 ^ 11
def outputDegree (t : ℕ) : ℕ := 2 ^ (t - 1) + 12
def outputCoefficient (t : ℕ) : ℕ :=
  2 * (rowCoefficient t + columnCoefficient t + (4 * t + 6)) + 3 +
    rowCoefficient t * columnCoefficient t

theorem source_headers_le {t : ℕ} (src : YaoSource t) :
    src.1 + src.2.1 + 2 ≤ (encode src).length := by
  rw [encode_length]
  omega

theorem source_capacity_le {t : ℕ} (src : YaoSource t) :
    2 ^ edgeBits src.2.1 ≤ 2 * ((encode src).length + 1) := by
  have h := capacity_le_twice_succ src.2.1
  have hh := source_headers_le src
  omega

theorem instance_rows_bound {t : ℕ} (src : YaoSource t) :
    (sourceInstance src).rows ≤
      rowCoefficient t * ((encode src).length + 1) ^ (2 ^ (t - 1) + 1) := by
  rw [(sourceInstance_dimensions src).1]
  have hv : src.1 ≤ (encode src).length + 1 := by
    have hh := source_headers_le src
    omega
  have hH := source_capacity_le src
  calc
    _ ≤ ((encode src).length + 1) *
        (2 * ((encode src).length + 1)) ^ (2 ^ (t - 1)) :=
      Nat.mul_le_mul hv (Nat.pow_le_pow_left hH _)
    _ = _ := by simp only [rowCoefficient, mul_pow, pow_succ]; ring

theorem instance_cols_bound {t : ℕ} (src : YaoSource t) :
    (sourceInstance src).cols ≤
      columnCoefficient t * ((encode src).length + 1) ^ 11 := by
  rw [(sourceInstance_dimensions src).2.1, field_order_exact, target_fixed_t]
  have hH := Nat.pow_le_pow_left (source_capacity_le src) 11
  calc
    _ = (2 ^ (t - 1) * (2 ^ (14 * t)) ^ 2) *
        (2 ^ edgeBits src.2.1) ^ 11 := by ring
    _ ≤ (2 ^ (t - 1) * (2 ^ (14 * t)) ^ 2) *
        (2 * ((encode src).length + 1)) ^ 11 :=
      Nat.mul_le_mul_left _ hH
    _ = _ := by simp only [columnCoefficient, mul_pow]; ring

theorem instance_threshold_bound {t : ℕ} (src : YaoSource t) :
    (sourceInstance src).threshold ≤
      (4 * t + 6) * ((encode src).length + 1) := by
  rw [(sourceInstance_dimensions src).2.2]
  have hb : edgeBits src.2.1 ≤ 2 ^ edgeBits src.2.1 :=
    (Nat.lt_two_pow_self).le
  have hH := source_capacity_le src
  have hn : 0 < (encode src).length + 1 := by omega
  have ht := Nat.le_mul_of_pos_right (4 * t + 2) hn
  nlinarith

theorem instance_table_length {t : ℕ} (src : YaoSource t) :
    (sourceInstance src).table.length =
      (sourceInstance src).rows * (sourceInstance src).cols := by
  exact (CurrentAdditive.V38Executable.table
    (edgeBits src.2.1) t (v38FieldDegree (edgeBits src.2.1) t)
    (selectedModulus (edgeBits src.2.1) t)
    (edgeCount_le_capacity src.2.1) src.2.2).length

theorem instance_table_length_bound {t : ℕ} (src : YaoSource t) :
    (sourceInstance src).table.length ≤
      (rowCoefficient t * columnCoefficient t) *
        ((encode src).length + 1) ^ outputDegree t := by
  rw [instance_table_length]
  calc
    _ ≤ (rowCoefficient t * ((encode src).length + 1) ^ (2 ^ (t - 1) + 1)) *
        (columnCoefficient t * ((encode src).length + 1) ^ 11) :=
      Nat.mul_le_mul (instance_rows_bound src) (instance_cols_bound src)
    _ = _ := by
      rw [mul_mul_mul_comm, ← pow_add]
      congr 1

/-- This counts the exact three headers and the actual selected matrix word,
not an auxiliary complete-stream alphabet or another representation. -/
theorem encoded_instance_length_bound {t : ℕ} (src : YaoSource t) :
    (encodeInstance (sourceInstance src)).length ≤
      outputCoefficient t * ((encode src).length + 1) ^ outputDegree t := by
  rw [encodeInstance_length]
  have hr := instance_rows_bound src
  have hc := instance_cols_bound src
  have ht := instance_threshold_bound src
  have hm := instance_table_length_bound src
  have hbase : 1 ≤ (encode src).length + 1 := by omega
  have hrow : ((encode src).length + 1) ^ (2 ^ (t - 1) + 1) ≤
      ((encode src).length + 1) ^ outputDegree t :=
    Nat.pow_le_pow_right hbase (Nat.add_le_add_left (by decide : 1 ≤ 12) _)
  have hcol : ((encode src).length + 1) ^ 11 ≤
      ((encode src).length + 1) ^ outputDegree t :=
    Nat.pow_le_pow_right hbase
      ((by decide : 11 ≤ 12).trans (Nat.le_add_left 12 _))
  have hlin : (encode src).length + 1 ≤
      ((encode src).length + 1) ^ outputDegree t :=
    Nat.le_self_pow (Nat.ne_of_gt (lt_of_lt_of_le
      (by decide : 0 < 12) (Nat.le_add_left 12 _))) _
  have hr' := hr.trans (Nat.mul_le_mul_left _ hrow)
  have hc' := hc.trans (Nat.mul_le_mul_left _ hcol)
  have ht' := ht.trans (Nat.mul_le_mul_left _ hlin)
  have hpos : 1 ≤ ((encode src).length + 1) ^ outputDegree t :=
    Nat.one_le_pow _ _ hbase
  have hbr := UnaryBinaryEncoding.bits_length_le (sourceInstance src).rows
  have hbc := UnaryBinaryEncoding.bits_length_le (sourceInstance src).cols
  have hbt := UnaryBinaryEncoding.bits_length_le (sourceInstance src).threshold
  unfold outputCoefficient
  nlinarith

/-- Composing the explicit byte-size bound with the actual source compiler's
output-length bound gives a polynomial in the original input size. -/
theorem selected_encoded_instance_length_poly {t : ℕ} (G : GLSourceInput t) :
    ∃ c d : ℕ, ∀ input,
      (encodeInstance (sourceInstance (selectedSource G input))).length ≤
        c * (input.length + 1) ^ d := by
  obtain ⟨c, d, hc⟩ := CurrentAdditive.V38Machine.source_encoded_length_poly G
  refine ⟨outputCoefficient t * (c + 1) ^ outputDegree t,
    d * outputDegree t, fun input => ?_⟩
  have hp : 1 ≤ (input.length + 1) ^ d :=
    Nat.one_le_pow _ _ (by omega)
  have hlen : (encode (selectedSource G input)).length + 1 ≤
      (c + 1) * (input.length + 1) ^ d := by
    have h := hc input
    nlinarith
  calc
    _ ≤ outputCoefficient t *
        ((encode (selectedSource G input)).length + 1) ^ outputDegree t :=
      encoded_instance_length_bound _
    _ ≤ outputCoefficient t *
        ((c + 1) * (input.length + 1) ^ d) ^ outputDegree t :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlen _)
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

#print axioms source_headers_le
#print axioms source_capacity_le
#print axioms instance_rows_bound
#print axioms instance_cols_bound
#print axioms instance_threshold_bound
#print axioms instance_table_length
#print axioms instance_table_length_bound
#print axioms encoded_instance_length_bound
#print axioms selected_encoded_instance_length_poly

end CurrentAdditive.V39SourceOutputSize
