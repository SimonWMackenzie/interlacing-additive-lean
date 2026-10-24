import CurrentAdditive.IndexedLawBytesPrimitives
import CurrentAdditive.RatioListClockBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
namespace CurrentAdditive.IndexedLawBytes
open EthInapproximability.CurrentPaper BitMachineBankCodec

def inputSize (xs : List (List Bool)) := (SourceListEncoding.encode xs).length

def stateCap (N : Nat) := 100*(N+1)^2

theorem count_le (xs : List (List Bool)) : xs.length  ≤  inputSize xs := GaussRowCount.rows_le_input xs

theorem indexedWord_length_le (xs : List (List Bool)) (i : Nat) (word : List Bool)
    (hi : i ≤ xs.length) (hw : word∈xs) :
    (indexedWord i word).length ≤ 4*inputSize xs+2 := by
  have hn := count_le xs
  have hb := UnaryBinaryEncoding.bits_length_le i
  have hword := RatioListClockBounds.word_le_packet xs word hw
  have hweight := BankFieldProjection.result_length (1 : Fin 2) word
  change (weightWord word).length ≤ word.length at hweight
  have he : (indexedWord i word).length=2*i.bits.length+2*(weightWord word).length+2 := by
    simp [indexedWord,encode_length,Fin.sum_univ_two]
    omega
  rw [he]
  dsimp only [inputSize] at *
  omega

theorem framedWord_length_le (xs : List (List Bool)) (i : Nat) (hi : i<xs.length) :
    (SourceListMachineWriter.result true (indexedWord i (xs[i]?.getD []))).length  ≤ 12*inputSize xs+7 := by
  have h := indexedWord_length_le xs i xs[i] (Nat.le_of_lt hi) (List.getElem_mem hi)
  have hf := SourceListMachineWriter.result_length true (indexedWord i (xs[i]?.getD []))
  simp only [List.getElem?_eq_getElem hi,Option.getD_some] at hf ⊢
  omega

theorem fieldsAt_length_le (xs : List (List Bool)) (i : Nat) (hi : i ≤ xs.length) :
    (fieldsAt xs i).length  ≤ i*(12*inputSize xs+7) := by
  induction i with
  | zero => simp [fieldsAt]
  | succ i ih =>
    have hb : i<xs.length := by omega
    have hp := ih (by omega)
    have hw := framedWord_length_le xs i hb
    rw [fieldsAt_succ,List.length_append]
    nlinarith

theorem state_length_le (xs : List (List Bool)) (i : Nat) (hi : i ≤ xs.length) :
    (state xs i).length  ≤ stateCap (inputSize xs) := by
  have hn := count_le xs
  have hf := fieldsAt_length_le xs i hi
  have hm := Nat.mul_le_mul_right (12*inputSize xs+7) (hi.trans hn)
  have he : (state xs i).length=2*(inputSize xs+i+(fieldsAt xs i).length)+3 := by
    simp [state,inputSize,encode_length,Fin.sum_univ_succ,Nat.add_assoc]
  rw [he]
  unfold stateCap
  nlinarith

#print axioms state_length_le
end CurrentAdditive.IndexedLawBytes
