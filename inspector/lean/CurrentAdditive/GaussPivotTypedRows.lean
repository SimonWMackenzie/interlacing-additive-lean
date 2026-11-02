import CurrentAdditive.GaussPivotTypedScan
import CurrentAdditive.GaussTypedGetterBridge
import CurrentAdditive.GaussRawZeroCheck

set_option maxHeartbeats 1000000

namespace CurrentAdditive.GaussPivotTypedRows

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussTypedGetterBridge
open CurrentAdditive.CodeDCodec
open CurrentAdditive.GaussPhysical

def piece (column : Nat) (word : List Bool) : Bool :=
  (CurrentAdditive.GaussRawZeroCheck.numeratorWord
    (((SourceListEncoding.decode word).getD [])[column]?.getD [])).any id

theorem numerator_nonzero (q : ℚ) :
    (CurrentAdditive.GaussRawZeroCheck.numeratorWord
      (encodeRawRat (rawOfRat q))).any id = decide (q ≠ 0) := by
  have hz := CurrentAdditive.GaussRawZeroCheck.zero_flag_iff_value
    (rawOfRat q) (rawOfRat_valid q)
  simp only [CurrentAdditive.GaussRawZeroCheck.result,
    rawOfRat_value, List.cons.injEq] at hz
  cases hb : (CurrentAdditive.GaussRawZeroCheck.numeratorWord
      (encodeRawRat (rawOfRat q))).any id <;>
    simp [hb] at hz ⊢ <;> assumption

theorem piece_typed {m k : Nat} (B : Fin m → Fin k → ℚ)
    (i : Fin m) (j : Fin k) :
    piece j.val (SourceListEncoding.encode (cellWords B i)) =
      decide (B i j ≠ 0) := by
  have hc : ((cellWords B i)[j.val]?).getD [] =
      encodeRawRat (rawOfRat (B i j)) := by
    simp [cellWords]
  simp only [piece, SourceListEncoding.decode_encode, Option.getD_some]
  rw [hc]
  exact numerator_nonzero (B i j)

theorem row_split {m k : Nat} (B : Fin m → Fin k → ℚ)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool))
    (h : pre ++ word :: suffix = rowWords B) :
    ∃ i : Fin m, i.val = pre.length ∧
      word = SourceListEncoding.encode (cellWords B i) := by
  have hlt : pre.length < m := by
    have hh := congrArg List.length h
    simp [rowWords] at hh
    omega
  let i : Fin m := ⟨pre.length, hlt⟩
  refine ⟨i, rfl, ?_⟩
  have hw := congrArg (fun xs : List (List Bool) => xs[pre.length]?) h
  simp only [List.getElem?_append] at hw
  have hc : (rowWords B)[pre.length]? =
      some (SourceListEncoding.encode (cellWords B i)) := by
    have hi : pre.length < (rowWords B).length := by
      simpa [rowWords] using hlt
    rw [List.getElem?_eq_getElem hi]
    exact congrArg some (rowWords_get B i)
  rw [hc] at hw
  simpa using Option.some.inj (by simpa using hw)

theorem row_cell_split {m k : Nat} (B : Fin m → Fin k → ℚ)
    (j : Fin k) (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool))
    (h : pre ++ word :: suffix = rowWords B) :
    ∃ i : Fin m, ∃ cellPre cellSuffix : List (List Bool),
      i.val = pre.length ∧ cellPre.length = j.val ∧
      word = SourceListEncoding.encode
        (cellPre ++ encodeRawRat (rawOfRat (B i j)) :: cellSuffix) := by
  obtain ⟨i, hi, hw⟩ := row_split B pre word suffix h
  let cells := cellWords B i
  have hj : j.val < cells.length := by simp [cells, cellWords]
  let cellPre := cells.take j.val
  let cellSuffix := cells.drop (j.val+1)
  refine ⟨i, cellPre, cellSuffix, hi, ?_, ?_⟩
  · simp [cellPre, cells, cellWords]
  · have hc := split_at cells j.val hj
    have hword : cells[j.val]'hj = encodeRawRat (rawOfRat (B i j)) := by
      simpa [cells] using cellWords_get B i j
    rw [hword] at hc
    simpa only [cellPre, cellSuffix] using hw.trans (congrArg _ hc)

end CurrentAdditive.GaussPivotTypedRows
