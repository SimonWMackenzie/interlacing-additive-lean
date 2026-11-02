import EthInapproximability.CurrentPaper.MatrixStage4ColumnMachine

/-!
# Physical variable-length tuple coordinate extraction

This is a deliberately redundant specialization of the fixed four-division
column controller. It resolves any `Fin n → Fin m` tuple digit without
placing the tuple length or selected coordinate in finite control. The
required unary powers are supplied and their construction is still owed.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4TupleMachine

open MatrixMaterialization MatrixLabelArithmetic MatrixStage4ColumnMachine

theorem tuple_coordinate_run {m n : ℕ} (code : Fin (m ^ n)) (j : Fin n) :
    let stride := m^(n-1-j.val)
    let digit := ((tupleCode m n).symm code j).val
    ∃ t ≤ MatrixUnaryDivision.totalTime code.val (m^n)+
      MatrixUnaryDivision.totalTime code.val stride+
      MatrixUnaryDivision.totalTime (code.val/stride) m+
      MatrixUnaryDivision.totalTime digit 1+1,
      (run t (cfg (some outerStart) initial
        (List.replicate code.val true) (List.replicate (m^n) true)
        (List.replicate stride true) (List.replicate m true)
        [true] [] [] [] [] [] [] [] [])).stk 15 =
          List.replicate digit true := by
  dsimp
  let stride := m^(n-1-j.val)
  let digit := ((tupleCode m n).symm code j).val
  have hmod : code.val % m^n = code.val := Nat.mod_eq_of_lt code.isLt
  have hdigit : code.val/stride % m = digit := by
    exact (tuple_digit code j).symm
  obtain ⟨t,ht,hr⟩ := column_run code.val (m^n) stride m 1
  refine ⟨t, ?_, ?_⟩
  · simpa only [hmod, hdigit] using ht
  · have h := congrArg (fun c : Config => c.stk 15) hr
    simpa only [cfg, Nat.div_one, hmod, hdigit,
      List.replicate_one, Matrix.cons_val_fin_one] using h

end EthInapproximability.CurrentPaper.MatrixStage4TupleMachine
