import EthInapproximability.CurrentPaper.MatrixWeightedRawRead
import EthInapproximability.CurrentPaper.MatrixIndexSplit

/-!
# First physical weighted-column split and exact ordinal semantics

The uniform-copy digit is last in the actual protected column order.
This owner identifies the quotient/remainder output of the fixed split
machine with the two components of `MatrixWeightedArithmetic.decodeColumn`.
-/

namespace EthInapproximability.CurrentPaper.MatrixWeightedColumnOuterDecode

open MatrixWeightedArithmetic MatrixIndexQuotient

theorem pair_coordinates (m n : ℕ) (i : Fin (m * n)) :
    i.val / n = (finProdFinEquiv.symm i).1.val ∧
      i.val % n = (finProdFinEquiv.symm i).2.val := by
  let p := finProdFinEquiv.symm i
  have hval : i.val = p.1.val * n + p.2.val := by
    have hpair : finProdFinEquiv p = i := Equiv.apply_symm_apply _ _
    have hv := congrArg Fin.val hpair
    simpa only [finProdFinEquiv_apply_val, Nat.mul_comm, Nat.add_comm] using hv.symm
  constructor
  · rw [hval, Nat.mul_comm p.1.val n,
      Nat.mul_add_div (Nat.zero_lt_of_lt p.2.isLt),
      Nat.div_eq_of_lt p.2.isLt]
    rfl
  · rw [hval, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt p.2.isLt]

def supportOrdinal (M D S : ℕ)
    (i : Fin ((M * (182 * D) + D * (2 * M)) * S)) : ℕ :=
  (finProdFinEquiv.symm i).1.val

theorem outer_coordinates (M D S : ℕ)
    (i : Fin ((M * (182 * D) + D * (2 * M)) * S)) :
    i.val / S = supportOrdinal M D S i ∧
      i.val % S = (decodeColumn M D S i).2.val := by
  exact pair_coordinates _ S i

theorem outer_split_run (M D S : ℕ)
    (i : Fin ((M * (182 * D) + D * (2 * M)) * S)) :
    ∃ t ≤ 10 * i.val + 3 * S + 6,
      run t (cfg (some start) initial
        (List.replicate i.val true) (List.replicate S true)
        [] [] [] [] [] []) =
      cfg (some clear) initial
        (List.replicate i.val true) (List.replicate S true)
        [] [] []
        (List.replicate (decodeColumn M D S i).2.val true)
        (List.replicate (supportOrdinal M D S i) true) [] := by
  have hc := outer_coordinates M D S i
  simpa only [hc.1, hc.2] using MatrixIndexSplit.split_run i.val S

/-- The cut's left branch is exactly the full-support branch of the
arithmetically decoded protected label. -/
theorem full_branch (M D S : ℕ)
    (i : Fin ((M * (182 * D) + D * (2 * M)) * S))
    (h : supportOrdinal M D S i < M * (182 * D)) :
    (decodeColumn M D S i).1 =
      .inl (finProdFinEquiv.symm
        (⟨supportOrdinal M D S i, h⟩ : Fin (M * (182 * D)))) := by
  let p := finProdFinEquiv.symm i
  let x : Fin (M * (182 * D)) := ⟨p.1.val, h⟩
  have hp : p.1 = Fin.castAdd (D * (2 * M)) x := Fin.ext rfl
  change (match finSumFinEquiv.symm p.1 with
    | Sum.inl q => Sum.inl (finProdFinEquiv.symm q)
    | Sum.inr q => Sum.inr (finProdFinEquiv.symm q)) = _
  rw [hp, finSumFinEquiv_symm_apply_castAdd]
  rfl

/-- The other cut branch is exactly the diagonal-support branch, with the
threshold subtracted from the support ordinal. -/
theorem diagonal_branch (M D S : ℕ)
    (i : Fin ((M * (182 * D) + D * (2 * M)) * S))
    (h : M * (182 * D) ≤ supportOrdinal M D S i) :
    (decodeColumn M D S i).1 =
      .inr (finProdFinEquiv.symm
        (⟨supportOrdinal M D S i - M * (182 * D), by
          have hi := (finProdFinEquiv.symm i).1.isLt
          have hh : M * (182 * D) ≤ (finProdFinEquiv.symm i).1.val := by
            simpa only [supportOrdinal] using h
          simp only [supportOrdinal]
          omega⟩ : Fin (D * (2 * M)))) := by
  let p := finProdFinEquiv.symm i
  let y : Fin (D * (2 * M)) :=
    ⟨p.1.val - M * (182 * D), by
      have hi := p.1.isLt
      have hh : M * (182 * D) ≤ p.1.val := by
        simpa only [supportOrdinal, p] using h
      omega⟩
  have hp : p.1 = Fin.natAdd (M * (182 * D)) y := by
    apply Fin.ext
    have hh : M * (182 * D) ≤ p.1.val := by
      simpa only [supportOrdinal, p] using h
    dsimp [y]
    omega
  change (match finSumFinEquiv.symm p.1 with
    | Sum.inl q => Sum.inl (finProdFinEquiv.symm q)
    | Sum.inr q => Sum.inr (finProdFinEquiv.symm q)) = _
  calc
    (match finSumFinEquiv.symm p.1 with
      | Sum.inl q => Sum.inl (finProdFinEquiv.symm q)
      | Sum.inr q => Sum.inr (finProdFinEquiv.symm q)) =
        Sum.inr (finProdFinEquiv.symm y) := by
          rw [hp, finSumFinEquiv_symm_apply_natAdd]
    _ = _ := rfl

/-- The fixed unary cut decides the exact 182-weight boundary and retains
the threshold for the next group-specific quotient. -/
theorem group_cut_run (M D S : ℕ)
    (i : Fin ((M * (182 * D) + D * (2 * M)) * S)) :
    ∃ t ≤ 3 * min (supportOrdinal M D S i) (M * (182 * D)) + 4,
      MatrixUnaryCut.run t
        (MatrixUnaryCut.cfg (some .scan) (false,true)
          (List.replicate (supportOrdinal M D S i) true)
          (List.replicate (M * (182 * D)) true) [] []) =
      MatrixUnaryCut.cfg none
        (decide (M * (182 * D) ≤ supportOrdinal M D S i), false)
        (List.replicate
          (if supportOrdinal M D S i < M * (182 * D) then
            supportOrdinal M D S i
          else supportOrdinal M D S i - M * (182 * D)) true)
        (List.replicate (M * (182 * D)) true) [] [] :=
  MatrixUnaryCut.cut_run _ _

/-- After the uniform and group cut, a second fixed quotient machine
produces the full-support label and its literal `182*D` copy digit. -/
theorem full_split_run (M D S : ℕ)
    (i : Fin ((M * (182 * D) + D * (2 * M)) * S))
    (h : supportOrdinal M D S i < M * (182 * D)) :
    let p := finProdFinEquiv.symm
      (⟨supportOrdinal M D S i, h⟩ : Fin (M * (182 * D)))
    ∃ t ≤ 10 * supportOrdinal M D S i + 3 * (182 * D) + 6,
      run t (cfg (some start) initial
        (List.replicate (supportOrdinal M D S i) true)
        (List.replicate (182 * D) true) [] [] [] [] [] []) =
      cfg (some clear) initial
        (List.replicate (supportOrdinal M D S i) true)
        (List.replicate (182 * D) true) [] [] []
        (List.replicate p.2.val true)
        (List.replicate p.1.val true) [] := by
  have hc := pair_coordinates M (182 * D)
    (⟨supportOrdinal M D S i, h⟩ : Fin (M * (182 * D)))
  simpa only [hc.1, hc.2] using
    MatrixIndexSplit.split_run (supportOrdinal M D S i) (182 * D)

/-- The diagonal-support branch uses exactly the `2*M` copy divisor. -/
theorem diagonal_split_run (M D S : ℕ)
    (i : Fin ((M * (182 * D) + D * (2 * M)) * S))
    (h : M * (182 * D) ≤ supportOrdinal M D S i) :
    let residual := supportOrdinal M D S i - M * (182 * D)
    let p := finProdFinEquiv.symm
      (⟨residual, by
        have hi := (finProdFinEquiv.symm i).1.isLt
        have hh : M * (182 * D) ≤ (finProdFinEquiv.symm i).1.val := by
          simpa only [supportOrdinal] using h
        simp only [residual, supportOrdinal]
        omega⟩ : Fin (D * (2 * M)))
    ∃ t ≤ 10 * residual + 3 * (2 * M) + 6,
      run t (cfg (some start) initial
        (List.replicate residual true)
        (List.replicate (2 * M) true) [] [] [] [] [] []) =
      cfg (some clear) initial
        (List.replicate residual true)
        (List.replicate (2 * M) true) [] [] []
        (List.replicate p.2.val true)
        (List.replicate p.1.val true) [] := by
  have hi := (finProdFinEquiv.symm i).1.isLt
  have hh : M * (182 * D) ≤ (finProdFinEquiv.symm i).1.val := by
    simpa only [supportOrdinal] using h
  have hres : supportOrdinal M D S i - M * (182 * D) < D * (2 * M) := by
    simp only [supportOrdinal]
    omega
  have hc := pair_coordinates D (2 * M)
    (⟨supportOrdinal M D S i - M * (182 * D), hres⟩ : Fin (D * (2 * M)))
  simpa only [hc.1, hc.2] using
    MatrixIndexSplit.split_run
      (supportOrdinal M D S i - M * (182 * D)) (2 * M)

end EthInapproximability.CurrentPaper.MatrixWeightedColumnOuterDecode
