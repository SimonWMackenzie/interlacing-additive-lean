import EthInapproximability.CurrentPaper.MatrixStage4Digits
import EthInapproximability.CurrentPaper.MatrixIndexSplit

/-!
# Actual first splits of variable-bin Stage--4 labels

These theorems connect the fixed unary Boolean-stack quotient/remainder
program to the *typed* `Construction.rawMatrix` row and column codes.
Template row labels split into a bin and family index.  Every raw column
label splits into the tail-word code and the entire `s`-bin tuple code.
Subsequent per-bin selection, family payload access, graph active rank and
source-table read remain separate physical stages.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4Decode

open Construction MatrixStage4Codes MatrixStage4Digits
open MatrixMaterialization
open MatrixIndexQuotient

theorem template_row_split {s L nv nb rx : ℕ} (order : ItemOrder nv nb)
    (p : Fin s) (ℓ : Fin L) :
    ∃ t ≤ 10*(rowCode s L nv nb rx order (.inl (p,ℓ))).val+3*L+6,
      run t (cfg (some start) initial
        (List.replicate (rowCode s L nv nb rx order (.inl (p,ℓ))).val true)
        (List.replicate L true) [] [] [] [] [] []) =
      cfg (some clear) initial
        (List.replicate (rowCode s L nv nb rx order (.inl (p,ℓ))).val true)
        (List.replicate L true) [] [] []
        (List.replicate ℓ.val true) (List.replicate p.val true) [] := by
  have hdiv : (rowCode s L nv nb rx order (.inl (p,ℓ))).val / L = p.val := by
    rw [template_row_value]
    have hL : 0 < L := lt_of_le_of_lt (Nat.zero_le ℓ.val) ℓ.isLt
    rw [Nat.add_mul_div_left _ _ hL]
    simp [Nat.div_eq_of_lt ℓ.isLt]
  have hmod : (rowCode s L nv nb rx order (.inl (p,ℓ))).val % L = ℓ.val := by
    rw [template_row_value]
    simp [Nat.mod_eq_of_lt ℓ.isLt]
  simpa only [hdiv,hmod] using
    MatrixIndexSplit.split_run (rowCode s L nv nb rx order (.inl (p,ℓ))).val L

theorem raw_column_outer_split {a s q cy : ℕ}
    (code : Fin (cols a s q cy)) :
    ∃ t ≤ 10*code.val+3*(binBase a s q cy)^s+6,
      run t (cfg (some start) initial
        (List.replicate code.val true)
        (List.replicate ((binBase a s q cy)^s) true) [] [] [] [] [] []) =
      cfg (some clear) initial
        (List.replicate code.val true)
        (List.replicate ((binBase a s q cy)^s) true) [] [] []
        (List.replicate (code.val % (binBase a s q cy)^s) true)
        (List.replicate
          ((tupleCode cy (s+1)) ((rawColumnCode a s q cy).symm code).1).val true)
        [] := by
  have htail := column_tail_code code
  simpa only [htail] using
    MatrixIndexSplit.split_run code.val ((binBase a s q cy)^s)

/-- The second physical quotient exposes the selected base-`q*wordBase` digit.
The power divisor is an explicit unary input; constructing it is charged
separately and is not folded into this statement. -/
theorem raw_column_bin_stride_split {a s q cy : ℕ}
    (code : Fin (cols a s q cy)) (p : Fin s) :
    ∃ t ≤ 10*(code.val % (binBase a s q cy)^s) +
        3*(binBase a s q cy)^(s-1-p.val)+6,
      run t (cfg (some start) initial
        (List.replicate (code.val % (binBase a s q cy)^s) true)
        (List.replicate ((binBase a s q cy)^(s-1-p.val)) true)
        [] [] [] [] [] []) =
      cfg (some clear) initial
        (List.replicate (code.val % (binBase a s q cy)^s) true)
        (List.replicate ((binBase a s q cy)^(s-1-p.val)) true)
        [] [] []
        (List.replicate
          ((code.val % (binBase a s q cy)^s) %
            (binBase a s q cy)^(s-1-p.val)) true)
        (List.replicate
          ((code.val % (binBase a s q cy)^s) /
            (binBase a s q cy)^(s-1-p.val)) true) [] :=
  MatrixIndexSplit.split_run _ _

/-- The third physical quotient/remainder recovers precisely the typed
second-row code selected by bin `p`. -/
theorem raw_column_bin_digit_split {a s q cy : ℕ}
    (code : Fin (cols a s q cy)) (p : Fin s) :
    let n := (code.val % (binBase a s q cy)^s) /
      (binBase a s q cy)^(s-1-p.val)
    ∃ t ≤ 10*n+3*(binBase a s q cy)+6,
      run t (cfg (some start) initial
        (List.replicate n true)
        (List.replicate (binBase a s q cy) true) [] [] [] [] [] []) =
      cfg (some clear) initial
        (List.replicate n true)
        (List.replicate (binBase a s q cy) true) [] [] []
        (List.replicate
          (secondRowCode a s q cy
            (((rawColumnCode a s q cy).symm code).2 p)).val true)
        (List.replicate (n/(binBase a s q cy)) true) [] := by
  dsimp
  have h := column_bin_code code p
  unfold binDigit at h
  simpa only [← h] using
    MatrixIndexSplit.split_run
      ((code.val % (binBase a s q cy)^s) /
        (binBase a s q cy)^(s-1-p.val)) (binBase a s q cy)

/-- The fourth quotient resolves the selected bin into its `q`-selector and
first-matrix word, again with the unary word-base supplied explicitly. -/
theorem raw_column_family_split {a s q cy : ℕ}
    (code : Fin (cols a s q cy)) (p : Fin s) :
    let r := ((rawColumnCode a s q cy).symm code).2 p
    let digit := (secondRowCode a s q cy r).val
    ∃ t ≤ 10*digit+3*(wordBase a s cy)+6,
      run t (cfg (some start) initial
        (List.replicate digit true)
        (List.replicate (wordBase a s cy) true) [] [] [] [] [] []) =
      cfg (some clear) initial
        (List.replicate digit true)
        (List.replicate (wordBase a s cy) true) [] [] []
        (List.replicate (firstWordCode a s cy r.2).val true)
        (List.replicate r.1.val true) [] := by
  dsimp
  have hword := second_row_word
    (((rawColumnCode a s q cy).symm code).2 p)
  have halpha := second_row_alpha
    (((rawColumnCode a s q cy).symm code).2 p)
  simpa only [← hword, ← halpha] using
    MatrixIndexSplit.split_run
      (secondRowCode a s q cy (((rawColumnCode a s q cy).symm code).2 p)).val
      (wordBase a s cy)

end EthInapproximability.CurrentPaper.MatrixStage4Decode
