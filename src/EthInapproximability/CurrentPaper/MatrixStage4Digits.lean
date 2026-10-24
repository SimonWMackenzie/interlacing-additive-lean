import EthInapproximability.CurrentPaper.MatrixStage4Codes
import EthInapproximability.CurrentPaper.MatrixLabelArithmetic

/-!
# Variable-bin mixed-radix identities for the Stage--4 source table

Frozen v8 `B-effectivity-details.tex`, `thm:paper-materialization` requires
quotient/remainder decoding of every source, group and interlace label.  These
identities pin the exact digits of `MatrixStage4Codes.rawColumnCode`; the
physical quotient/remainder stage is `MatrixIndexSplit.split_run`.  The
identities themselves are mathematical specifications, not runtime claims.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4Digits

open Construction MatrixStage4Codes MatrixMaterialization

def wordBase (a s cy : ℕ) : ℕ := cy^(firstLength a s)
def binBase (a s q cy : ℕ) : ℕ := q*wordBase a s cy
def binDigit (code a s q cy : ℕ) (p : Fin s) : ℕ :=
  code % (binBase a s q cy)^s /
    (binBase a s q cy)^(s-1-p.val) % (binBase a s q cy)

theorem template_row_value {s L nv nb rx : ℕ} (order : ItemOrder nv nb)
    (p : Fin s) (ℓ : Fin L) :
    (rowCode s L nv nb rx order (.inl (p,ℓ))).val = ℓ.val+L*p.val := by
  rfl

theorem item_row_value {s L nv nb rx : ℕ} (order : ItemOrder nv nb)
    (i : Fin (nv + nb)) (x : Fin rx) :
    (rowCode s L nv nb rx order
      ((rawRowEquiv s L nv nb order).symm (.inr (i,x)))).val =
        s*L+x.val+rx*i.val := by
  simp only [MatrixStage4Codes.rowCode, Equiv.trans_apply, Equiv.apply_symm_apply]
  change s*L+(finProdFinEquiv (i,x)).val = _
  simp only [finProdFinEquiv_apply_val]
  omega

theorem column_tail_code {a s q cy : ℕ} (code : Fin (cols a s q cy)) :
    ((tupleCode cy (s+1)) ((rawColumnCode a s q cy).symm code).1).val =
      code.val / (binBase a s q cy)^s := by
  change ((tupleCode cy (s+1)) ((tupleCode cy (s+1)).symm code.divNat)).val = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem column_tail_digit {a s q cy : ℕ} (code : Fin (cols a s q cy))
    (j : Fin (s + 1)) :
    (((rawColumnCode a s q cy).symm code).1 j).val =
      (code.val / (binBase a s q cy)^s) / cy^(s-j.val) % cy := by
  change ((tupleCode cy (s+1)).symm code.divNat j).val = _
  rw [MatrixLabelArithmetic.tuple_digit]
  rfl

theorem column_bin_code {a s q cy : ℕ} (code : Fin (cols a s q cy))
    (p : Fin s) :
    (secondRowCode a s q cy (((rawColumnCode a s q cy).symm code).2 p)).val =
      binDigit code.val a s q cy p := by
  have hd := MatrixLabelArithmetic.tuple_digit
    (m := q * cy ^ firstLength a s) (n := s) code.modNat p
  simpa [rawColumnCode, thirdColumnCode, binDigit, binBase, wordBase] using hd

theorem second_row_alpha {a s q cy : ℕ}
    (r : SecondRows a s q (Fin cy)) :
    r.1.val = (secondRowCode a s q cy r).val / wordBase a s cy := by
  have hw := (firstWordCode a s cy r.2).isLt
  change r.1.val =
    (finProdFinEquiv (r.1, firstWordCode a s cy r.2)).val /
      cy ^ firstLength a s
  rw [finProdFinEquiv_apply_val]
  rw [Nat.add_mul_div_left _ _ (by omega : 0 < cy ^ firstLength a s)]
  simp [Nat.div_eq_of_lt hw]

theorem second_row_word {a s q cy : ℕ}
    (r : SecondRows a s q (Fin cy)) :
    (firstWordCode a s cy r.2).val =
      (secondRowCode a s q cy r).val % wordBase a s cy := by
  have hw := (firstWordCode a s cy r.2).isLt
  change (firstWordCode a s cy r.2).val =
    (finProdFinEquiv (r.1, firstWordCode a s cy r.2)).val %
      cy ^ firstLength a s
  rw [finProdFinEquiv_apply_val]
  simp [Nat.mod_eq_of_lt hw]

end EthInapproximability.CurrentPaper.MatrixStage4Digits
