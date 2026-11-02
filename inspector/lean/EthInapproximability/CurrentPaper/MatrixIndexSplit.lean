import EthInapproximability.CurrentPaper.MatrixIndexQuotient

/-!
# Physical mixed-radix split before cleanup

Frozen v8 `B-effectivity-details.tex`, proof of `thm:paper-materialization`:
row, column and group labels are decoded by quotient and remainder.  This
checkpoint of the fixed `MatrixIndexQuotient` program exposes both results
before its remainder-cleanup state executes.  The source label, divisor and
all their unary bits have been preserved, and every elapsed transition is
charged.  It is an operational stage, not a free arithmetic accessor.
-/

namespace EthInapproximability.CurrentPaper.MatrixIndexSplit

open EthInapproximability.CurrentPaper.MatrixIndexQuotient

theorem split_run (n m : ℕ) :
    ∃ t ≤ 10*n+3*m+6,
      run t (cfg (some start) initial (List.replicate n true)
        (List.replicate m true) [] [] [] [] [] []) =
      cfg (some clear) initial (List.replicate n true)
        (List.replicate m true) [] [] [] (List.replicate (n%m) true)
        (List.replicate (n/m) true) [] := by
  obtain ⟨a,ha,he⟩ := copy_run n m
  obtain ⟨b,hb,hr⟩ := division_run n m
  refine ⟨a+b,?_,?_⟩
  · have htime := MatrixUnaryDivision.totalTime_bound n m
    omega
  · exact run_add he b |>.trans hr

end EthInapproximability.CurrentPaper.MatrixIndexSplit
