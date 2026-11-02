import CurrentAdditive.GaussPivotRawClock32

namespace CurrentAdditive.GaussPivotRawInput32

open CurrentAdditive.GaussStepFields32

private theorem bank_le_sum (S : Stack → List Bool) (j : Stack) :
    (S j).length ≤ ∑ i : Stack, (S i).length := by
  exact Finset.single_le_sum
    (s := Finset.univ) (f := fun i => (S i).length)
    (fun i hi => Nat.zero_le _)
    (Finset.mem_univ j)

theorem bank_le_charge {m k : Nat}
    (s : GaussControlTrace.State m k)
    (foreign : Stack → List Bool) (j : Stack) :
    ((GaussStepParseRun32.raw s foreign).stk j).length ≤
      GaussPivotRawClock32.inputBankCharge s foreign := by
  exact bank_le_sum (GaussStepParseRun32.raw s foreign).stk j

#print axioms bank_le_charge

end CurrentAdditive.GaussPivotRawInput32
