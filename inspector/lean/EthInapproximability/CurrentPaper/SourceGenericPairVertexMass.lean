import EthInapproximability.CurrentPaper.SourceGenericPairVertex

/-! Reusable absorption of charged one-pair costs across a finite pair list.
This is a conditional arithmetic lemma, not yet a polynomial claim for the
concrete one-pair routine. -/

namespace EthInapproximability.CurrentPaper.SourceGenericPairEnumeration

open SourceBooleanPrefix.PairMachineComposition

theorem listCost_mass_bound {α : Type}
    (stepCost : α → List Bool → List Bool → List Bool → Nat)
    (payload : α → List Bool) (xs : List α)
    (saved output count : List Bool) (B L C d : Nat)
    (hpayload : ∀ x, (payload x).length ≤ L)
    (hstep : ∀ x saved output count,
      stepCost x saved output count ≤
        C * (B + saved.length + output.length + count.length + 1)^d) :
    listCost stepCost payload xs saved output count ≤
      (xs.length + 1) *
        (C * (B + saved.length + output.length + count.length +
          xs.length * (L + 8) + 1)^d + 1) := by
  induction xs generalizing saved count with
  | nil =>
      simp only [listCost, List.length_nil, zero_mul, add_zero, zero_add, one_mul]
      omega
  | cons x xs ih =>
      let M := B + saved.length + output.length + count.length +
        (x::xs).length * (L+8) + 1
      let T := B + (payload x ++ saved).length + output.length +
        (List.replicate 8 true ++ count).length + xs.length * (L+8) + 1
      have hheadMass : B + saved.length + output.length + count.length + 1 ≤ M := by
        dsimp [M]
        omega
      have htailMass : T ≤ M := by
        dsimp [T, M]
        simp only [List.length_append, List.length_replicate, List.length_cons,
          Nat.add_mul, Nat.one_mul]
        have hp := hpayload x
        omega
      have hhead : stepCost x saved output count ≤ C*M^d := by
        calc
          _ ≤ C*(B + saved.length + output.length + count.length + 1)^d :=
            hstep x saved output count
          _ ≤ C*M^d := by gcongr
      have htail := ih (payload x ++ saved) (List.replicate 8 true ++ count)
      have htail' :
          listCost stepCost payload xs (payload x ++ saved) output
            (List.replicate 8 true ++ count) ≤
          (xs.length+1)*(C*M^d+1) := by
        calc
          _ ≤ (xs.length+1)*(C*T^d+1) := htail
          _ ≤ (xs.length+1)*(C*M^d+1) := by gcongr
      change stepCost x saved output count +
          listCost stepCost payload xs (payload x ++ saved) output
            (List.replicate 8 true ++ count) + 1 ≤
        ((x::xs).length+1)*(C*M^d+1)
      simp only [List.length_cons]
      nlinarith [hhead, htail']

#print axioms listCost_mass_bound

end EthInapproximability.CurrentPaper.SourceGenericPairEnumeration
