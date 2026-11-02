import CurrentV43.PowerSchedule

namespace CurrentAdditive.V43PowerSchedule
noncomputable section
open EthInapproximability.CurrentPaper PhysicalProducer
set_option maxHeartbeats 1000000

theorem sparse_input_bound (density : Nat) (Φ : EncodedETHSource.ValidFormula)
    (hsp : Φ.val.clauses.length ≤ density*Φ.val.variables) :
    (EncodedCNF.encode Φ.val).length+1 ≤ (14*density+4)*(Φ.val.variables+1)^2 := by
  have h := EncodedCNF.encode_length_upper Φ.val Φ.property
  have hs := Nat.mul_le_mul_right (6*Φ.val.variables+8) hsp
  have h1 : Φ.val.variables+3 ≤ 4*(Φ.val.variables+1)^2 := by nlinarith
  have h2 : Φ.val.variables*(6*Φ.val.variables+8) ≤ 14*(Φ.val.variables+1)^2 := by
    nlinarith
  have h3 := Nat.mul_le_mul_left density h2
  nlinarith

/-- The cost is paid in the original number of variables, uniformly on
every formula of fixed clause density. There is no large-input premise. -/
theorem formula_paid (a b density : Nat) :
    ∃ c d : Nat, ∀ Φ : EncodedETHSource.ValidFormula,
      Φ.val.clauses.length ≤ density*Φ.val.variables →
      (localProducer (formula a b)).clock (EncodedCNF.encode Φ.val) ≤
        c*(Φ.val.variables+gap a b Φ.val.variables+1)^d := by
  let F := formula a b
  refine ⟨F.coefficient*(14*density+4)^F.degree,2*F.degree,?_⟩
  intro Φ hsp
  let W := Φ.val.variables+gap a b Φ.val.variables+1
  have hW : Φ.val.variables+1 ≤ W := by dsimp [W]; omega
  have hin := (sparse_input_bound density Φ hsp).trans
    (Nat.mul_le_mul_left (14*density+4) (Nat.pow_le_pow_left hW 2))
  change F.coefficient*((EncodedCNF.encode Φ.val).length+1)^F.degree ≤
    (F.coefficient*(14*density+4)^F.degree)*W^(2*F.degree)
  calc
    _ ≤ F.coefficient*((14*density+4)*W^2)^F.degree :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hin _)
    _ = (F.coefficient*(14*density+4)^F.degree)*W^(2*F.degree) := by
      rw [mul_pow,←pow_mul]
      ring

#print axioms sparse_input_bound
#print axioms formula_paid
end
end CurrentAdditive.V43PowerSchedule
