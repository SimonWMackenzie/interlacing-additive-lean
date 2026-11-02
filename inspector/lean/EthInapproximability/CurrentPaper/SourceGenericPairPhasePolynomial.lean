import EthInapproximability.CurrentPaper.SourceGenericPairGateEnvelope

/-! Fixed-(alphabet, width) quartic envelopes for the two physical unit and
gate phases of a generic ordered pair. -/

namespace EthInapproximability.CurrentPaper.SourceGenericPairEnumeration

open SourceGenericPrefixMachine SourceBooleanPrefix SourceBooleanEncoding
open scoped Classical
set_option maxHeartbeats 2000000

def sourceSize (n a q : Nat) (saved output count : List Bool) : Nat :=
  2*n+a+ordinalBound n a+width a q+12+
    saved.length+output.length+count.length

noncomputable def unitStepCoefficient (a q : Nat) : Nat :=
  BitMachineStackGrowth.perStep
      (UnitCycle.pairProgram a (width a q+1) 0 false) +
    BitMachineStackGrowth.perStep
      (UnitCycle.pairProgram a (width a q+1) 2 true)

private theorem finite_image_bound {α : Type} [Fintype α]
    (f : α → Nat) : ∃ C, ∀ x, f x ≤ C := by
  classical
  exact ⟨Finset.univ.sup f, fun x => Finset.le_sup
    (f := f) (Finset.mem_univ x)⟩

noncomputable def gateStepCoefficient (a q : Nat) : Nat :=
  Classical.choose (finite_image_bound
    (fun x : Fin a × Fin 2 × Bool =>
    BitMachineStackGrowth.perStep
      (SourceGenericPrefixMachine.PairGateCycle.firstProgram
        x.1 x.2.1 x.2.2 (width a q+1))))

theorem gate_step_le (a q : Nat) (bit : Fin a) (ell : Fin 2)
    (sign : Bool) :
    BitMachineStackGrowth.perStep
      (SourceGenericPrefixMachine.PairGateCycle.firstProgram
        bit ell sign (width a q+1)) ≤ gateStepCoefficient a q := by
  exact (Classical.choose_spec (finite_image_bound
    (fun x : Fin a × Fin 2 × Bool =>
    BitMachineStackGrowth.perStep
      (SourceGenericPrefixMachine.PairGateCycle.firstProgram
        x.1 x.2.1 x.2.2 (width a q+1))))) (bit,ell,sign)

noncomputable def unitCoefficient (a q : Nat) : Nat :=
  (16*UnaryBinaryEncoding.coefficient+100)*
    (1+PrefixLoopCost.workCount*unitStepCoefficient a q)+
    2*PrefixLoopCost.workCount+4

noncomputable def gateCoefficient (a q : Nat) : Nat :=
  100000*(UnaryBinaryEncoding.coefficient+1)*
    (1+PairGateCost.workCount*gateStepCoefficient a q)+
    2*PairGateCost.workCount+4

theorem unit_cost_le_source_poly {n a q : Nat}
    (v : Fin n) (s t : Fin a) (ell : Nat) (sign : Bool)
    (saved output count : List Bool)
    (hcase : (ell=0 ∧ sign=false) ∨ (ell=2 ∧ sign=true)) :
    PairOneMachine.unitCost n a (SourceGenericPrefix.pairOrdinal v s t)
      (width a q+1) ell sign saved output count ≤
    unitCoefficient a q * (sourceSize n a q saved output count)^4 := by
  let ord := SourceGenericPrefix.pairOrdinal v s t
  let w := width a q+1
  let S := sourceSize n a q saved output count
  let P := UnitCycle.pairCost n a ord w ell saved output count
  let D := BitMachineStackGrowth.perStep (UnitCycle.pairProgram a w ell sign)
  let H := n+ord+saved.length+output.length+count.length
  let K := 16*UnaryBinaryEncoding.coefficient+100
  let W := PrefixLoopCost.workCount
  have hord := pairOrdinal_le v s t
  have hell : ell ≤ 2 := by rcases hcase with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> omega
  have hM : n+a+ord+w+ell+1 ≤ S := by
    have hv := v.isLt
    dsimp [S,sourceSize,w]
    omega
  have hP : P ≤ K*S^4 := by
    have hp := unit_pairCost_le_poly n a ord w ell saved output count
    have hm := pow_le_pow_left₀ (by omega) hM 4
    exact hp.trans (Nat.mul_le_mul_left K hm)
  have hD : D ≤ unitStepCoefficient a q := by
    rcases hcase with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      dsimp [D,unitStepCoefficient,w] <;> omega
  have hH : H ≤ S := by dsimp [H,S,sourceSize]; omega
  have hS1 : 1 ≤ S := by dsimp [S,sourceSize]; omega
  have hS4 : S ≤ S^4 := by
    have h2 : S ≤ S^2 := by nlinarith
    have h24 : S^2 ≤ S^4 := by
      calc
        S^2 = S*S := by ring
        _ ≤ S^2*S^2 := Nat.mul_le_mul h2 h2
        _ = S^4 := by ring
    exact h2.trans h24
  have hS41 : 1 ≤ S^4 := by omega
  have henv := unit_cost_le_envelope n a ord w ell sign
    saved output count
  have hdp := Nat.mul_le_mul hD hP
  have hmass := Nat.mul_le_mul_left W
    (show H+D*P ≤ (1+unitStepCoefficient a q*K)*S^4 by
      nlinarith only [hH,hS4,hdp])
  change UnitCycle.cost n a ord w ell sign saved output count ≤
    (K*(1+W*unitStepCoefficient a q)+2*W+4)*S^4
  change UnitCycle.cost n a ord w ell sign saved output count ≤
    P+W*(H+D*P)+W+3 at henv
  have hextra : W+3 ≤ (W+4)*S^4 := by
    have hW := Nat.mul_le_mul_left W hS41
    have h4 := Nat.mul_le_mul_left 4 hS41
    calc
      W+3 ≤ W*S^4+4*S^4 := by omega
      _ = (W+4)*S^4 := by ring
  calc
    _ ≤ P+W*(H+D*P)+W+3 := henv
    _ ≤ K*S^4+W*((1+unitStepCoefficient a q*K)*S^4)+
        (W+4)*S^4 := by omega
    _ = (K*(1+W*unitStepCoefficient a q)+2*W+4)*S^4 := by ring

theorem gate_cost_le_source_poly {n a q : Nat}
    (v : Fin n) (s t : Fin a) (bit : Fin a) (ell : Fin 2)
    (sign : Bool) (saved output count : List Bool) :
    PairOneMachine.gateCost v bit ell
      (SourceGenericPrefix.pairOrdinal v s t) (width a q+1)
      sign saved output count ≤
    gateCoefficient a q*(sourceSize n a q saved output count)^4 := by
  let ord := SourceGenericPrefix.pairOrdinal v s t
  let w := width a q+1
  let S := sourceSize n a q saved output count
  let P := gatePre v bit ell ord w sign
  let D := BitMachineStackGrowth.perStep
    (SourceGenericPrefixMachine.PairGateCycle.firstProgram bit ell sign w)
  let H := n+v.val+ord+saved.length+output.length+count.length
  let K := 100000*(UnaryBinaryEncoding.coefficient+1)
  let W := PairGateCost.workCount
  have hord := pairOrdinal_le v s t
  have hM : n+a+v.val+ord+w+ell.val+5 ≤ S := by
    have hv := v.isLt
    have he := ell.isLt
    dsimp [S,sourceSize,w]
    omega
  have hP : P ≤ K*S^4 := by
    have hp := gate_pre_le_poly v bit ell ord w sign
    have hm := pow_le_pow_left₀ (by omega) hM 4
    exact hp.trans (Nat.mul_le_mul_left K hm)
  have hD : D ≤ gateStepCoefficient a q :=
    gate_step_le a q bit ell sign
  have hH : H ≤ S := by
    have hv := v.isLt
    dsimp [H,S,sourceSize]
    omega
  have hS1 : 1 ≤ S := by dsimp [S,sourceSize]; omega
  have hS4 : S ≤ S^4 := by
    have h2 : S ≤ S^2 := by nlinarith
    have h24 : S^2 ≤ S^4 := by
      calc
        S^2 = S*S := by ring
        _ ≤ S^2*S^2 := Nat.mul_le_mul h2 h2
        _ = S^4 := by ring
    exact h2.trans h24
  have hS41 : 1 ≤ S^4 := by omega
  have henv := gate_cost_le_envelope v bit ell ord w sign
    saved output count
  have hdp := Nat.mul_le_mul hD hP
  have hmass := Nat.mul_le_mul_left W
    (show H+D*P ≤ (1+gateStepCoefficient a q*K)*S^4 by
      nlinarith only [hH,hS4,hdp])
  change PairOneMachine.gateCost v bit ell ord w sign
    saved output count ≤
      (K*(1+W*gateStepCoefficient a q)+2*W+4)*S^4
  change PairOneMachine.gateCost v bit ell ord w sign
    saved output count ≤ P+W*(H+D*P)+W+3 at henv
  have hextra : W+3 ≤ (W+4)*S^4 := by
    have hW := Nat.mul_le_mul_left W hS41
    have h4 := Nat.mul_le_mul_left 4 hS41
    calc
      W+3 ≤ W*S^4+4*S^4 := by omega
      _ = (W+4)*S^4 := by ring
  calc
    _ ≤ P+W*(H+D*P)+W+3 := henv
    _ ≤ K*S^4+W*((1+gateStepCoefficient a q*K)*S^4)+
        (W+4)*S^4 := by omega
    _ = (K*(1+W*gateStepCoefficient a q)+2*W+4)*S^4 := by ring

#print axioms unit_cost_le_source_poly
#print axioms gate_cost_le_source_poly

end EthInapproximability.CurrentPaper.SourceGenericPairEnumeration
