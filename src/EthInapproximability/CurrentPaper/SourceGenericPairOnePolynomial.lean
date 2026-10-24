import EthInapproximability.CurrentPaper.SourceGenericPairPhasePolynomial

/-! A charged quartic clock for one concrete physical generic ordered-pair
routine. The coefficient depends only on the fixed alphabet and width. -/

namespace EthInapproximability.CurrentPaper.SourceGenericPairEnumeration

open SourceBooleanEncoding SourceClauseEncoding EncodedCNF
open SourceGenericPrefix SourceGenericPrefixMachine
open scoped Classical
set_option maxHeartbeats 2000000

def oneSize (n a q : Nat) (saved output count : List Bool) : Nat :=
  sourceSize n a q saved output count + wordBound n a q + 2*n + 20

noncomputable def oneCoefficient (a q : Nat) : Nat :=
  2*unitCoefficient a q+2*gateCoefficient a q+1

private theorem phaseSize_le (n a q : Nat)
    (saved saved' output count count' : List Bool)
    (hs : saved'.length ≤ saved.length + wordBound n a q)
    (hc : count'.length ≤ count.length+8) :
    sourceSize n a q saved' output count' ≤
      oneSize n a q saved output count := by
  dsimp [sourceSize,oneSize]
  omega

theorem one_cost_le_poly {n a q : Nat} (v : Fin n) (s t : Fin a)
    (saved output count : List Bool) :
    PairOneMachine.cost (q := q) v s t saved output count ≤
      oneCoefficient a q*(oneSize n a q saved output count)^4 := by
  let ord := pairOrdinal v s t
  let w := width a q+1
  let s₁ := UnitHandoff.nextSaved n a ord w 0 false saved
  let s₂ := (clauseFields (PairGateCleanup.emitted v s 0 ord w
    (decide (s=t)))).reverse ++ s₁
  let s₃ := (clauseFields (PairGateCleanup.emitted v t 1 ord w false)).reverse ++ s₂
  let s₄ := UnitHandoff.nextSaved n a ord w 2 true s₃
  let c₁ := true::count
  let c₂ := true::true::true::c₁
  let c₃ := true::true::true::c₂
  let S := oneSize n a q saved output count
  let U := unitCoefficient a q
  let G := gateCoefficient a q
  have hord := pairOrdinal_le v s t
  have hv := v.isLt
  have hword := pair_word_length_le q v s t
  have hs₄ : s₄.length ≤ saved.length+wordBound n a q := by
    change (PairSource.savedAfter (q := q) v s t saved).length ≤ _
    rw [PairSource.savedAfter_eq_chain (q := q) v s t saved]
    dsimp only [payload,pairChain] at hword
    simp only [List.length_reverse] at hword
    simp only [List.length_append,List.length_reverse]
    omega
  have hs₁ : s₁.length ≤ s₄.length := by
    dsimp [s₁,s₂,s₃,s₄,UnitHandoff.nextSaved]
    simp only [List.length_append]
    omega
  have hs₂ : s₂.length ≤ s₄.length := by
    dsimp [s₂,s₃,s₄,UnitHandoff.nextSaved]
    simp only [List.length_append]
    omega
  have hs₃ : s₃.length ≤ s₄.length := by
    dsimp [s₃,s₄,UnitHandoff.nextSaved]
    simp only [List.length_append]
    omega
  have hsize₀ : sourceSize n a q saved output count ≤ S := by
    dsimp [S,oneSize]
    omega
  have hsize₁ : sourceSize n a q s₁ output c₁ ≤ S :=
    phaseSize_le n a q saved s₁ output count c₁ (hs₁.trans hs₄)
      (by simp [c₁])
  have hsize₂ : sourceSize n a q s₂ output c₂ ≤ S :=
    phaseSize_le n a q saved s₂ output count c₂ (hs₂.trans hs₄)
      (by simp [c₂,c₁])
  have hsize₃ : sourceSize n a q s₃ output c₃ ≤ S :=
    phaseSize_le n a q saved s₃ output count c₃ (hs₃.trans hs₄)
      (by simp [c₃,c₂,c₁])
  have hpow₀ := pow_le_pow_left₀ (by omega) hsize₀ 4
  have hpow₁ := pow_le_pow_left₀ (by omega) hsize₁ 4
  have hpow₂ := pow_le_pow_left₀ (by omega) hsize₂ 4
  have hpow₃ := pow_le_pow_left₀ (by omega) hsize₃ 4
  have hU₀ : PairOneMachine.unitCost n a ord w 0 false
      saved output count ≤ U*S^4 :=
    (unit_cost_le_source_poly v s t 0 false saved output count
      (Or.inl ⟨rfl,rfl⟩)).trans (Nat.mul_le_mul_left U hpow₀)
  have hU₂ : PairOneMachine.unitCost n a ord w 2 true
      s₃ output c₃ ≤ U*S^4 :=
    (unit_cost_le_source_poly v s t 2 true s₃ output c₃
      (Or.inr ⟨rfl,rfl⟩)).trans (Nat.mul_le_mul_left U hpow₃)
  have hG₀ : PairOneMachine.gateCost v s 0 ord w (decide (s=t))
      s₁ output c₁ ≤ G*S^4 :=
    (gate_cost_le_source_poly v s t s 0 (decide (s=t))
      s₁ output c₁).trans (Nat.mul_le_mul_left G hpow₁)
  have hG₁ : PairOneMachine.gateCost v t 1 ord w false
      s₂ output c₂ ≤ G*S^4 :=
    (gate_cost_le_source_poly v s t t 1 false
      s₂ output c₂).trans (Nat.mul_le_mul_left G hpow₂)
  have hoverhead : SourceBooleanPrefix.SourceGenericPairOrdinal.clock n v.val+ord+2+5 ≤ S := by
    dsimp [SourceBooleanPrefix.SourceGenericPairOrdinal.clock,S,oneSize,sourceSize]
    omega
  have hS1 : 1 ≤ S := by dsimp [S,oneSize,sourceSize]; omega
  have hS4 : S ≤ S^4 := by
    have h2 : S ≤ S^2 := by nlinarith
    have h24 : S^2 ≤ S^4 := by
      calc
        S^2 = S*S := by ring
        _ ≤ S^2*S^2 := Nat.mul_le_mul h2 h2
        _ = S^4 := by ring
    exact h2.trans h24
  change PairOneMachine.cost (q := q) v s t saved output count ≤
    oneCoefficient a q*S^4
  dsimp only [PairOneMachine.cost]
  change SourceBooleanPrefix.SourceGenericPairOrdinal.clock n v.val+
      PairOneMachine.unitCost n a ord w 0 false saved output count+1+
      PairOneMachine.gateCost v s 0 ord w (decide (s=t)) s₁ output c₁+1+
      PairOneMachine.gateCost v t 1 ord w false s₂ output c₂+1+
      PairOneMachine.unitCost n a ord w 2 true s₃ output c₃+1+
      (ord+2)+1 ≤ oneCoefficient a q*S^4
  dsimp only [oneCoefficient]
  nlinarith only [hU₀,hU₂,hG₀,hG₁,hoverhead,hS4]

#print axioms one_cost_le_poly

end EthInapproximability.CurrentPaper.SourceGenericPairEnumeration
