import CurrentAdditive.V22PublicRepeatRun

namespace V22PublicRepeat
noncomputable section
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open V22UnaryExpression
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem q0_peak (s m : ℕ) :
    q0Expression.peak s m ≤ V22RepeatArithmetic.q0 s m+4*s+m+4 := by
  have hprod : 4*s*m ≤ V22RepeatArithmetic.q0 s m :=
    Nat.le_pow_clog (by decide) _
  have hlog : Nat.clog 2 (4*s*m) ≤ V22RepeatArithmetic.q0 s m :=
    (Nat.lt_two_pow_self).le
  simp only [q0Expression,Expr.peak,Expr.eval,Unary.value,Binary.value,
    V22RepeatArithmetic.q0,max_le_iff]
  dsimp only [V22RepeatArithmetic.q0] at hprod hlog
  omega

def clockCoefficient : ℕ := 1000+36*q0Expression.coefficient

theorem clock_polynomial (g : EncodedGraph.Graph) (s q₂ : ℕ)
    (hq0 : V22RepeatArithmetic.q0 s g.edges.length ≤ q₂) :
    clock g s q₂ ≤ clockCoefficient *
      ((EncodedGraph.encode g).length+s+g.edges.length+q₂+1)^3 := by
  let M := V22RepeatArithmetic.q0 s g.edges.length+4*s+g.edges.length+4
  let W := (EncodedGraph.encode g).length+s+g.edges.length+q₂+1
  have hW : 1 ≤ W := by dsimp [W]; omega
  have hsq₀ : W ≤ W^2 := by nlinarith
  have hsq : W^2 ≤ W^3 := by
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ hW
  have hlin : W ≤ W^3 := hsq₀.trans hsq
  have hq := q0Expression.clock_le_of_peak s g.edges.length M (q0_peak s g.edges.length)
  have hscale : s+g.edges.length+M+2 ≤ 6*W := by dsimp [M,W]; omega
  have hsquare := Nat.pow_le_pow_left hscale 2
  have hqclock : q0Clock s g.edges.length ≤ 36*q0Expression.coefficient*W^2 := by
    change q0Expression.clock s g.edges.length ≤ _
    nlinarith [Nat.mul_le_mul_left q0Expression.coefficient hsquare]
  have hqclock' : q0Clock s g.edges.length ≤ 36*q0Expression.coefficient*W^3 :=
    hqclock.trans (Nat.mul_le_mul_left _ hsq)
  have hparser : 100*((EncodedGraph.encode g).length+1)^3 ≤ 100*W^3 := by
    apply Nat.mul_le_mul_left
    exact Nat.pow_le_pow_left (by dsimp [W]; omega) 3
  have hdiv := V22ParameterDivide.clock_linear q₂ (V22RepeatArithmetic.q0 s g.edges.length)
  have hpairs : pairClock s g.edges.length=5*s+5*g.edges.length+14 := by
    simp only [pairClock,MatrixUnaryArithmetic.encodeInput,List.length_append,List.length_replicate,
      List.length_cons,List.length_nil]
    omega
  unfold clock edgeClock powClock
  rw [hpairs]
  simp only [MatrixUnaryArithmetic.encodeInput,List.length_append,List.length_replicate,List.length_cons,List.length_nil]
  have hrest : 2*(EncodedGraph.encode g).length+7*s+9*g.edges.length+19*q₂+29 ≤ 100*W := by
    dsimp [W]
    omega
  dsimp only [clockCoefficient]
  dsimp only [W] at hlin hsq hqclock' hparser hrest ⊢
  nlinarith

end
#print axioms V22PublicRepeat.clock_polynomial
end V22PublicRepeat
