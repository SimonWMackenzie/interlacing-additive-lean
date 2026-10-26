import EthInapproximability.CurrentPaper.SignedMidpointApproxCost

/-!
# Explicit polynomial majorant for the actual approximation callback

For a fixed approximation machine and its fixed polynomial witness `c,d`,
the physical packet callback has one fixed polynomial bound in packet length.
The coefficient depends on the actual finite program's push bound and stack
count; it does not depend on the number of source branches.
-/

namespace EthInapproximability.CurrentPaper.SignedMidpointApproxPolynomial

variable (M : BitMachine.Machine) (c d : ℕ)

def capCoefficient : ℕ := c+10+60*(c*M.pushBound+1)

noncomputable def decisionCoefficient : ℕ :=
  let K := SignedMidpointApproxPacket.Width M
  let q := (SignedMidpointApproxPacket.rawMachine M).pushBound
  let C := capCoefficient M c
  (2*K+1)+C+(2*K+8)*(1+2*K*C*q)+(2*K+10)

theorem callbackCostBound_polynomial (n : ℕ) :
    SignedMidpointApproxCost.callbackCostBound M n (c*(n+1)^d) ≤
      capCoefficient M c*(n+1)^(d+2) := by
  let U := n+1
  let P := U^(d+2)
  let p := M.pushBound
  let C := capCoefficient M c
  have hU : 0 < U := by omega
  have hP : 1 ≤ P := by
    have hp := pow_pos hU (d+2)
    dsimp [P]
    omega
  have hpow1 : U^d ≤ U^(d+1) :=
    Nat.pow_le_pow_right hU (by omega)
  have hpow2 : U^(d+1) ≤ P := by
    exact Nat.pow_le_pow_right hU (by omega : d+1 ≤ d+2)
  have hUpow : U ≤ U^(d+1) := by
    calc
      U = U^1 := by simp
      _ ≤ U^(d+1) := Nat.pow_le_pow_right hU (by omega)
  have hUP : U ≤ P := hUpow.trans hpow2
  have hb : c*U^d ≤ c*P :=
    Nat.mul_le_mul_left c (hpow1.trans hpow2)
  have hinner : n+c*U^d*p+1 ≤ (c*p+1)*U^(d+1) := by
    have hmul := Nat.mul_le_mul_right p (Nat.mul_le_mul_left c hpow1)
    calc
      n+c*U^d*p+1 = U+c*U^d*p := by omega
      _ ≤ U^(d+1)+c*U^(d+1)*p := by omega
      _ = (c*p+1)*U^(d+1) := by ring
  have hfactor : 3*n+1 ≤ 3*U := by omega
  have hprod := Nat.mul_le_mul hinner hfactor
  have hprod' :
      (n+c*U^d*p+1)*(3*n+1) ≤
        3*(c*p+1)*P := by
    calc
      _ ≤ ((c*p+1)*U^(d+1))*(3*U) := hprod
      _ = 3*(c*p+1)*P := by
        dsimp [P]
        rw [show d+2 = d+1+1 by omega, pow_succ]
        ring
  have hprod20 := Nat.mul_le_mul_left 20 hprod'
  have hn : n ≤ P := by omega
  have hconst : 6 ≤ 6*P := by omega
  change c*U^d+1+4*n+3+
      20*(n+c*U^d*p+1)*(3*n+1)+2 ≤ C*P
  have hterm : 20*(n+c*U^d*p+1)*(3*n+1) ≤
      60*(c*p+1)*P := by
    calc
      _ = 20*((n+c*U^d*p+1)*(3*n+1)) := by ring
      _ ≤ 20*(3*(c*p+1)*P) := hprod20
      _ = 60*(c*p+1)*P := by ring
  dsimp [C, capCoefficient]
  nlinarith

theorem decisionBound_polynomial (n : ℕ) :
    SignedMidpointApproxPacket.decisionBound M n
      (SignedMidpointApproxCost.callbackCostBound M n (c*(n+1)^d)) ≤
        decisionCoefficient M c*(n+1)^(d+2) := by
  let U := n+1
  let P := U^(d+2)
  let K := SignedMidpointApproxPacket.Width M
  let q := (SignedMidpointApproxPacket.rawMachine M).pushBound
  let C := capCoefficient M c
  let B := SignedMidpointApproxCost.callbackCostBound M n (c*U^d)
  have hB : B ≤ C*P := callbackCostBound_polynomial M c d n
  have hU : 0 < U := by omega
  have hP : 1 ≤ P := by
    have hp := pow_pos hU (d+2)
    exact hp
  have hUP : U ≤ P := by
    calc
      U = U^1 := by simp
      _ ≤ P := Nat.pow_le_pow_right hU (by omega : 1 ≤ d+2)
  have hn : n ≤ P := by omega
  have hBterm : 2*K*B*q ≤ 2*K*(C*P)*q :=
    Nat.mul_le_mul_right q (Nat.mul_le_mul_left (2*K) hB)
  have hinner : n+2*K*B*q ≤ (1+2*K*C*q)*P := by
    calc
      _ ≤ P+2*K*(C*P)*q := Nat.add_le_add hn hBterm
      _ = (1+2*K*C*q)*P := by ring
  have hlead := Nat.mul_le_mul_left (2*K+1) hUP
  have houter := Nat.mul_le_mul_left (2*K+8) hinner
  have hconst := Nat.mul_le_mul_left (2*K+10) hP
  change (2*K+1)*U+B+(2*K+8)*(n+2*K*B*q)+(2*K+10) ≤
    decisionCoefficient M c*P
  calc
    _ ≤ (2*K+1)*P+C*P+
        (2*K+8)*((1+2*K*C*q)*P)+(2*K+10)*P := by omega
    _ = decisionCoefficient M c*P := by
      dsimp [decisionCoefficient, K, q, C]
      ring

theorem callback_decision_fixed_polynomial
    (answer : List Bool → ℤ)
    (hM : M.ComputesWithin
      (fun table => EncodedETHTail.encodeInteger (answer table))
      (fun n => c*(n+1)^d))
    (table : List Bool) (Y k : ℕ) :
    (SignedMidpointApproxPacket.decisionMachine M).OutputsWithin
      (SignedMidpointApproxPacket.packet M table Y k)
      [decide (2*answer table < (2*Y+k : ℤ))]
      (decisionCoefficient M c *
        ((SignedMidpointApproxPacket.packet M table Y k).length+1)^(d+2)) := by
  have hrun := SignedMidpointApproxCost.callback_decision_polynomial_on_packet
    M answer c d hM table Y k
  have htime := decisionBound_polynomial M c d
    (SignedMidpointApproxPacket.packet M table Y k).length
  exact BitMachine.outputsWithin_mono _ hrun htime

end EthInapproximability.CurrentPaper.SignedMidpointApproxPolynomial
