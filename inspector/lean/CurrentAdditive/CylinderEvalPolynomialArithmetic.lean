import CurrentAdditive.CylinderEvalByteBounds

namespace CurrentAdditive.CylinderEvalPolynomialArithmetic

theorem power_envelope (N C R d r : ℕ) :
    N+C*(N+1)^d+R*(N+1)^r+1≤
      (C+R+1)*(N+1)^(max 1 (max d r)) := by
  let e := max 1 (max d r)
  have h1 : N+1≤(N+1)^e := by
    simpa using Nat.pow_le_pow_right (by omega : 0<N+1) (show 1≤e by dsimp [e];omega)
  have hd : (N+1)^d≤(N+1)^e :=
    Nat.pow_le_pow_right (by omega) (by dsimp [e];omega)
  have hr : (N+1)^r≤(N+1)^e :=
    Nat.pow_le_pow_right (by omega) (by dsimp [e];omega)
  have hc := Nat.mul_le_mul_left C hd
  have hR := Nat.mul_le_mul_left R hr
  nlinarith

theorem map_envelope (N C R d r K E : ℕ) :
    K*(N+C*(N+1)^d+R*(N+1)^r+1)^E≤
      (K*(C+R+1)^E)*(N+1)^((max 1 (max d r))*E) := by
  have h := Nat.mul_le_mul_left K
    (Nat.pow_le_pow_left (power_envelope N C R d r) E)
  simpa only [Nat.mul_pow,← Nat.pow_mul,Nat.mul_assoc] using h

theorem routed_envelope (N C d : ℕ) :
    C*(2*N+1)^d≤(C*2^d)*(N+1)^d := by
  have h := Nat.mul_le_mul_left C
    (Nat.pow_le_pow_left (show 2*N+1≤2*(N+1) by omega) d)
  simpa only [Nat.mul_pow,Nat.mul_assoc] using h

theorem linear_plus (N C A d : ℕ) (hd : 1≤d) :
    C*(N+1)^d+A*(N+1)≤(C+A)*(N+1)^d := by
  have hp : N+1≤(N+1)^d := by
    simpa using Nat.pow_le_pow_right (by omega : 0<N+1) hd
  have hm := Nat.mul_le_mul_left A hp
  nlinarith

def mapDegree (d E : ℕ) : ℕ := max 1 (d*E)

def mapCoefficient (K E C R d : ℕ) : ℕ :=
  (K*(C+R+1)^E)*2^(d*E)+40

theorem routed_power (N T mapped K E : ℕ) (hT : T≤2*N)
    (hm : mapped≤K*(T+1)^E) :
    30*(N+1)+2*T+2+mapped≤(K*2^E+40)*(N+1)^(max 1 E) := by
  have hbase := Nat.mul_le_mul_left K
    (Nat.pow_le_pow_left (show T+1≤2*N+1 by omega) E)
  have hroute := routed_envelope N K E
  have hlift := Nat.mul_le_mul_left (K*2^E)
    (Nat.pow_le_pow_right (by omega : 0<N+1) (show E ≤ max 1 E by omega))
  have htot : 30*(N+1)+2*T+2+mapped≤
      (K*2^E)*(N+1)^(max 1 E)+40*(N+1) := by nlinarith
  exact htot.trans (linear_plus N _ 40 (max 1 E) (by omega))

theorem routed_map_envelope (N T mapped K E C R d : ℕ)
    (hd : 1≤d) (hT : T≤2*N)
    (hm : mapped≤K*(T+C*(T+1)^d+R*(T+1)+1)^E) :
    30*(N+1)+2*T+2+mapped≤
      mapCoefficient K E C R d*(N+1)^(mapDegree d E) := by
  have he : max 1 (max d 1)=d := by omega
  have hmap := map_envelope T C R d 1 K E
  simp only [pow_one,he] at hmap
  have hbase := Nat.mul_le_mul_left (K*(C+R+1)^E)
    (Nat.pow_le_pow_left (show T+1≤2*N+1 by omega) (d*E))
  have hroute := routed_envelope N (K*(C+R+1)^E) (d*E)
  have hlift := Nat.mul_le_mul_left ((K*(C+R+1)^E)*2^(d*E))
    (Nat.pow_le_pow_right (by omega : 0<N+1) (show d*E ≤ mapDegree d E by dsimp [mapDegree];omega))
  have htot : 30*(N+1)+2*T+2+mapped≤
      ((K*(C+R+1)^E)*2^(d*E))*(N+1)^(mapDegree d E)+40*(N+1) := by
    nlinarith
  exact htot.trans (linear_plus N _ 40 (mapDegree d E) (by dsimp [mapDegree];omega))

end CurrentAdditive.CylinderEvalPolynomialArithmetic

#print axioms CurrentAdditive.CylinderEvalPolynomialArithmetic.map_envelope
