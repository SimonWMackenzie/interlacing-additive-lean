import CurrentAdditive.V39UniformResource

/-! Elementary base change for the already absorbed iteration bound.
The polynomial prefix and the unary round count are paid at the original
input base; no eventual cutoff is used. -/
namespace CurrentAdditive.V40IterationBaseChange
set_option maxHeartbeats 8000000

theorem base_le_linear_exponent (N K : Nat) (hN : 2≤N) : N+K+1≤N^(K+2) := by
  induction K with
  | zero => simpa only [Nat.add_zero,Nat.zero_add,pow_two] using (show N+1≤N*N by nlinarith)
  | succ K ih =>
      have hp : 1≤N^(K+2) := Nat.one_le_pow _ _ (by omega)
      have hm : N^(K+2)+1≤N^(K+2)*N := by nlinarith
      calc
        N+(K+1)+1≤N^(K+2)+1 := by omega
        _ ≤ N^(K+2)*N := hm
        _ = N^((K+1)+2) := by rw [←pow_succ]

theorem base_le_original (N K : Nat) (hN : 2≤N) : N+K+1≤N^(2*2^K) := by
  have hK : K+1≤2^K := (Nat.lt_two_pow_self : K<2^K)
  have hp : 1≤(2:Nat)^K := Nat.one_le_two_pow
  exact (base_le_linear_exponent N K hN).trans
    (Nat.pow_le_pow_right (by omega) (by omega))

theorem remove_K_from_power (N K c A : Nat) (hN : 2≤N) :
    (N+K+1)^(c*A^K)≤N^((2*c)*(2*A)^K) := by
  calc
    _ ≤ (N^(2*2^K))^(c*A^K) := Nat.pow_le_pow_left (base_le_original N K hN) _
    _ = _ := by rw [←pow_mul,mul_pow];congr 1;ring

theorem prefix_polynomial_bound (c d A N K : Nat) (hA : 2≤A) (hN : 2≤N) :
    c*(N+K+1)^d≤N^((2*V39UniformResource.seedExponent c d)*A^K) := by
  let B := N+K+1
  have hB : 2≤B := by dsimp [B];omega
  have hpoly := V39UniformResource.seed_envelope_le_power c d B (c*B^d) hB le_rfl
  have hp : c*B^d≤B^(V39UniformResource.seedExponent c d) := by omega
  have hc := remove_K_from_power N K (V39UniformResource.seedExponent c d) 1 hN
  simp only [one_pow,mul_one] at hc
  exact (hp.trans hc).trans (Nat.pow_le_pow_right (by omega)
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hA K)))

#print axioms remove_K_from_power
#print axioms prefix_polynomial_bound
end CurrentAdditive.V40IterationBaseChange
