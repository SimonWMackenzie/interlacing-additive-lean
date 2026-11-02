import CurrentAdditive.V40RandomizedETHArithmetic
import Paper2.ETape
import Paper2.A4PolyIn

/-! A scalar closure lemma for the exact prefix-cut runtime. Its argument is
an ordinary numerical polynomial, not a promised execution or supplied clock. -/
namespace CurrentAdditive.V40RandomizedETHEndpoint
noncomputable section
open Paper2
set_option maxHeartbeats 200000
set_option maxRecDepth 8192

theorem polynomial_of_source_prefix_subexponential (f : ℕ → ℕ)
    (hf : Unit4Shell.Poly.PolyIn id f) (A : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ K d N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ m, N ≤ m →
      f (A*(m+AEth.expLen N+1)) ≤
        K*⌈(2:ℝ)^(ε*N)⌉₊*(m+1)^d := by
  obtain ⟨c,d,hf⟩ := hf
  have hsub : AEth.Subexp (fun N => (AEth.expLen N+1)^d) := by
    apply AEth2.subexp_poly_comp 1 d AEth.expLen_subexp
    intro N
    simpa only [Nat.one_mul] using
      (Nat.pow_le_pow_left (show AEth.expLen N+1≤N+AEth.expLen N+1 by omega) d)
  obtain ⟨c₁,e,N₀,h₁⟩ := hsub ε hε
  refine ⟨c*(A+1)^d*c₁,d+e,N₀,?_⟩
  intro N hN m hNm
  have hr : (AEth.expLen N+1)^d ≤ c₁*⌈(2:ℝ)^(ε*N)⌉₊*(m+1)^e :=
    (h₁ N hN).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) e))
  have hbase : A*(m+AEth.expLen N+1)+1 ≤
      (A+1)*(m+1)*(AEth.expLen N+1) := by
    have hb : m+AEth.expLen N+1 ≤ (m+1)*(AEth.expLen N+1) := by nlinarith
    have hz : 1 ≤ (m+1)*(AEth.expLen N+1) := Nat.mul_pos (by omega) (by omega)
    calc
      _ ≤ A*((m+1)*(AEth.expLen N+1))+1 := Nat.add_le_add_right (Nat.mul_le_mul_left _ hb) _
      _ ≤ A*((m+1)*(AEth.expLen N+1))+(m+1)*(AEth.expLen N+1) := Nat.add_le_add_left hz _
      _ = _ := by ring
  calc
    _ ≤ c*(A*(m+AEth.expLen N+1)+1)^d := hf _
    _ ≤ c*((A+1)*(m+1)*(AEth.expLen N+1))^d :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase _)
    _ = (c*(A+1)^d*(m+1)^d)*(AEth.expLen N+1)^d := by simp only [mul_pow]; ac_rfl
    _ ≤ (c*(A+1)^d*(m+1)^d)*(c₁*⌈(2:ℝ)^(ε*N)⌉₊*(m+1)^e) :=
      Nat.mul_le_mul_left _ hr
    _ = _ := by rw [pow_add]; ac_rfl

#print axioms polynomial_of_source_prefix_subexponential
end
end CurrentAdditive.V40RandomizedETHEndpoint
