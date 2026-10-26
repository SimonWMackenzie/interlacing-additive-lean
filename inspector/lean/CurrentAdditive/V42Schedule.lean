import CurrentAdditive.V39GeneralExceptionBudget
import CurrentAdditive.V39PublicSchedule
import CurrentAdditive.V39FullCutoff

/-! Literal unified recipe of the author's replacement v42, source
`main.tex`, def:amplification-parameters and Appendix sec:parameters.
The exponents k,b mean s=2^k and rho=2^-b. No validity assertion is
included in the recipe. -/

namespace CurrentAdditive.V42Schedule

def s (k : ℕ) : ℕ := 2^k
def q₁ (k : ℕ) : ℕ := s k-2
def q₂ (k b : ℕ) : ℕ := 2^(b+2*k)
def w (k : ℕ) : ℕ := 2^(8*k)
def Q (k : ℕ) : ℕ := 2^(24*k)
def rho (b : ℕ) : ℚ := 1/2^b
def x (b : ℕ) : ℚ := 1/2^(8*b)
def eta (k : ℕ) : ℚ := 1/2^(2*k)
def theta (k : ℕ) : ℚ := 1/2^(9+24*k)
def deltaU (k : ℕ) : ℚ := 1/2^(4+10*k)

theorem s_pos (k : ℕ) : 0 < s k := by unfold s; positivity
theorem q₂_pos (k b : ℕ) : 0 < q₂ k b := by unfold q₂; positivity
theorem w_pos (k : ℕ) : 0 < w k := by unfold w; positivity
theorem Q_pos (k : ℕ) : 0 < Q k := by unfold Q; positivity

theorem recipe_exact (k b : ℕ) :
    (q₂ k b : ℚ) = (s k : ℚ)^2 / rho b ∧
    w k = (s k)^8 ∧ Q k = (s k)^24 ∧
    x b = (rho b)^8 ∧ eta k = 1/(s k : ℚ)^2 ∧
    theta k = 1/(512*(Q k : ℚ)) ∧
    deltaU k = eta k/(16*(w k : ℚ)) := by
  have hp (a c : ℕ) : (2 : ℚ)^(a*c) = ((2:ℚ)^a)^c := pow_mul 2 a c
  simp only [q₂,s,w,Q,rho,x,eta,theta,deltaU,Nat.cast_pow,Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pow_add, mul_comm 2 k, hp]
    field_simp
  · rw [← pow_mul]; congr 1; omega
  · rw [← pow_mul]; congr 1; omega
  · rw [mul_comm 8 b, hp]; ring
  · rw [mul_comm 2 k, hp]
  · rw [pow_add]; norm_num
  · rw [show 4+10*k=4+2*k+8*k by omega,pow_add,pow_add]
    norm_num
    ring

theorem ratio_le (a b c d : ℕ) (h : a+d ≤ c+b) :
    (2:ℚ)^a/2^b ≤ 2^c/2^d := V39FullCutoff.two_ratio_le a b c d h

theorem reciprocal_le (a b : ℕ) (h : b ≤ a) :
    (1:ℚ)/2^a ≤ 1/2^b := by simpa using ratio_le 0 a 0 b (by omega)

theorem w_deltaU (k : ℕ) : (w k : ℚ)*deltaU k=eta k/16 := by
  rw [(recipe_exact k 0).2.2.2.2.2.2]
  have hw : (w k : ℚ) ≠ 0 := by exact_mod_cast (w_pos k).ne'
  field_simp

theorem Q_theta (k : ℕ) : (Q k : ℚ)*theta k=1/512 := by
  rw [(recipe_exact k 0).2.2.2.2.2.1]
  have hQ : (Q k : ℚ) ≠ 0 := by exact_mod_cast (Q_pos k).ne'
  field_simp

theorem Q_deltaU (k : ℕ) : (Q k : ℚ)*deltaU k=(2:ℚ)^(14*k)/16 := by
  simp only [Q,deltaU,Nat.cast_pow,Nat.cast_ofNat]
  rw [show 24*k=14*k+10*k by omega,pow_add,pow_add]
  norm_num
  field_simp

theorem ebar_dyadic (b t : ℕ) :
    V38Schedule.ebar b ((1:ℚ)/2^t)=2^(90+2*t+(b+63)/64) := by
  unfold V38Schedule.ebar
  have he : (2^90:ℚ)/((1:ℚ)/2^t)^2*(2^((b+63)/64):ℚ)=
      ((2^(90+2*t+(b+63)/64):ℕ):ℚ) := by
    push_cast
    rw [pow_add,pow_add,show 2*t=t*2 by omega,pow_mul]
    field_simp
  rw [he]
  exact Nat.ceil_natCast _

end CurrentAdditive.V42Schedule
