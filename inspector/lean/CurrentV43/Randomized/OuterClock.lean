import CurrentV43.Randomized.Algorithm
import CurrentV43.Randomized.Clock

namespace CurrentV43.RandomizedRate
noncomputable section
set_option maxHeartbeats 1000000

/-- The fixed cubic finite-exception router and its extra framing are
absorbed into the already paid physical inner clock. -/
theorem add_router_clock_bound (m T inner carrier run R C d F : ℕ)
    (he : inner = carrier+T+4*(m+T+1)+run)
    (hinner : inner ≤ C*(F+1)^d) (hm : m ≤ F) :
    carrier+run+2*(R*(m+1)^3)+14*m+7*T+16 ≤
      (3*C+2*R+22)*(F+1)^(d+3) := by
  have hT : T ≤ inner := by rw [he]; omega
  have hp : (F+1)^d ≤ (F+1)^(d+3) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : (m+1)^3 ≤ (F+1)^(d+3) :=
    (Nat.pow_le_pow_left (by omega) 3).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have h1 : F+1 ≤ (F+1)^(d+3) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 1 ≤ F+1 by omega)
      (show 1 ≤ d+3 by omega)
  have hpos : 1 ≤ (F+1)^(d+3) := Nat.one_le_pow _ _ (by omega)
  have hi := hinner.trans (Nat.mul_le_mul_left C hp)
  have hr := Nat.mul_le_mul_left R h3
  calc
    _ ≤ 3*inner+2*(R*(m+1)^3)+10*m+12 := by omega
    _ ≤ _ := by nlinarith

#print axioms add_router_clock_bound
end
end CurrentV43.RandomizedRate
