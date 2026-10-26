import CurrentAdditive.QuarticTMBaseCaps

namespace Paper2.CurrentAdditive.QuarticTMClockRepair

theorem power_identity (N B k : ℕ) :
    ((N ^ B) ^ (266 * (k + 1))) ^ 8 =
      N ^ ((B * 2128) * (k + 1)) := by
  rw [← pow_mul, ← pow_mul]
  congr 1
  ring

#print axioms power_identity

end Paper2.CurrentAdditive.QuarticTMClockRepair
