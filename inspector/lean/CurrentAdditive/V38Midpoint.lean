import CurrentAdditive.V38Public

/-!
# V38 rational threshold arithmetic

Source: `papers/randomized-additive-hardness/versions/v38/source/sections/alternation.tex`,
proof of `yao:main,yao:bpp` (lines 354--370). This is the arithmetic adapter
for the all-signed-binary-rational comparator. It does not itself implement
the estimator repetition, physical source reduction, or output-code machine.
-/

namespace CurrentAdditive.SmallBias

/-- The public midpoint is a binary rational with one fractional bit. -/
def v38MidpointNumerator (B k : ℕ) : ℕ := 2 * B + k

theorem v38MidpointNumerator_value (B k : ℕ) :
    ((v38MidpointNumerator B k : ℕ) : ℝ) / 2 =
      (B : ℝ) + (k : ℝ) / 2 := by
  simp [v38MidpointNumerator]
  ring

/-- One additive-`u` estimate of any comparison-model cost, whose distance
from Alice-first public-output cost is at most two, lands below the public
midpoint on a YES table. -/
theorem v38Midpoint_yes (B k : ℕ) (u C D estimate : ℝ)
    (hgap : 2 * (u + 2) < (k : ℝ))
    (hDA : D ≤ B) (hmodel : |C - D| ≤ 2)
    (hestimate : |estimate - C| ≤ u) :
    estimate < ((v38MidpointNumerator B k : ℕ) : ℝ) / 2 := by
  rw [v38MidpointNumerator_value]
  have hm := (abs_le.mp hmodel).2
  have he := (abs_le.mp hestimate).2
  linarith

/-- The same fixed public threshold lies below an accurate estimate on a
NO table. Repeating independent threshold comparisons and taking a majority
may be used by the endpoint, but is outside this arithmetic declaration. -/
theorem v38Midpoint_no (B k : ℕ) (u C D estimate : ℝ)
    (hgap : 2 * (u + 2) < (k : ℝ))
    (hDA : (B : ℝ) + (k : ℝ) ≤ D)
    (hmodel : |C - D| ≤ 2)
    (hestimate : |estimate - C| ≤ u) :
    ((v38MidpointNumerator B k : ℕ) : ℝ) / 2 < estimate := by
  rw [v38MidpointNumerator_value]
  have hm := (abs_le.mp hmodel).1
  have he := (abs_le.mp hestimate).1
  linarith

#print axioms CurrentAdditive.SmallBias.v38MidpointNumerator_value
#print axioms CurrentAdditive.SmallBias.v38Midpoint_yes
#print axioms CurrentAdditive.SmallBias.v38Midpoint_no

end CurrentAdditive.SmallBias
