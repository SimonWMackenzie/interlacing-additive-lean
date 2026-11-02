import Paper2.ProjectionDefect
import Paper2.DefectLogMargin
import EthBridge.Main

/-!
# The actual interlacing defect induction

Frozen v12 Appendix A, `cl:defect-induction` (lines 313--476).
The frozen `EthBridge.theorem_one` and `EthBridge.one_bit_down` prove
the two concrete first-bit inductions. Their inputs are a one-copy
near-full lower bound and a two-copy three-rung lower bound; both are
derived here from the manuscript's hypotheses, with no assumed child
lower bounds or induction certificate.

Their logarithms are natural. The change of units is `lambda=delta*log 2`.
For the one-bit-down state their allowance `(1+6/(5p))*log 2` is larger
than the manuscript's `(1+1/p)*log 2`. We therefore use a checked stronger
numeric margin when instantiating the inherited induction. The exact
base communication cost is never assumed to equal the parameter `C`.
-/

namespace Paper2.DefectInduction

open Workspace.Types.CommComplexity Workspace.Types.Interlace

variable {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

/-- The profile supplies the entire two-copy bundle used by the first-bit
induction, not merely its top complexity rung. -/
theorem two_copy_input (F : X → Y → Bool) (C : ℕ) (hC : 3 ≤ C)
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 4)
    (hprofile : RestrictionProfile F (FiniteLaw.uniform X) (FiniteLaw.uniform Y)
      θ ((C : ℤ) - 1)) :
    EthBridge.TwoCopyBundle F C θ (3 / 5) := by
  have hp : RestrictionProfile F (FiniteLaw.uniform X) (FiniteLaw.uniform Y)
      θ ((C - 1 : ℕ) : ℤ) := by
    simpa only [Nat.cast_sub (by omega : 1 ≤ C), Nat.cast_one] using hprofile
  have hb := ClassicalCapacities.profile_lambda F (C - 1) θ (by linarith) hp
  have ht := ClassicalRows.two_copy F (C - 1) (by omega) hθ (by linarith)
    (by norm_num : (0 : ℝ) < 3 / 5) (by norm_num) hb
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ C)] using ht

omit [Nonempty Y] in
/-- Conversion between the paper's base-two defect and the natural-log
defect used by the frozen first-bit induction. Column nonemptiness is
imposed when this algebraic identity is used as a state condition. -/
theorem natural_defect_bound (p : ℕ) (K : Finset (Fin p → Y)) (v : ℝ)
    (hdef : ProjectionDefect.defect (ProjectionDefect.columnDensity p K) ≤ v) :
    EthBridge.colDefect Y p K ≤ v * Real.log 2 := by
  rw [ProjectionDefect.defect_columnDensity, Real.logb] at hdef
  exact (div_le_iff₀ (Real.log_pos (by norm_num))).mp hdef

/-- The main (`e=0`) state, with the full copied matrix and retained input
sets visible. The doubled power guard includes the `a=0,p=1` endpoint. -/
theorem main_state (F : X → Y → Bool) (C p a : ℕ) (θ δ : ℝ)
    (hC : 3 ≤ C) (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 4) (hδ : 0 < δ)
    (hp : 2 ^ a < 2 * p) (hscale : (2 : ℝ) ^ a * θ ≤ 1)
    (hmargin : 3 * (δ * Real.log 2) + (7 / 5) * Real.log 2 ≤ -2 * Real.log (3 / 5))
    (hnear : EthBridge.NearFull F C θ (δ * Real.log 2))
    (hprofile : RestrictionProfile F (FiniteLaw.uniform X) (FiniteLaw.uniform Y)
      θ ((C : ℤ) - 1))
    (R : Finset (Fin p × X)) (K : Finset (Fin p → Y)) (hK : K.Nonempty)
    (hR : NPCC.IsEquipartitionedGE R Finset.univ
      ⌈(Fintype.card X : ℝ) * (2 : ℝ) ^ a * θ⌉₊)
    (hdef : ProjectionDefect.defect (ProjectionDefect.columnDensity p K) ≤
      ((p : ℝ) - (2 : ℝ) ^ ((a : ℤ) - 1)) * δ) :
    C + a ≤ D (NPCC.subgame (fullInterlace F p) R K) := by
  have hc := natural_defect_bound p K _ hdef
  have hcn : EthBridge.colDefect Y p K ≤ EthBridge.cExcess a p * (δ * Real.log 2) := by
    simpa only [EthBridge.cExcess, mul_assoc] using hc
  exact EthBridge.theorem_one F C p a θ (3 / 5) (δ * Real.log 2)
    hp hscale hθ hθ1 (by norm_num) (by norm_num)
    (mul_pos hδ (Real.log_pos (by norm_num)))
    Fintype.card_pos Fintype.card_pos hC hmargin hnear
    (two_copy_input F C hC θ hθ hθ1 hprofile) (R, K)
    ⟨hR, (EthBridge.state_defect_iff_density Y p K _ hK.card_pos Fintype.card_pos).mp hcn⟩

/-- The flag-one state is a subset of the inherited one-bit-down states.
Its slightly larger internal allowance is used only inside the proof. -/
theorem one_bit_state (F : X → Y → Bool) (C p a : ℕ) (θ δ : ℝ)
    (hC : 3 ≤ C) (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 4) (hδ : 0 < δ)
    (ha : 2 ≤ a) (hp : 2 ^ a < 2 * p)
    (hmargin : 3 * (δ * Real.log 2) + (7 / 5) * Real.log 2 ≤ -2 * Real.log (3 / 5))
    (hprofile : RestrictionProfile F (FiniteLaw.uniform X) (FiniteLaw.uniform Y)
      θ ((C : ℤ) - 1))
    (R : Finset (Fin p × X)) (K : Finset (Fin p → Y)) (hK : K.Nonempty)
    (hR : NPCC.IsEquipartitionedGE R Finset.univ
      ⌈(Fintype.card X : ℝ) * (2 : ℝ) ^ a * θ⌉₊)
    (hdef : ProjectionDefect.defect (ProjectionDefect.columnDensity p K) ≤
      ((p : ℝ) - (2 : ℝ) ^ ((a : ℤ) - 1)) * δ + 1 + 1 / (p : ℝ)) :
    C + a - 1 ≤ D (NPCC.subgame (fullInterlace F p) R K) := by
  have hp0 : 0 < p := by
    by_contra hh
    have : p = 0 := by omega
    simp [this] at hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hp' : 2 ^ (a - 1) < p := by
    have he : 2 ^ a = 2 * 2 ^ (a - 1) := by
      conv_lhs => rw [show a = (a - 1) + 1 by omega]
      rw [pow_succ']
    omega
  have hb : 1 / (p : ℝ) ≤ 6 / (5 * (p : ℝ)) := by
    apply (div_le_div_iff₀ hpR (by positivity)).mpr
    nlinarith
  have hc := natural_defect_bound p K _ hdef
  have hcn : EthBridge.colDefect Y p K ≤
      EthBridge.cExcess a p * (δ * Real.log 2) + EthBridge.Bdef p := by
    have hh := mul_le_mul_of_nonneg_right hb
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    dsimp only [EthBridge.cExcess, EthBridge.Bdef]
    nlinarith
  have hout := EthBridge.one_bit_down F C p a θ (3 / 5) (δ * Real.log 2)
    ha hp' hθ hθ1 (by norm_num) (by norm_num)
    (mul_pos hδ (Real.log_pos (by norm_num)))
    Fintype.card_pos Fintype.card_pos hC hmargin
    (two_copy_input F C hC θ hθ hθ1 hprofile) (R, K)
    ⟨hR, (EthBridge.state_defect_iff_density Y p K _ hK.card_pos Fintype.card_pos).mp hcn⟩
  change C + (a - 1) ≤ D (NPCC.subgame (fullInterlace F p) R K) at hout
  omega

omit [Nonempty Y] in
/-- The original near-full column threshold implies the natural-density
input required by the inherited induction. -/
theorem near_full_input (F : X → Y → Bool) (C : ℕ) (θ δ : ℝ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 4) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 64)
    (hnear : C ≤ ClassicalRows.restrictionCost F 1 θ (1 - δ)) :
    EthBridge.NearFull F C θ (δ * Real.log 2) := by
  exact hnear.trans (ClassicalRows.restrictionCost_mono F 1 1 θ θ (1 - δ)
    (Real.exp (-(δ * Real.log 2))) (by omega) le_rfl hθ le_rfl (by linarith)
    (by linarith) (DefectLogMargin.one_sub_le_exp_neg_mul_log_two hδ.le)
    (Real.exp_le_one_iff.mpr (by
      have := mul_pos hδ (Real.log_pos (by norm_num : (1 : ℝ) < 2))
      linarith)))

/-- Frozen v12 `cl:defect-induction` on uniform finite indexed carriers.
The doubled guard is exactly `p > 2^(a-1)`, including the half-integer
cutoff at `a=0`. The flag is a natural number bounded by one, and natural
subtraction in the conclusion is harmless because `2*e <= a`.

All matrix/protocol inputs to the inherited inductions are discharged by
the displayed manuscript assumptions. No child-state or successful-projection
contract remains as a hypothesis. -/
theorem defect_induction (F : X → Y → Bool) (C p a e : ℕ) (θ δ : ℝ)
    (hC : 3 ≤ C) (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 4)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 64)
    (he : e ≤ 1) (ha : 2 * e ≤ a)
    (hp : 2 ^ a < 2 * p) (hscale : (2 : ℝ) ^ a * θ ≤ 1)
    (hnear : C ≤ ClassicalRows.restrictionCost F 1 θ (1 - δ))
    (hprofile : RestrictionProfile F (FiniteLaw.uniform X) (FiniteLaw.uniform Y)
      θ ((C : ℤ) - 1))
    (R : Finset (Fin p × X)) (K : Finset (Fin p → Y)) (hK : K.Nonempty)
    (hR : NPCC.IsEquipartitionedGE R Finset.univ
      ⌈(Fintype.card X : ℝ) * (2 : ℝ) ^ a * θ⌉₊)
    (hdef : ProjectionDefect.defect (ProjectionDefect.columnDensity p K) ≤
      ((p : ℝ) - (2 : ℝ) ^ ((a : ℤ) - 1)) * δ +
        (e : ℝ) * (1 + 1 / (p : ℝ))) :
    C + a - e ≤ D (NPCC.subgame (fullInterlace F p) R K) := by
  have hm := DefectLogMargin.natural_log_margin hδ1
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he with rfl | rfl
  · simp only [Nat.cast_zero, zero_mul, add_zero] at hdef
    exact main_state F C p a θ δ hC hθ hθ1 hδ hp hscale hm
      (near_full_input F C θ δ hθ hθ1 hδ hδ1 hnear) hprofile R K hK hR hdef
  · simp only [Nat.cast_one, one_mul] at hdef
    exact one_bit_state F C p a θ δ hC hθ hθ1 hδ (by omega) hp hm
      hprofile R K hK hR (by simpa only [add_assoc] using hdef)

end Paper2.DefectInduction
