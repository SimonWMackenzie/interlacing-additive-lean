import EthInapproximability.CurrentPaper.Construction
import EthInapproximability.CurrentPaper.ExactCoordinateControl
import EthInapproximability.CurrentPaper.ExactResidualIndexing
import EthInapproximability.CurrentPaper.ParameterGates
import EthInapproximability.CurrentPaper.AmplificationFirstProfiles
import EthInapproximability.CurrentPaper.AmplificationSecondGates

/-!
# Inner profiles of the amplification construction

Source: locked v8 `03-parameterized-construction.tex`,
`eq:paper-M2-aux-robust` and the proof of `lem:paper-scaffold`.
The matrices here are the actual `Construction.secondMatrix`, using the
same indexed family for every supplied density. The source for its stopping
argument is the transpose of the actual full first matrix.
-/

namespace EthInapproximability.CurrentPaper.AmplificationInnerProfiles

open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace
open Construction ExactCoordinateControl ExactResidualIndexing

universe u
variable {X Y : Type u} [Fintype X] [Fintype Y]

/-- The actual second matrix, with its two players interchanged. -/
def secondTranspose (f : X → Y → Bool) (a s q L : ℕ)
    (family : SecondFamily a q L X) : Fin L → SecondRows a s q Y → Bool :=
  fun j r => secondMatrix f a s q L family r j

/-- The literal selector protocol first announces the graph coordinate. -/
theorem secondMatrix_upper (f : X → Y → Bool) {a s q L k : ℕ}
    (family : SecondFamily a q L X) (hwidth : q = 2 ^ k) :
    D (secondMatrix f a s q L family) ≤ D (firstMatrix f a s) + k := by
  subst q
  apply (show D (secondMatrix f a s (2 ^ k) L family) ≤ k + D (firstMatrix f a s) from ?_).trans
    (by omega)
  apply comp_le_partition _ k (D (firstMatrix f a s)) Prod.fst
  intro α
  have hm := D_mapNodes_le (fun c r => firstMatrix f a s r c)
    (fun r : {r : SecondRows a s (2 ^ k) Y // r.1 = α} => r.val.2)
    (fun j : Fin L => family j α)
  have hcost : D (fun c r => firstMatrix f a s r c) = D (firstMatrix f a s) :=
    comp_transpose (firstMatrix f a s)
  rw [hcost] at hm
  convert hm using 1
  congr 1
  funext r j
  simp only [secondMatrix, r.property]

section Profiles

variable [Nonempty X] [Nonempty Y] [DecidableEq X]
    (f : X → Y → Bool) {a s q L H m R : ℕ} {x h ε : ℝ}
    (ha : 2 ≤ a) (family : SecondFamily a q L X)
    (hwidth : q = 2 ^ R * 2 ^ m)
    (hH : 2 ≤ H) (hm : 2 ^ 20 ≤ m) (hx : 0 < x)
    (hrow : (2 : ℝ) ^ m * x ≤ 1) (hε : 0 ≤ ε) (hh : 0 < h)
    (h1 : H ≤ Dfamily (interlaceFun (fun c r => firstMatrix f a s r c) 1)
      (bracketGE (FirstColumns a s Y) (FirstRows a X) 1 x (3 / 5)))
    (h2 : H - 1 ≤ Dfamily (interlaceFun (fun c r => firstMatrix f a s r c) 1)
      (bracketGE (FirstColumns a s Y) (FirstRows a X) 1 x (3 / 10)))
    (hS : IsBalancedFamily (2 ^ m) family ε)
    (hgateOne : (3 / 5 : ℝ) ≤ yLoss ε (2 ^ m) h (H + (R + m)))
    (hgateSeed : HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
      h * (2 : ℝ) ^ (-((H + m : ℕ) : ℝ)) / (1 + ε))

include ha hwidth hH hm hx hrow hε hh h1 h2 hS hgateOne hgateSeed

/-- A restriction of the literal second transpose has the cost furnished
by localized stopping after selecting actual populated coordinate blocks. -/
theorem secondTranspose_subgame_lower {β : ℝ}
    (R' : ℕ) (hR' : R' ≤ R)
    (hsmall : (2 : ℝ) ^ (R' + m) * x < 1)
    (hcount : 2 ^ R' * HardSeed.copyCount m ≤
      ⌈(q : ℝ) * (β - (2 : ℝ) ^ (R' + m) * x) /
        (1 - (2 : ℝ) ^ (R' + m) * x)⌉₊)
    (J : Finset (Fin L)) (I : Finset (SecondRows a s q Y))
    (hJ : (L : ℝ) * h ≤ J.card)
    (hI : ((q : ℝ) * Fintype.card (FirstColumns a s Y)) * β ≤ I.card) :
    H + (R' + m) ≤ D (subgame (secondTranspose f a s q L family) J I) := by
  classical
  have hqone : 0 < qOne a := by
    have hp := Nat.pow_le_pow_right (by norm_num : 0 < 2) ha
    norm_num at hp
    unfold qOne
    omega
  letI : NeZero (qOne a) := ⟨by omega⟩
  have hq : 0 < q := by rw [hwidth]; positivity
  have hv : 1 ≤ 2 ^ R' * HardSeed.copyCount m := by
    have hp := (HardSeed.copyCount_bounds (show 5 ≤ m by omega)).1
    have hpos : 0 < HardSeed.copyCount m := by omega
    exact Nat.succ_le_iff.mpr (Nat.mul_pos (by positivity) hpos)
  have hblock := coordinateBlockLowerBound_of_width (z := h)
    (fun c r => firstMatrix f a s r c) hwidth hH hm hx hrow hε hh h1 h2
    ((by omega : 1 ≤ H).trans h1) family hS hgateOne hgateSeed
    0 R' (2 ^ R' * HardSeed.copyCount m)
    ⌈(2 : ℝ) ^ (R' + m) * x * (Fintype.card (FirstColumns a s Y) : ℝ)⌉₊
    (by omega) hR' (le_refl _) (le_refl _) (by simp)
  have hbound := lowerBound_of_denseRows (secondMatrix f a s q L family) Finset.univ
    hq (by positivity : 0 < (2 : ℝ) ^ (R' + m) * x) hsmall hv
    (by ring_nf; exact le_refl _)
    hcount hblock I J (by simpa only [mul_comm, mul_left_comm, mul_assoc] using hI)
    (Finset.subset_univ _) (by simpa [mul_comm] using hJ)
  have htranspose : D (subgame (secondTranspose f a s q L family) J I) =
      D (subgame (secondMatrix f a s q L family) I J) :=
    comp_transpose (subgame (secondMatrix f a s q L family) I J)
  rw [htranspose]
  exact hbound

/-- The actual restriction estimate in the one-copy profile interface. -/
theorem secondTranspose_oneCopy_lower {β : ℝ}
    (hh1 : h ≤ 1) (hβ1 : β ≤ 1)
    (R' : ℕ) (hR' : R' ≤ R)
    (hsmall : (2 : ℝ) ^ (R' + m) * x < 1)
    (hcount : 2 ^ R' * HardSeed.copyCount m ≤
      ⌈(q : ℝ) * (β - (2 : ℝ) ^ (R' + m) * x) /
        (1 - (2 : ℝ) ^ (R' + m) * x)⌉₊) :
    H + (R' + m) ≤ Dfamily (interlaceFun (secondTranspose f a s q L family) 1)
      (bracketGE (Fin L) (SecondRows a s q Y) 1 h β) := by
  have hL : 0 < L := hS.1
  letI : NeZero L := ⟨by omega⟩
  apply oneCopy_family_lower_of_subgame (secondTranspose f a s q L family) hh1 hβ1
  intro J I hJ hI
  exact secondTranspose_subgame_lower f ha family hwidth hH hm hx hrow hε hh
    h1 h2 hS hgateOne hgateSeed R' hR' hsmall hcount J I
    (by simpa using hJ)
    (by simpa only [SecondRows, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] using hI)

/-- Both second-matrix profiles at one retained row density. Applying this
twice uses the identical family at depths `b₂` and `bT`. -/
theorem secondTranspose_profiles (hR : 1 ≤ R) (hh1 : h ≤ 1)
    (hsmall : (2 : ℝ) ^ (R + m) * x < 1)
    (hfull : 2 ^ R * HardSeed.copyCount m ≤
      ⌈(q : ℝ) * ((3 / 5 : ℝ) - (2 : ℝ) ^ (R + m) * x) /
        (1 - (2 : ℝ) ^ (R + m) * x)⌉₊)
    (hhalf : 2 ^ (R - 1) * HardSeed.copyCount m ≤
      ⌈(q : ℝ) * ((3 / 10 : ℝ) - (2 : ℝ) ^ (R - 1 + m) * x) /
        (1 - (2 : ℝ) ^ (R - 1 + m) * x)⌉₊) :
    H + (R + m) ≤ Dfamily (interlaceFun (secondTranspose f a s q L family) 1)
      (bracketGE (Fin L) (SecondRows a s q Y) 1 h (3 / 5)) ∧
    H + (R + m) - 1 ≤ Dfamily (interlaceFun (secondTranspose f a s q L family) 1)
      (bracketGE (Fin L) (SecondRows a s q Y) 1 h (3 / 10)) := by
  have hsmallHalf : (2 : ℝ) ^ (R - 1 + m) * x < 1 :=
    (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)) hx.le).trans_lt hsmall
  constructor
  · exact secondTranspose_oneCopy_lower f ha family hwidth hH hm hx hrow hε hh
      h1 h2 hS hgateOne hgateSeed hh1 (by norm_num) R (le_refl _) hsmall hfull
  · have hh := secondTranspose_oneCopy_lower f ha family hwidth hH hm hx hrow hε hh
      h1 h2 hS hgateOne hgateSeed hh1 (by norm_num : (3 / 10 : ℝ) ≤ 1)
      (R - 1) (Nat.sub_le R 1) hsmallHalf hhalf
    have heq : H + (R - 1 + m) = H + (R + m) - 1 := by omega
    rwa [heq] at hh

/-- Exact cost follows from the full profile and the literal selector
protocol once the first-matrix cost has been established. -/
theorem secondMatrix_cost (hfirst : D (firstMatrix f a s) = H) (hh1 : h ≤ 1)
    (hsmall : (2 : ℝ) ^ (R + m) * x < 1)
    (hfull : 2 ^ R * HardSeed.copyCount m ≤
      ⌈(q : ℝ) * ((3 / 5 : ℝ) - (2 : ℝ) ^ (R + m) * x) /
        (1 - (2 : ℝ) ^ (R + m) * x)⌉₊) :
    D (secondMatrix f a s q L family) = H + (R + m) ∧
      D (secondTranspose f a s q L family) = H + (R + m) := by
  classical
  have hsub := secondTranspose_subgame_lower f ha family hwidth hH hm hx hrow hε hh
    h1 h2 hS hgateOne hgateSeed R (le_refl _) hsmall hfull Finset.univ Finset.univ
    (by simpa using mul_le_of_le_one_right (Nat.cast_nonneg L) hh1)
    (by
      simp only [SecondRows, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
      nlinarith [mul_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
        (Nat.cast_nonneg (Fintype.card (FirstColumns a s Y)) :
          (0 : ℝ) ≤ Fintype.card (FirstColumns a s Y))])
  have hlower := hsub.trans (D_mapNodes_le (secondTranspose f a s q L family)
    (fun j : ↥(Finset.univ : Finset (Fin L)) => j.val)
    (fun r : ↥(Finset.univ : Finset (SecondRows a s q Y)) => r.val))
  have htranspose : D (secondTranspose f a s q L family) =
      D (secondMatrix f a s q L family) := comp_transpose (secondMatrix f a s q L family)
  rw [htranspose] at hlower
  have hupper := secondMatrix_upper (s := s) f family (show q = 2 ^ (R + m) by
    simpa only [pow_add] using hwidth)
  rw [hfirst] at hupper
  exact ⟨le_antisymm hupper hlower, htranspose.trans (le_antisymm hupper hlower)⟩

/-- The actual second transpose is robust at the requested depth, from
the first transpose's two profiles and the scalar stopping gates. -/
theorem second_robustAt (hfirst : D (firstMatrix f a s) = H)
    (b : ℕ) (hb : 1 ≤ b) (hhEq : h = (2 : ℝ) ^ (-(b : ℝ)))
    (hR : 1 ≤ R) (hh1 : h ≤ 1)
    (hsmall : (2 : ℝ) ^ (R + m) * x < 1)
    (hfull : 2 ^ R * HardSeed.copyCount m ≤
      ⌈(q : ℝ) * ((3 / 5 : ℝ) - (2 : ℝ) ^ (R + m) * x) /
        (1 - (2 : ℝ) ^ (R + m) * x)⌉₊)
    (hhalf : 2 ^ (R - 1) * HardSeed.copyCount m ≤
      ⌈(q : ℝ) * ((3 / 10 : ℝ) - (2 : ℝ) ^ (R - 1 + m) * x) /
        (1 - (2 : ℝ) ^ (R - 1 + m) * x)⌉₊) :
    IsRobustAt (secondTranspose f a s q L family) b := by
  have hcost := (secondMatrix_cost f ha family hwidth hH hm hx hrow hε hh
    h1 h2 hS hgateOne hgateSeed hfirst hh1 hsmall hfull).2
  have hp := secondTranspose_profiles f ha family hwidth hH hm hx hrow hε hh
    h1 h2 hS hgateOne hgateSeed hR hh1 hsmall hfull hhalf
  unfold IsRobustAt
  rw [hcost, ← hhEq]
  exact ⟨hb, by omega, hp⟩

end Profiles

/-- The one prime-polynomial family used at every requested density. -/
def scheduledFamily (i : Parameters.Input) (ha : Parameters.Accepted i) :
    SecondFamily (Parameters.firstExponent i) (Parameters.secondWidth i)
      (PrimeSampler.size (Parameters.secondWidth i) (Parameters.balanceOrder i)
        (Parameters.firstWidth i * i.rows)) (Fin i.rows) :=
  PrimeSampler.secondFamily (Parameters.firstExponent i) (Parameters.secondWidth i)
    (Parameters.balanceOrder i) (Parameters.firstWidth i * i.rows)
    (lt_of_lt_of_le (by decide : 0 < 2) (ParameterGates.samplerAlphabet_ge_two i ha.1))
    (PrimeSampler.canonicalFirstRowsEquiv (Parameters.firstExponent i) i.rows)

/-- The literal sampled second transpose at all printed parameter values. -/
def scheduledSecond (i : Parameters.Input) (ha : Parameters.Accepted i)
    (f : Fin i.rows → Fin i.columns → Bool) :=
  secondTranspose f (Parameters.firstExponent i) (Parameters.bins i)
    (Parameters.secondWidth i)
    (PrimeSampler.size (Parameters.secondWidth i) (Parameters.balanceOrder i)
      (Parameters.firstWidth i * i.rows)) (scheduledFamily i ha)

/-- The literal second transpose has the asserted exact cost and is robust
at every positive depth up to the larger of the two printed depths. There
is no matrix-profile premise besides robustness of the source matrix. -/
theorem scheduled_second_profile (i : Parameters.Input)
    (hc : 0 < i.sourceConstant) (ha : Parameters.Accepted i)
    (f : Fin i.rows → Fin i.columns → Bool)
    (hf : IsRobustAt f i.incomingDepth) (hcost : D f = i.cost)
    (b : ℕ) (hb : 1 ≤ b)
    (hbmax : b ≤ max (Parameters.secondDepth i) (Parameters.tailDepth i)) :
    D (scheduledSecond i ha f) =
        i.cost + Parameters.firstExponent i + Parameters.secondExponent i ∧
      IsRobustAt (scheduledSecond i ha f) b := by
  classical
  letI : NeZero i.rows := ⟨by have := ha.1; omega⟩
  letI : NeZero i.columns := ⟨by have := ha.2.1; omega⟩
  let a := Parameters.firstExponent i
  let m := Parameters.balanceExponent i
  let R := Parameters.secondExponent i - m
  let x := (2 : ℝ) ^ (-(Parameters.firstDepth i : ℝ))
  let h := (2 : ℝ) ^ (-(b : ℝ))
  let ε := 1 / (100 * (Parameters.balanceOrder i : ℝ))
  have hp := AmplificationFirstProfiles.scheduled_first_profiles f i ha hf
  rw [hcost] at hp
  obtain ⟨hm, hR, hwidth, hrow, hsmall, hfull, hhalf⟩ :=
    AmplificationSecondGates.scalar_gates i hc ha
  have hmk := AmplificationSecondGates.balanceExponent_add_two_le_second i hc ha
  have hsum : R + m = Parameters.secondExponent i := by dsimp [R, m]; omega
  have ha2 : 2 ≤ a := by
    have := (ParameterGates.hard_seed_exponent_domains i).2.2.1
    dsimp [a]
    omega
  have hH : 2 ≤ i.cost + a := by have := hf.2.1; omega
  have hx : 0 < x := by dsimp [x]; positivity
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hh : 0 < h := by dsimp [h]; positivity
  have hh1 : h ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 2)
    exact neg_nonpos.mpr (Nat.cast_nonneg b)
  have hS : IsBalancedFamily (2 ^ m) (scheduledFamily i ha) ε :=
    ParameterGates.actualSecondFamily_balanced i hc ha
  have hgates := ParameterGates.second_interlace_stopping_gates i b hbmax
  have hg1 : (3 / 5 : ℝ) ≤ yLoss ε (2 ^ m) h (i.cost + a + (R + m)) := by
    simpa only [yLoss, hsum, a, m, h, ε, Parameters.balanceOrder,
      Nat.cast_pow, Nat.cast_ofNat] using hgates.1
  have hg2 : HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
      h * (2 : ℝ) ^ (-((i.cost + a + m : ℕ) : ℝ)) / (1 + ε) := by
    simpa only [a, m, h, ε, Parameters.balanceOrder, Nat.cast_pow, Nat.cast_ofNat]
      using hgates.2
  have hcostSecond := (secondMatrix_cost f ha2 (scheduledFamily i ha) hwidth
    hH hm hx hrow hε hh hp.2.1 hp.2.2 hS hg1 hg2 hp.1 hh1 hsmall hfull).2
  have hrobust := second_robustAt f ha2 (scheduledFamily i ha) hwidth
    hH hm hx hrow hε hh hp.2.1 hp.2.2 hS hg1 hg2 hp.1
    b hb rfl hR hh1 hsmall hfull hhalf
  have hsum' : Parameters.secondExponent i - Parameters.balanceExponent i +
      Parameters.balanceExponent i = Parameters.secondExponent i := hsum
  exact ⟨by simpa only [scheduledSecond, hsum', a] using hcostSecond, hrobust⟩

/-- The same indexed family supplies both depths required by protected
preparation and by reference extraction. -/
theorem scheduled_second_profiles (i : Parameters.Input)
    (hc : 0 < i.sourceConstant) (ha : Parameters.Accepted i)
    (f : Fin i.rows → Fin i.columns → Bool)
    (hf : IsRobustAt f i.incomingDepth) (hcost : D f = i.cost) :
    D (scheduledSecond i ha f) =
        i.cost + Parameters.firstExponent i + Parameters.secondExponent i ∧
      IsRobustAt (scheduledSecond i ha f) (Parameters.secondDepth i) ∧
      IsRobustAt (scheduledSecond i ha f) (Parameters.tailDepth i) := by
  have hsecond := scheduled_second_profile i hc ha f hf hcost (Parameters.secondDepth i)
    (by unfold Parameters.secondDepth; omega) (le_max_left _ _)
  have htail := scheduled_second_profile i hc ha f hf hcost (Parameters.tailDepth i)
    (Nat.one_le_pow _ _ (by norm_num)) (le_max_right _ _)
  exact ⟨hsecond.1, hsecond.2, htail.2⟩

/-- The auxiliary reference-scale bound follows from the same two-profile
robustness, with an explicit scalar column-density comparison. -/
theorem hardSeed_from_robustness [Nonempty X] [Nonempty Y]
    (f : X → Y → Bool) {b k : ℕ} {z : ℝ}
    (hf : IsRobustAt f b) (hk : 2 ^ 20 ≤ k) (hkb : k ≤ b)
    (hz : HardSeed.columnDensity ((2 : ℝ) ^ k) ≤ z) (hz1 : z ≤ 1) :
    D f + k ≤ Dfamily (interlaceFun f (HardSeed.copyCount k))
      (bracketGE X Y (HardSeed.copyCount k)
        ((2 : ℝ) ^ k * (2 : ℝ) ^ (-(b : ℝ))) z) := by
  have hrow : (2 : ℝ) ^ k * (2 : ℝ) ^ (-(b : ℝ)) ≤ 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    calc
      (2 : ℝ) ^ ((k : ℝ) + -(b : ℝ)) ≤ (2 : ℝ) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (by have hkbR : (k : ℝ) ≤ b := by exact_mod_cast hkb
              linarith)
      _ = 1 := Real.rpow_zero _
  have hgamma : (3 / 5 : ℝ) ≤ 1 / Real.sqrt 2 := by
    rw [le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hseed := HardSeed.hardSeed f hf.2.1 hk (by positivity)
    (by norm_num : (0 : ℝ) < 3 / 5) hgamma hf.2.2.1
    (by convert hf.2.2.2 using 1; norm_num) hrow
  have hmono := HardSeed.lambda_mono f
    (HardSeed.copyCount_bounds (show 5 ≤ k by omega)).1 (le_refl _)
    (by positivity : 0 < (2 : ℝ) ^ k * (2 : ℝ) ^ (-(b : ℝ))) hrow
    (HardSeed.columnDensity_pos _) hz hz1
  exact (hseed.trans hmono).trans (min_le_left _ _)

/-- The column gate holds at each of the three reference extraction scales. -/
theorem tail_chi_levels (i : Parameters.Input) (j : ℕ) (hj : j ≤ 2) :
    HardSeed.columnDensity ((2 : ℝ) ^ (Parameters.binExponent i - j)) ≤
      (2 : ℝ) ^ (-(Parameters.tailDepth i : ℝ)) := by
  apply ParameterGates.chi_le_dyadic_of_square
  have hu := Parameters.auxiliaryLog_floor i
  have hb : j ≤ Parameters.binExponent i := by unfold Parameters.binExponent; nlinarith
  have hsub := Nat.sub_add_cancel hb
  change 10000 * (40 * Parameters.auxiliaryLog i) ^ 2 ≤
    2401 * (Parameters.binExponent i - j)
  change (Parameters.binExponent i - j) + j = 10000 * Parameters.auxiliaryLog i ^ 2 at hsub
  nlinarith

/-- The same scheduled matrix supplies the hard-seed profiles at every
reference extraction level `j ≤ 2`. The integer seed counts are expressed
by `copyCount` to avoid rounding ambiguity. -/
theorem scheduled_tail_hardSeed_levels (i : Parameters.Input)
    (hc : 0 < i.sourceConstant) (ha : Parameters.Accepted i)
    (f : Fin i.rows → Fin i.columns → Bool)
    (hf : IsRobustAt f i.incomingDepth) (hcost : D f = i.cost)
    (j : ℕ) (hj : j ≤ 2) :
    D (scheduledSecond i ha f) + (Parameters.binExponent i - j) ≤
      Dfamily (interlaceFun (scheduledSecond i ha f)
        (HardSeed.copyCount (Parameters.binExponent i - j)))
        (bracketGE
          (Fin (PrimeSampler.size (Parameters.secondWidth i) (Parameters.balanceOrder i)
            (Parameters.firstWidth i * i.rows)))
          (SecondRows (Parameters.firstExponent i) (Parameters.bins i)
            (Parameters.secondWidth i) (Fin i.columns))
          (HardSeed.copyCount (Parameters.binExponent i - j))
          ((2 : ℝ) ^ (Parameters.binExponent i - j) *
            (2 : ℝ) ^ (-(Parameters.tailDepth i : ℝ)))
          ((2 : ℝ) ^ (-(Parameters.tailDepth i : ℝ)))) := by
  classical
  have hS := ParameterGates.actualSecondFamily_balanced i hc ha
  letI : NeZero (PrimeSampler.size (Parameters.secondWidth i) (Parameters.balanceOrder i)
      (Parameters.firstWidth i * i.rows)) := ⟨by have := hS.1; omega⟩
  letI : NeZero i.columns := ⟨by have := ha.2.1; omega⟩
  letI : NeZero (Parameters.secondWidth i) := ⟨by
    unfold Parameters.secondWidth
    positivity⟩
  have hh : Parameters.binExponent i - j ≤ Parameters.tailDepth i := by
    have := Parameters.binExponent_lt_tailDepth i
    omega
  exact hardSeed_from_robustness (scheduledSecond i ha f)
    (scheduled_second_profiles i hc ha f hf hcost).2.2
    (by have := (ParameterGates.hard_seed_exponent_domains i).2.2.2; omega) hh
    (tail_chi_levels i j hj)
    (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr (Nat.cast_nonneg _)))

end EthInapproximability.CurrentPaper.AmplificationInnerProfiles
