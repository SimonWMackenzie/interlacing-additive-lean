import EthInapproximability.CurrentPaper.Iteration
import EthInapproximability.ParameterizedNP.ScheduleCompilerExistential

/-!
# Effective bounds for the literal iteration

Source: locked v8 `F-parameter-choices.tex`, eventual validity and the two
integer tests `eq:paper-tail-graph`; `05-iteration.tex`,
`lem:paper-reader-depth-acceptance` and `thm:paper-effective-level`.

The integer cutoff test below has a concrete terminating witness and persists
at every later index.  Only the general elementary inequalities
`IterationAssembly.sq_le_two_pow` and
`ScheduleCompilerExistential.pow_succ_le_two_mul` are reused from the older
route. No old schedule, cutoff oracle, constructor or endpoint is consumed.
-/

namespace EthInapproximability.CurrentPaper.EffectiveIteration

open Parameters
open EthInapproximability.ParameterizedNP

/-- The degree recurrence in the last subsection of Appendix F. -/
def degree : ℕ → ℕ
  | 0 => 4
  | i + 1 => 8 * degree i + 100

@[simp] theorem degree_zero : degree 0 = 4 := rfl
@[simp] theorem degree_succ (i : ℕ) : degree (i + 1) = 8 * degree i + 100 := rfl

/-- A literal finite arithmetic test, with the degree guard needed for
persistence. Both comparisons can be evaluated on natural numbers. -/
def CutoffTest (A d v : ℕ) : Prop :=
  2 * d ≤ v ∧ A * (v + 1) ^ d ≤ 2 ^ v

instance (A d v : ℕ) : Decidable (CutoffTest A d v) := inferInstanceAs
  (Decidable (2 * d ≤ v ∧ A * (v + 1) ^ d ≤ 2 ^ v))

/-- A primitive-recursive successful search index; efficient evaluation of
this deliberately loose witness is not needed for bounded search. -/
def cutoffWitness (A d : ℕ) : ℕ := 2 ^ (A + d + 8)

theorem cutoffWitness_spec (A d : ℕ) : CutoffTest A d (cutoffWitness A d) := by
  let k := A + d + 8
  have hk : 8 ≤ k := by dsimp [k]; omega
  have hd : d ≤ k := by dsimp [k]; omega
  have hA : A ≤ k := by dsimp [k]; omega
  have hsq := IterationAssembly.sq_le_two_pow k hk
  have hkpow : k ≤ 2 ^ k := Nat.le_of_lt Nat.lt_two_pow_self
  have hpoly : k + (k + 1) * d ≤ 2 ^ k := by
    have hmul : (k + 1) * d ≤ (k + 1) * k := Nat.mul_le_mul_left _ hd
    nlinarith
  change 2 * d ≤ 2 ^ k ∧ A * (2 ^ k + 1) ^ d ≤ 2 ^ (2 ^ k)
  refine ⟨by nlinarith, ?_⟩
  have hbase : 2 ^ k + 1 ≤ 2 ^ (k + 1) := by
    rw [pow_succ (2 : ℕ) k]
    have := Nat.one_le_two_pow (n := k)
    omega
  calc
    A * (2 ^ k + 1) ^ d ≤ 2 ^ k * (2 ^ (k + 1)) ^ d :=
      Nat.mul_le_mul (hA.trans hkpow) (Nat.pow_le_pow_left hbase _)
    _ = 2 ^ (k + (k + 1) * d) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ (2 ^ k) := Nat.pow_le_pow_right (by decide) hpoly

theorem cutoffTest_succ {A d v : ℕ} (h : CutoffTest A d v) :
    CutoffTest A d (v + 1) := by
  obtain ⟨hd, hbound⟩ := h
  refine ⟨by omega, ?_⟩
  have hratio : (v + 1 + 1) ^ d ≤ 2 * (v + 1) ^ d :=
    ScheduleCompilerExistential.pow_succ_le_two_mul (by omega)
  calc
    A * (v + 1 + 1) ^ d ≤ A * (2 * (v + 1) ^ d) := Nat.mul_le_mul_left _ hratio
    _ = 2 * (A * (v + 1) ^ d) := by ring
    _ ≤ 2 * 2 ^ v := Nat.mul_le_mul_left _ hbound
    _ = 2 ^ (v + 1) := by rw [pow_succ]; omega

theorem cutoffTest_persistent {A d v w : ℕ} (h : CutoffTest A d v) (hvw : v ≤ w) :
    CutoffTest A d w := by
  induction w, hvw using Nat.le_induction with
  | base => exact h
  | succ w _ ih => exact cutoffTest_succ ih

theorem cutoffTest_exists (A d : ℕ) : ∃ v, CutoffTest A d v :=
  ⟨cutoffWitness A d, cutoffWitness_spec A d⟩

/-- The logarithm of a sufficient graph-width demand when all public inputs
are controlled by the single scale `L`. -/
def graphDemand (L : ℕ) : ℕ := 40 + 2 * L + 2000 * L ^ 2 + 400000000 * L ^ 4

def depthDemand (L : ℕ) : ℕ := 256 * L ^ 2 + 2 + L

theorem depthDemand_mono : Monotone depthDemand := by
  intro L M h
  have hs := Nat.pow_le_pow_left h 2
  unfold depthDemand
  omega

theorem graphDemand_mono : Monotone graphDemand := by
  intro L M h
  have hs := Nat.pow_le_pow_left h 2
  have hf := Nat.pow_le_pow_left h 4
  unfold graphDemand
  omega

/-- Discharge the actual two acceptance checks from a numerical scale bound.
In particular no feasibility or eventual-acceptance assumption is hidden in
this statement. The matrix-domain checks remain the literal checks. -/
theorem accepted_of_scale_bound (p : Input) (L : ℕ)
    (hscale : scale p ≤ L) (hrows : 2 ≤ p.rows) (hcolumns : 2 ≤ p.columns)
    (hdepth : depthDemand L ≤ p.incomingDepth)
    (hedges : 2 ^ graphDemand L ≤ p.edges) : Accepted p := by
  refine ⟨hrows, hcolumns, ?_, ?_⟩
  · have hbin := binExponent_le_scale p
    have hsq := Nat.pow_le_pow_left hscale 2
    unfold firstExponent depthDemand at *
    omega
  · have hconstant : p.sourceConstant ≤ 2 ^ L :=
      (public_bounds p).1.trans (Nat.pow_le_pow_right (by decide) hscale)
    have hbin : bins p ≤ 2 ^ L :=
      (bins_le_scale_power p).trans (Nat.pow_le_pow_right (by decide) hscale)
    have houter : outerWidth p ≤ 2 ^ (1000 * L ^ 2) := by
      apply Nat.pow_le_pow_right (by decide)
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hscale 2)
    have hbalance : balanceOrder p ≤ 2 ^ (100000000 * L ^ 4) := by
      apply Nat.pow_le_pow_right (by decide)
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hscale 4)
    have hraw : p.edges ≤ secondWidth p := by
      have hs : 1 ≤ bins p := (bins_pos p)
      exact (by nlinarith : p.edges ≤ 12 * bins p * p.edges).trans
        (Nat.le_pow_clog (by decide) _)
    calc
      2 ^ 40 * p.sourceConstant * bins p * outerWidth p ^ 2 * balanceOrder p ^ 4
          ≤ 2 ^ 40 * 2 ^ L * 2 ^ L * (2 ^ (1000 * L ^ 2)) ^ 2 *
            (2 ^ (100000000 * L ^ 4)) ^ 4 := by
              gcongr
      _ = 2 ^ graphDemand L := by
        rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
        congr 1
        unfold graphDemand
        ring
      _ ≤ p.edges := hedges
      _ ≤ secondWidth p := hraw

/-- One explicit coefficient dominates both acceptance polynomials. -/
def acceptanceCoefficient (C : ℕ) : ℕ := 500000000 * (C + 1) ^ 4

theorem demands_le_quartic (L : ℕ) :
    depthDemand L ≤ 500000000 * (L + 1) ^ 4 ∧
    graphDemand L ≤ 500000000 * (L + 1) ^ 4 := by
  have hL : L ≤ (L + 1) ^ 4 := by
    have h := Nat.pow_le_pow_right (n := L + 1) (by omega) (by decide : 1 ≤ 4)
    simp only [pow_one] at h
    exact (Nat.le_succ L).trans h
  have hsq : L ^ 2 ≤ (L + 1) ^ 4 :=
    (Nat.pow_le_pow_left (Nat.le_succ L) 2).trans
      (Nat.pow_le_pow_right (by omega) (by decide))
  have hfour : L ^ 4 ≤ (L + 1) ^ 4 := Nat.pow_le_pow_left (Nat.le_succ L) 4
  have hpos : 1 ≤ (L + 1) ^ 4 := one_le_pow₀ (by omega)
  unfold depthDemand graphDemand
  constructor <;> omega

theorem demands_of_polynomial_scale {L C d v : ℕ} (hL : L ≤ C * (v + 1) ^ d) :
    depthDemand L ≤ acceptanceCoefficient C * (v + 1) ^ (4 * d) ∧
    graphDemand L ≤ acceptanceCoefficient C * (v + 1) ^ (4 * d) := by
  have hp : 1 ≤ (v + 1) ^ d := one_le_pow₀ (by omega)
  have hsum : L + 1 ≤ (C + 1) * (v + 1) ^ d := by nlinarith
  have hpow := Nat.pow_le_pow_left hsum 4
  have heq : 500000000 * ((C + 1) * (v + 1) ^ d) ^ 4 =
      acceptanceCoefficient C * (v + 1) ^ (4 * d) := by
    rw [mul_pow, ← pow_mul]
    unfold acceptanceCoefficient
    rw [Nat.mul_comm d 4]
    ring
  have hbound : 500000000 * (L + 1) ^ 4 ≤
      acceptanceCoefficient C * (v + 1) ^ (4 * d) := by
    rw [← heq]
    exact Nat.mul_le_mul_left _ hpow
  exact ⟨(demands_le_quartic L).1.trans hbound,
    (demands_le_quartic L).2.trans hbound⟩

/-- A finite integer cutoff check discharges the actual acceptance tests at
any scale obeying the displayed polynomial envelope. -/
theorem accepted_of_cutoff_test (p : Input) (C d v : ℕ)
    (hscale : scale p ≤ C * (v + 1) ^ d)
    (htest : CutoffTest (acceptanceCoefficient C) (4 * d) v)
    (hrows : 2 ≤ p.rows) (hcolumns : 2 ≤ p.columns)
    (hdepth : 2 ^ v ≤ p.incomingDepth) (hedges : 2 ^ (2 ^ v) ≤ p.edges) :
    Accepted p := by
  obtain ⟨hD, hG⟩ := demands_of_polynomial_scale hscale
  apply accepted_of_scale_bound p (scale p) le_rfl hrows hcolumns
  · exact hD.trans (htest.2.trans hdepth)
  · exact (Nat.pow_le_pow_right (by decide) (hG.trans htest.2)).trans hedges

/-- A convenient integer double logarithm for the cutoff proof. It is not
used by the matrix parameter constructor. -/
def sourceLog (n : ℕ) : ℕ := Nat.log 2 (Nat.log 2 n)

def sourceThreshold (v : ℕ) : ℕ := 2 ^ (2 ^ v)

theorem sourceLog_mono : Monotone sourceLog :=
  fun _ _ h => Nat.log_mono_right (Nat.log_mono_right h)

theorem sourceLog_threshold (v : ℕ) : sourceLog (sourceThreshold v) = v := by
  unfold sourceLog sourceThreshold
  rw [Nat.log_pow (by decide), Nat.log_pow (by decide)]

theorem sourceLog_ge_of_threshold {v n : ℕ} (h : sourceThreshold v ≤ n) :
    v ≤ sourceLog n := by
  rw [← sourceLog_threshold v]
  exact sourceLog_mono h

theorem sourceLog_available (n : ℕ) (hn : 2 ≤ n) :
    2 ^ sourceLog n ≤ Nat.clog 2 (n + 2) ∧
    sourceThreshold (sourceLog n) ≤ n := by
  have hn0 : n ≠ 0 := by omega
  have hlog0 : Nat.log 2 n ≠ 0 := (Nat.log_pos (by decide) hn).ne'
  have hpow := Nat.pow_log_le_self 2 hlog0
  refine ⟨hpow.trans ((Nat.log_le_clog 2 n).trans (Nat.clog_mono_right 2 (by omega))), ?_⟩
  exact (Nat.pow_le_pow_right (by decide) hpow).trans (Nat.pow_log_le_self 2 hn0)

def sourceDepth (n : ℕ) : ℕ := Nat.clog 2 (n + 2)

theorem source_binary_bounds (n : ℕ) :
    n ≤ 2 ^ (2 ^ (sourceLog n + 1)) ∧ sourceDepth n ≤ 2 ^ (sourceLog n + 3) := by
  let v := sourceLog n
  have hlog : Nat.log 2 n + 1 ≤ 2 ^ (v + 1) := by
    have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (Nat.log 2 n)
    exact h
  have hn : n ≤ 2 ^ (2 ^ (v + 1)) :=
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).le.trans
      (Nat.pow_le_pow_right (by decide) hlog)
  refine ⟨hn, ?_⟩
  have hp : 1 ≤ 2 ^ (v + 1) := Nat.one_le_two_pow
  have htwo : 2 ≤ 2 ^ (2 ^ (v + 1)) :=
    (by norm_num : (2 : ℕ) = 2 ^ 1) ▸ Nat.pow_le_pow_right (by decide) hp
  have hsum : n + 2 ≤ 2 ^ (2 ^ (v + 1) + 1) := by rw [pow_succ]; omega
  have hb := Nat.clog_le_of_le_pow hsum
  have he : 2 ^ (v + 1) + 1 ≤ 2 ^ (v + 3) := by
    rw [show v + 3 = (v + 1) + 2 by omega, pow_add (2 : ℕ) (v + 1) 2]
    norm_num
  exact hb.trans he

theorem source_edge_log_bound (n A d e : ℕ)
    (he : e ≤ A * n * sourceDepth n ^ d) :
    Nat.clog 2 (e + 2) ≤ 2 ^ (A + d + sourceLog n + 5) := by
  let v := sourceLog n
  let Z := A + 2 ^ (v + 1) + (v + 3) * d
  let W := A + d + v + 3
  obtain ⟨hn, hb⟩ := source_binary_bounds n
  have hA : A ≤ 2 ^ A := Nat.le_of_lt Nat.lt_two_pow_self
  have hepow : e ≤ 2 ^ Z := by
    apply he.trans
    calc
      A * n * sourceDepth n ^ d ≤ 2 ^ A * 2 ^ (2 ^ (v + 1)) * (2 ^ (v + 3)) ^ d :=
        Nat.mul_le_mul (Nat.mul_le_mul hA hn) (Nat.pow_le_pow_left hb _)
      _ = 2 ^ Z := by rw [← pow_mul, ← pow_add, ← pow_add]
  have hz : 1 ≤ Z := by dsimp [Z]; have := Nat.one_le_two_pow (n := v + 1); omega
  have htwo : 2 ≤ 2 ^ Z :=
    (by norm_num : (2 : ℕ) = 2 ^ 1) ▸ Nat.pow_le_pow_right (by decide) hz
  have hsum : e + 2 ≤ 2 ^ (Z + 1) := by rw [pow_succ]; omega
  have hlog := Nat.clog_le_of_le_pow hsum
  have hAW : A ≤ 2 ^ W := hA.trans
    (Nat.pow_le_pow_right (by decide) (by dsimp [W]; omega))
  have hpowW : 2 ^ (v + 1) ≤ 2 ^ W :=
    Nat.pow_le_pow_right (by decide) (by dsimp [W]; omega)
  have hprod : (v + 3) * d ≤ 2 ^ W := by
    have hp := Nat.mul_le_mul (Nat.le_of_lt (Nat.lt_two_pow_self (n := v + 3)))
      (Nat.le_of_lt (Nat.lt_two_pow_self (n := d)))
    rw [← pow_add] at hp
    exact hp.trans (Nat.pow_le_pow_right (by decide) (by dsimp [W]; omega))
  have hone : 1 ≤ 2 ^ W := Nat.one_le_two_pow
  have hZ : Z + 1 ≤ 4 * 2 ^ W := by dsimp [Z]; omega
  have hresult : Z + 1 ≤ 2 ^ (W + 2) := by simpa [pow_add, Nat.mul_comm] using hZ
  exact hlog.trans hresult

/-- Constants of the cited polynomial-size source enter only this explicit
initial coefficient. -/
def initialCoefficient (c A d : ℕ) : ℕ := 2 ^ 24 + c + A + d + 32

def initialInput (c e b : ℕ) : Input where
  sourceConstant := c
  nextDepth := b
  cost := IndexSeed.exponent b + 1
  rows := 2 ^ IndexSeed.width b
  columns := IndexSeed.width b
  edges := e
  incomingDepth := b

theorem initial_namingLength (c e b : ℕ) :
    namingLength (initialInput c e b) = IndexSeed.width b := by
  have he : IndexSeed.exponent b ≤ IndexSeed.width b := Nat.le_of_lt Nat.lt_two_pow_self
  change max (Nat.clog 2 (2 ^ IndexSeed.width b))
    (Nat.clog 2 (2 ^ IndexSeed.exponent b)) = IndexSeed.width b
  rw [Nat.clog_pow 2 _ (by decide), Nat.clog_pow 2 _ (by decide), max_eq_left he]

theorem initial_scale_bound (c A d n e : ℕ)
    (he : e ≤ A * n * sourceDepth n ^ d) :
    scale (initialInput c e (sourceDepth n)) ≤
      initialCoefficient c A d * (sourceLog n + 1) ^ 4 := by
  let v := sourceLog n
  let b := sourceDepth n
  let K := c + A + d + 16
  have hb : b ≤ 2 ^ (v + 3) := (source_binary_bounds n).2
  have hw : IndexSeed.width b ≤ 2 ^ (v + 11) := by
    have hp : 1 ≤ 2 ^ (v + 3) := Nat.one_le_two_pow
    have hb1 : b + 1 ≤ 2 ^ (v + 4) := by
      rw [show v + 4 = (v + 3) + 1 by omega, pow_succ]
      omega
    calc
      IndexSeed.width b ≤ 128 * (b + 1) := (IndexSeed.width_lt b).le
      _ ≤ 128 * 2 ^ (v + 4) := Nat.mul_le_mul_left _ hb1
      _ = 2 ^ (v + 11) := by
        rw [show (128 : ℕ) = 2 ^ 7 by norm_num, ← pow_add]
        congr 1
        omega
  have hc : c ≤ 2 ^ (K + v) :=
    (Nat.le_of_lt Nat.lt_two_pow_self).trans
      (Nat.pow_le_pow_right (by decide) (by dsimp [K]; omega))
  have hbK : b ≤ 2 ^ (K + v) := hb.trans
    (Nat.pow_le_pow_right (by decide) (by dsimp [K]; omega))
  have hwK : IndexSeed.width b ≤ 2 ^ (K + v) := hw.trans
    (Nat.pow_le_pow_right (by decide) (by dsimp [K]; omega))
  have hcost : IndexSeed.exponent b + 1 ≤ 2 ^ (K + v) :=
    (Nat.lt_two_pow_self (n := IndexSeed.exponent b)).trans_le hwK
  have heK : Nat.clog 2 (e + 2) ≤ 2 ^ (K + v) :=
    (source_edge_log_bound n A d e he).trans
      (Nat.pow_le_pow_right (by decide) (by dsimp [K, v]; omega))
  have htwo : 2 ≤ 2 ^ (K + v) :=
    (by norm_num : (2 : ℕ) = 2 ^ 1) ▸
      Nat.pow_le_pow_right (by decide) (by dsimp [K]; omega)
  have hbound : scaleBound (initialInput c e b) ≤ 2 ^ (K + v) := by
    unfold scaleBound
    rw [initial_namingLength]
    exact max_le hc (max_le hbK (max_le hcost (max_le hwK (max_le heK htwo))))
  have hscale : scale (initialInput c e b) ≤ max (2 ^ 24) (K + v) :=
    max_le_max le_rfl (Nat.clog_le_of_le_pow hbound)
  have hC : 1 ≤ initialCoefficient c A d := by unfold initialCoefficient; omega
  have hvC := Nat.mul_le_mul_right v hC
  have hlinear : max (2 ^ 24) (K + v) ≤ initialCoefficient c A d * (v + 1) := by
    apply max_le <;> dsimp [K, initialCoefficient] at * <;> nlinarith
  have hpow : (v + 1) ^ 1 ≤ (v + 1) ^ 4 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  rw [pow_one] at hpow
  exact hscale.trans (hlinear.trans (Nat.mul_le_mul_left _ hpow))

/-- Persistent acceptance beyond a concrete computable source threshold.
The scale envelope is the sole growth premise; no eventuality is assumed. -/
theorem accepted_beyond_threshold (p : Input) (C d v n : ℕ)
    (htest : CutoffTest (acceptanceCoefficient C) (4 * d) v)
    (hn : 2 ≤ n) (hthreshold : sourceThreshold v ≤ n)
    (hscale : scale p ≤ C * (sourceLog n + 1) ^ d)
    (hrows : 2 ≤ p.rows) (hcolumns : 2 ≤ p.columns)
    (hdepth : Nat.clog 2 (n + 2) ≤ p.incomingDepth) (hedges : n ≤ p.edges) :
    Accepted p := by
  have hv := sourceLog_ge_of_threshold hthreshold
  obtain ⟨hb, he⟩ := sourceLog_available n hn
  exact accepted_of_cutoff_test p C d (sourceLog n) hscale
    (cutoffTest_persistent htest hv) hrows hcolumns (hb.trans hdepth) (he.trans hedges)

/-- Simple common bounds for the literal parameters. The balancedness order
is large enough to dominate the other numerical widths (except the raw
source width, whose logarithm is bounded). -/
theorem parameter_size_bounds (p : Input) :
    let T := balanceOrder p
    128 ≤ T ∧ namingLength p ≤ T ∧ p.cost ≤ T ∧
    bins p ≤ T ∧ firstLength p ≤ T ∧ secondExponent p ≤ T ∧
    outerWidth p ≤ T ∧ restorationWidth p ≤ T ∧
    firstExponent p ≤ T ∧ binExponent p ≤ T ∧
    outerExponent p ≤ T ∧ restorationExponent p ≤ T ∧
    Nat.clog 2 (p.edges + 2) ≤ T := by
  dsimp only
  let L := scale p
  let B := balanceExponent p
  have hL : 2 ≤ L := by have := scale_floor p; dsimp [L]; omega
  have hL2 : L ≤ L ^ 2 := by nlinarith
  have h24 : L ^ 2 ≤ L ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
  have hB : B = 100000000 * L ^ 4 := rfl
  have hLB : L + 1 ≤ B := by omega
  have haB : firstExponent p + 2 ≤ B := by
    change 256 * L ^ 2 + 2 ≤ B
    omega
  have hrB : restorationExponent p ≤ B := by
    have h := retainedExponent_bound p
    rw [retainedExponent_eq] at h
    change restorationExponent p + 8 ≤ 1000 * L ^ 2 + 3 * L + 20 at h
    omega
  have hlarge : 128 ≤ balanceOrder p := by
    have hseven : 7 ≤ B := by omega
    exact (by norm_num : (128 : ℕ) = 2 ^ 7) ▸ Nat.pow_le_pow_right (by decide) hseven
  have hsmall : 2 ^ L ≤ balanceOrder p := Nat.pow_le_pow_right (by decide) (by omega)
  have hBsmall : B ≤ balanceOrder p := Nat.le_of_lt Nat.lt_two_pow_self
  have hb : bins p ≤ balanceOrder p := (bins_le_scale_power p).trans hsmall
  have hfirst : firstLength p ≤ balanceOrder p := by
    have hs := bins_le_firstPower p
    have hone : 1 ≤ 2 ^ firstExponent p := Nat.one_le_two_pow
    have hp : 2 ^ (firstExponent p + 2) ≤ balanceOrder p :=
      Nat.pow_le_pow_right (by decide) haB
    rw [pow_add] at hp
    norm_num at hp
    unfold firstLength firstWidth
    omega
  have hsecond : secondExponent p ≤ balanceOrder p :=
    (secondExponent_le p).trans (Nat.pow_le_pow_right (by decide) hLB)
  have hrest : restorationWidth p ≤ balanceOrder p :=
    Nat.pow_le_pow_right (by decide) hrB
  have ha : firstExponent p ≤ balanceOrder p := (by omega : firstExponent p ≤ B).trans hBsmall
  have hbin : binExponent p ≤ balanceOrder p :=
    (binExponent_le_scale p).trans
      ((Nat.le_of_lt Nat.lt_two_pow_self : L ≤ 2 ^ L).trans hsmall)
  have houter : outerExponent p ≤ balanceOrder p := by
    have h : outerExponent p ≤ B := by change 1000 * L ^ 2 ≤ B; omega
    exact h.trans hBsmall
  exact ⟨hlarge, (public_bounds p).2.2.2.1.trans hsmall,
    (public_bounds p).2.2.1.trans hsmall, hb, hfirst, hsecond,
    outer_le_balanceOrder p, hrest, ha, hbin, houter, hrB.trans hBsmall,
    (public_bounds p).2.2.2.2.trans hsmall⟩

theorem input_cardinality_bounds (p : Input) :
    p.rows ≤ 2 ^ balanceOrder p ∧ p.columns ≤ 2 ^ balanceOrder p ∧
    p.edges ≤ 2 ^ balanceOrder p := by
  have hz := (parameter_size_bounds p).2.1
  have he := (parameter_size_bounds p).2.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨?_, ?_, ?_⟩
  · apply (Nat.le_pow_clog (by decide : 1 < 2) p.rows).trans
    exact Nat.pow_le_pow_right (by decide) ((le_max_left _ _).trans hz)
  · apply (Nat.le_pow_clog (by decide : 1 < 2) p.columns).trans
    exact Nat.pow_le_pow_right (by decide) ((le_max_right _ _).trans hz)
  · have h := (Nat.le_pow_clog (by decide : 1 < 2) (p.edges + 2)).trans
      (Nat.pow_le_pow_right (by decide) he)
    omega

theorem sampler_cardinality_bound (q m T : ℕ) (hT : 1 ≤ T)
    (hq : q ≤ 2 ^ T) (hm : m ≤ 2 ^ (2 * T)) :
    PrimeSampler.size q T m ≤ 2 ^ (16 * T ^ 2) := by
  have ht : T ≤ 2 ^ T := Nat.le_of_lt Nat.lt_two_pow_self
  have hthreshold : PrimeSampler.threshold q T m ≤ 2 ^ (14 * T) := by
    apply max_le
    · apply max_le
      · exact hq.trans (Nat.pow_le_pow_right (by decide) (by omega))
      · calc
          1000 * m * T ^ 2 ≤ 2 ^ 10 * 2 ^ (2 * T) * (2 ^ T) ^ 2 := by
            gcongr
            norm_num
          _ = 2 ^ (10 + 4 * T) := by rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; ring
          _ ≤ 2 ^ (14 * T) := Nat.pow_le_pow_right (by decide) (by omega)
    · exact (by norm_num : (2 : ℕ) = 2 ^ 1) ▸ Nat.pow_le_pow_right (by decide) (by omega)
  have hprime : PrimeSampler.prime q T m ≤ 2 ^ (15 * T) := by
    calc
      PrimeSampler.prime q T m ≤ 2 * PrimeSampler.threshold q T m :=
        (PrimeSampler.prime_window q T m).2.le
      _ ≤ 2 * 2 ^ (14 * T) := Nat.mul_le_mul_left _ hthreshold
      _ = 2 ^ (14 * T + 1) := by rw [pow_succ]; omega
      _ ≤ 2 ^ (15 * T) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [PrimeSampler.size_exact]
  calc
    PrimeSampler.prime q T m ^ T ≤ (2 ^ (15 * T)) ^ T := Nat.pow_le_pow_left hprime _
    _ = 2 ^ (15 * T ^ 2) := by rw [← pow_mul]; congr 1; ring
    _ ≤ 2 ^ (16 * T ^ 2) := Nat.pow_le_pow_right (by decide) (by omega)

def familySize (p : Input) : ℕ :=
  PrimeSampler.size (secondWidth p) (balanceOrder p) (firstWidth p * p.rows)

def protectedColumnCount (p : Input) : ℕ :=
  let s := bins p
  let U := secondWidth p * p.columns ^ firstLength p
  184 * (p.columns ^ (s + 1) * U ^ s) * U * U ^ s

def protectedRowCount (p : Input) (vertices : ℕ) : ℕ :=
  let s := bins p
  let t := s * familySize p
  let v := 4 * s * vertices * p.rows
  let a := 4 * s * (s - 3) * p.rows
  2 ^ 22 * (t + v + a) * t * v * a

def nextRows (p : Input) : ℕ :=
  (outerWidth p * protectedColumnCount p) ^ restorationWidth p

def nextColumns (p : Input) (vertices : ℕ) : ℕ :=
  restorationWidth p * protectedRowCount p vertices ^ outerWidth p

theorem familySize_bound (p : Input) : familySize p ≤ 2 ^ (16 * balanceOrder p ^ 2) := by
  obtain ⟨hT, _, _, _, hfirst, hq, _⟩ := parameter_size_bounds p
  have hrows := (input_cardinality_bounds p).1
  apply sampler_cardinality_bound _ _ _ (by omega)
  · exact Nat.pow_le_pow_right (by decide) hq
  · have hw : firstWidth p ≤ balanceOrder p :=
      (by unfold firstLength at hfirst; omega)
    have hpow : balanceOrder p ≤ 2 ^ balanceOrder p := Nat.le_of_lt Nat.lt_two_pow_self
    calc
      firstWidth p * p.rows ≤ 2 ^ balanceOrder p * 2 ^ balanceOrder p :=
        Nat.mul_le_mul (hw.trans hpow) hrows
      _ = 2 ^ (2 * balanceOrder p) := by rw [← pow_add]; congr 1; omega

private theorem power_mul_bound {a b x y : ℕ} (ha : a ≤ 2 ^ x) (hb : b ≤ 2 ^ y) :
    a * b ≤ 2 ^ (x + y) := by
  rw [pow_add]
  exact Nat.mul_le_mul ha hb

private theorem power_add_bound {a b x : ℕ} (ha : a ≤ 2 ^ x) (hb : b ≤ 2 ^ x) :
    a + b ≤ 2 ^ (x + 1) := by
  rw [pow_succ]
  omega

private theorem power_exp_bound {a x y z : ℕ} (ha : a ≤ 2 ^ x) (hy : y ≤ z) :
    a ^ y ≤ 2 ^ (x * z) := by
  calc
    a ^ y ≤ (2 ^ x) ^ y := Nat.pow_le_pow_left ha _
    _ = 2 ^ (x * y) := (pow_mul _ _ _).symm
    _ ≤ 2 ^ (x * z) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hy)

theorem protectedColumnCount_bound (p : Input) :
    protectedColumnCount p ≤ 2 ^ (16 * balanceOrder p ^ 3) := by
  let T := balanceOrder p
  obtain ⟨hlarge, _, _, hs, hl, hq, _⟩ := parameter_size_bounds p
  have hT : 1 ≤ T := by dsimp [T]; omega
  have hcols : p.columns ≤ 2 ^ T := (input_cardinality_bounds p).2.1
  have hT2 : T ≤ T ^ 2 := by nlinarith
  have hT3 : T ^ 2 ≤ T ^ 3 := Nat.pow_le_pow_right hT (by decide)
  have hqpower : secondWidth p ≤ 2 ^ T := Nat.pow_le_pow_right (by decide) hq
  have hU : secondWidth p * p.columns ^ firstLength p ≤ 2 ^ (2 * T ^ 2) := by
    have h := power_mul_bound hqpower (power_exp_bound hcols hl)
    apply h.trans (Nat.pow_le_pow_right (by decide) ?_)
    nlinarith
  have htail : (secondWidth p * p.columns ^ firstLength p) ^ bins p ≤
      2 ^ (2 * T ^ 3) := by
    have h := power_exp_bound hU hs
    convert h using 1 <;> ring
  have hfirst : p.columns ^ (bins p + 1) ≤ 2 ^ (2 * T ^ 2) := by
    have h := power_exp_bound hcols (show bins p + 1 ≤ T + 1 by omega)
    exact h.trans (Nat.pow_le_pow_right (by decide) (by nlinarith))
  have h := power_mul_bound
    (power_mul_bound (power_mul_bound (by norm_num : (184 : ℕ) ≤ 2 ^ 8)
      (power_mul_bound hfirst htail)) hU) htail
  apply h.trans (Nat.pow_le_pow_right (by decide) ?_)
  have hpos : 1 ≤ T ^ 3 := one_le_pow₀ hT
  dsimp only [T] at *
  omega

theorem protectedRowCount_bound (p : Input) (vertices : ℕ)
    (hv : vertices ≤ 2 * p.edges) :
    protectedRowCount p vertices ≤ 2 ^ (80 * balanceOrder p ^ 2) := by
  let T := balanceOrder p
  obtain ⟨hlarge, _, _, hs, _⟩ := parameter_size_bounds p
  have hT : 1 ≤ T := by dsimp [T]; omega
  have hT2 : T ≤ T ^ 2 := by nlinarith
  have hrows : p.rows ≤ 2 ^ T := (input_cardinality_bounds p).1
  have hedges : p.edges ≤ 2 ^ T := (input_cardinality_bounds p).2.2
  have hspow : bins p ≤ 2 ^ T := hs.trans (Nat.le_of_lt Nat.lt_two_pow_self)
  have hvpow : vertices ≤ 2 ^ (2 * T) := by
    calc
      vertices ≤ 2 * p.edges := hv
      _ ≤ 2 * 2 ^ T := Nat.mul_le_mul_left _ hedges
      _ = 2 ^ (T + 1) := by rw [pow_succ]; omega
      _ ≤ 2 ^ (2 * T) := Nat.pow_le_pow_right (by decide) (by omega)
  have ht : bins p * familySize p ≤ 2 ^ (17 * T ^ 2) := by
    have h := power_mul_bound hspow (familySize_bound p)
    exact h.trans (Nat.pow_le_pow_right (by decide) (by dsimp [T] at *; omega))
  have hvrow : 4 * bins p * vertices * p.rows ≤ 2 ^ (6 * T ^ 2) := by
    have h := power_mul_bound
      (power_mul_bound (power_mul_bound (by norm_num : (4 : ℕ) ≤ 2 ^ 2) hspow) hvpow) hrows
    exact h.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have harow : 4 * bins p * (bins p - 3) * p.rows ≤ 2 ^ (5 * T ^ 2) := by
    have h := power_mul_bound
      (power_mul_bound (power_mul_bound (by norm_num : (4 : ℕ) ≤ 2 ^ 2) hspow)
        ((Nat.sub_le (bins p) 3).trans hspow)) hrows
    exact h.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hvsmall : 4 * bins p * vertices * p.rows ≤ 2 ^ (17 * T ^ 2) :=
    hvrow.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hasmall : 4 * bins p * (bins p - 3) * p.rows ≤ 2 ^ (17 * T ^ 2 + 1) :=
    harow.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hsum := power_add_bound (power_add_bound ht hvsmall) hasmall
  have h := power_mul_bound
    (power_mul_bound (power_mul_bound (power_mul_bound (le_refl (2 ^ 22)) hsum) ht) hvrow) harow
  apply h.trans (Nat.pow_le_pow_right (by decide) ?_)
  have hpos : 1 ≤ T ^ 2 := one_le_pow₀ hT
  dsimp only [T] at *
  omega

theorem next_cardinality_bounds (p : Input) (vertices : ℕ)
    (hv : vertices ≤ 2 * p.edges) :
    nextRows p ≤ 2 ^ (128 * balanceOrder p ^ 4) ∧
    nextColumns p vertices ≤ 2 ^ (128 * balanceOrder p ^ 4) := by
  let T := balanceOrder p
  obtain ⟨hlarge, _, _, _, _, _, hq, hQ, _⟩ := parameter_size_bounds p
  have hT : 1 ≤ T := by dsimp [T]; omega
  have hT2 : T ≤ T ^ 2 := by nlinarith
  have hT3 : T ^ 2 ≤ T ^ 3 := Nat.pow_le_pow_right hT (by decide)
  have hT4 : T ^ 3 ≤ T ^ 4 := Nat.pow_le_pow_right hT (by decide)
  have ht : T ≤ 2 ^ T := Nat.le_of_lt Nat.lt_two_pow_self
  constructor
  · have h := power_exp_bound
      (power_mul_bound (hq.trans ht) (protectedColumnCount_bound p)) hQ
    apply h.trans (Nat.pow_le_pow_right (by decide) ?_)
    change (T + 16 * T ^ 3) * T ≤ 128 * T ^ 4
    nlinarith [one_le_pow₀ hT (n := 4)]
  · have h := power_mul_bound (hQ.trans ht)
      (power_exp_bound (protectedRowCount_bound p vertices hv) hq)
    apply h.trans (Nat.pow_le_pow_right (by decide) ?_)
    change T + 80 * T ^ 2 * T ≤ 128 * T ^ 4
    nlinarith

theorem next_domains (p : Input) (vertices : ℕ)
    (hr : 0 < p.rows) (hc : 0 < p.columns) (hv : 0 < vertices) :
    2 ≤ nextRows p ∧ 2 ≤ nextColumns p vertices := by
  have hs : 0 < bins p := bins_pos p
  have hsq := bins_hard_seed_floor p
  have hone : 1 ≤ 2 ^ (2 ^ 20) := Nat.one_le_two_pow
  have haux : 0 < bins p - 3 := by omega
  clear hsq hone
  have hf : 0 < familySize p := PrimeSampler.size_pos _ _ _
  have hq : 0 < secondWidth p := secondWidth_pos p
  have houter : 1 ≤ outerWidth p := outerWidth_pos p
  have hrest : 1 ≤ restorationWidth p := restorationWidth_pos p
  have hcol : 2 ≤ protectedColumnCount p := by
    let U := secondWidth p * p.columns ^ firstLength p
    have hU : 0 < U := by dsimp [U]; positivity
    have hp : 0 < p.columns ^ (bins p + 1) * U ^ bins p * U * U ^ bins p := by positivity
    have heq : protectedColumnCount p =
        184 * (p.columns ^ (bins p + 1) * U ^ bins p * U * U ^ bins p) := by
      unfold protectedColumnCount
      dsimp [U]
      ring
    rw [heq]
    omega
  have hrow : 2 ≤ protectedRowCount p vertices := by
    let t := bins p * familySize p
    let v := 4 * bins p * vertices * p.rows
    let a := 4 * bins p * (bins p - 3) * p.rows
    have ht : 0 < t := by dsimp [t]; positivity
    have hv' : 0 < v := by dsimp [v]; positivity
    have ha : 0 < a := by dsimp [a]; positivity
    have hp : 0 < (t + v + a) * t * v * a := by positivity
    have heq : protectedRowCount p vertices = 2 ^ 22 * ((t + v + a) * t * v * a) := by
      unfold protectedRowCount
      dsimp [t, v, a]
      ring
    rw [heq]
    norm_num
    omega
  constructor
  · have hb : 2 ≤ outerWidth p * protectedColumnCount p :=
      hcol.trans (by nlinarith)
    have hp := Nat.pow_le_pow_right (by omega : 1 ≤ outerWidth p * protectedColumnCount p) hrest
    simp only [pow_one] at hp
    exact hb.trans hp
  · have hp := Nat.pow_le_pow_right (by omega : 1 ≤ protectedRowCount p vertices) houter
    simp only [pow_one] at hp
    have htwo := hrow.trans hp
    change 2 ≤ restorationWidth p * protectedRowCount p vertices ^ outerWidth p
    nlinarith

/-- Exact numeric input data for the following application. -/
def nextInput (p : Input) (vertices : ℕ) : Input :=
  { p with
    rows := nextRows p
    columns := nextColumns p vertices
    cost := p.cost + firstExponent p + secondExponent p + binExponent p +
      outerExponent p + restorationExponent p + 1 }

def nextScale (L : ℕ) : ℕ := 400000000 * L ^ 4 + 7

def coefficient (C : ℕ) : ℕ → ℕ
  | 0 => C
  | i + 1 => 400000000 * coefficient C i ^ 4 + 7

@[simp] theorem coefficient_zero (C : ℕ) : coefficient C 0 = C := rfl
@[simp] theorem coefficient_succ (C i : ℕ) :
    coefficient C (i + 1) = 400000000 * coefficient C i ^ 4 + 7 := rfl

theorem nextScale_polynomial_bound {L C d v : ℕ} (h : L ≤ C * (v + 1) ^ d) :
    nextScale L ≤ (400000000 * C ^ 4 + 7) * (v + 1) ^ (8 * d + 100) := by
  have hp := Nat.pow_le_pow_left h 4
  rw [mul_pow, ← pow_mul] at hp
  have hbase : 1 ≤ v + 1 := by omega
  have hpos : 1 ≤ (v + 1) ^ (4 * d) := one_le_pow₀ hbase
  have hpower : (v + 1) ^ (4 * d) ≤ (v + 1) ^ (8 * d + 100) :=
    Nat.pow_le_pow_right hbase (by omega)
  rw [Nat.mul_comm d 4] at hp
  calc
    nextScale L ≤ (400000000 * C ^ 4 + 7) * (v + 1) ^ (4 * d) := by
      unfold nextScale
      nlinarith
    _ ≤ _ := Nat.mul_le_mul_left _ hpower

theorem nextScale_identity (p : Input) :
    128 * balanceOrder p ^ 4 = 2 ^ nextScale (scale p) := by
  unfold balanceOrder nextScale balanceExponent
  rw [← pow_mul, show (128 : ℕ) = 2 ^ 7 by norm_num, ← pow_add]
  congr 1
  ring

theorem nextScale_mono : Monotone nextScale := by
  intro x y h
  have := Nat.pow_le_pow_left h 4
  unfold nextScale
  omega

def oneLevelBound (p : Input) : ℕ := 2 ^ nextScale (scale p)

theorem balanceOrder_le_oneLevelBound (p : Input) : balanceOrder p ≤ oneLevelBound p := by
  rw [oneLevelBound, ← nextScale_identity]
  have hT : 1 ≤ balanceOrder p := by have := (parameter_size_bounds p).1; omega
  have hp := Nat.pow_le_pow_right hT (by decide : 1 ≤ 4)
  simp only [pow_one] at hp
  omega

theorem current_naming_bound (p : Input) : max 1 (namingLength p) ≤ oneLevelBound p := by
  apply max_le Nat.one_le_two_pow
  exact (parameter_size_bounds p).2.1.trans (balanceOrder_le_oneLevelBound p)

theorem nextDepth_le_balanceOrder (p : Input) : p.nextDepth ≤ balanceOrder p := by
  have hL : 1 ≤ scale p := by have := scale_floor p; omega
  have hp := Nat.pow_le_pow_right hL (by decide : 1 ≤ 4)
  simp only [pow_one] at hp
  exact (public_bounds p).2.1.trans (Nat.pow_le_pow_right (by decide) (by
    change scale p ≤ 100000000 * scale p ^ 4
    omega))

theorem current_budget_bound (p : Input) (i : ℕ) (hi : i ≤ p.nextDepth) :
    p.cost + i ≤ oneLevelBound p := by
  obtain ⟨hlarge, _, hc, _⟩ := parameter_size_bounds p
  have hT : 1 ≤ balanceOrder p := by omega
  have hp := Nat.pow_le_pow_right hT (by decide : 1 ≤ 4)
  simp only [pow_one] at hp
  have := hi.trans (nextDepth_le_balanceOrder p)
  rw [oneLevelBound, ← nextScale_identity]
  omega

theorem next_budget_bound (p : Input) (vertices i : ℕ) (hi : i ≤ p.nextDepth) :
    (nextInput p vertices).cost + i ≤ oneLevelBound p := by
  obtain ⟨hlarge, _, hc, _, _, hsecond, _, _, ha, hs, hq, hQ, _⟩ := parameter_size_bounds p
  have hT : 1 ≤ balanceOrder p := by omega
  have hp := Nat.pow_le_pow_right hT (by decide : 1 ≤ 4)
  simp only [pow_one] at hp
  have := hi.trans (nextDepth_le_balanceOrder p)
  rw [oneLevelBound, ← nextScale_identity]
  change p.cost + firstExponent p + secondExponent p + binExponent p +
    outerExponent p + restorationExponent p + 1 + i ≤ 128 * balanceOrder p ^ 4
  omega

theorem next_naming_bound (p : Input) (vertices : ℕ) (hv : vertices ≤ 2 * p.edges) :
    max 1 (namingLength (nextInput p vertices)) ≤ oneLevelBound p := by
  obtain ⟨hr, hc⟩ := next_cardinality_bounds p vertices hv
  rw [nextScale_identity] at hr hc
  exact max_le Nat.one_le_two_pow
    (max_le (Nat.clog_le_of_le_pow hr) (Nat.clog_le_of_le_pow hc))

/-- Numerical widths and restriction depths are bounded by value; sampler
and protected carriers are bounded in binary length, as in the manuscript.
In particular this does not incorrectly bound the raw source width by value. -/
theorem internal_size_bounds (p : Input) (vertices : ℕ) (hv : vertices ≤ 2 * p.edges) :
    outerWidth p ≤ oneLevelBound p ∧ restorationWidth p ≤ oneLevelBound p ∧
    firstWidth p ≤ oneLevelBound p ∧ firstDepth p ≤ oneLevelBound p ∧
    tailDepth p ≤ oneLevelBound p ∧ secondDepth p ≤ oneLevelBound p ∧
    Nat.clog 2 (familySize p) ≤ oneLevelBound p ∧
    Nat.clog 2 (protectedRowCount p vertices) ≤ oneLevelBound p ∧
    Nat.clog 2 (protectedColumnCount p) ≤ oneLevelBound p ∧
    Nat.clog 2 (secondWidth p) ≤ oneLevelBound p := by
  obtain ⟨hlarge, _, _, hs, hl, hsecond, hq, hQ, _⟩ := parameter_size_bounds p
  have hL : 1 ≤ scale p := by have := scale_floor p; omega
  have hLfour := Nat.pow_le_pow_right hL (by decide : 1 ≤ 4)
  simp only [pow_one] at hLfour
  have hT : 1 ≤ balanceOrder p := by omega
  have hTf : balanceOrder p ^ 2 ≤ balanceOrder p ^ 4 :=
    Nat.pow_le_pow_right hT (by decide)
  have hTc : balanceOrder p ^ 3 ≤ balanceOrder p ^ 4 :=
    Nat.pow_le_pow_right hT (by decide)
  have hbound := balanceOrder_le_oneLevelBound p
  have hf : firstDepth p ≤ balanceOrder p := by
    exact Nat.pow_le_pow_right (by decide) (by
      change 7 * scale p ≤ 100000000 * scale p ^ 4
      omega)
  have ht : tailDepth p ≤ balanceOrder p := by
    have := tailDepth_four_le_bins p
    omega
  have hd : secondDepth p ≤ balanceOrder p := (secondDepth_bound p).trans
    (Nat.pow_le_pow_right (by decide) (by
      change scale p + 2 ≤ 100000000 * scale p ^ 4
      omega))
  have hfamily := Nat.clog_le_of_le_pow (familySize_bound p)
  have hrow := Nat.clog_le_of_le_pow (protectedRowCount_bound p vertices hv)
  have hcolumn := Nat.clog_le_of_le_pow (protectedColumnCount_bound p)
  have hfamily' : Nat.clog 2 (familySize p) ≤ oneLevelBound p := by
    rw [oneLevelBound, ← nextScale_identity]
    omega
  have hrow' : Nat.clog 2 (protectedRowCount p vertices) ≤ oneLevelBound p := by
    rw [oneLevelBound, ← nextScale_identity]
    omega
  have hcolumn' : Nat.clog 2 (protectedColumnCount p) ≤ oneLevelBound p := by
    rw [oneLevelBound, ← nextScale_identity]
    omega
  refine ⟨hq.trans hbound, hQ.trans hbound, ?_, hf.trans hbound, ht.trans hbound,
    hd.trans hbound, hfamily', hrow', hcolumn', ?_⟩
  · exact (by unfold firstLength at hl; omega : firstWidth p ≤ balanceOrder p).trans hbound
  · simpa only [secondWidth, Nat.clog_pow 2 _ (by decide : 1 < 2)] using
      hsecond.trans hbound

/-- This is a bound on table entries, not on the time of an implementation. -/
theorem entry_count_of_naming_bound (p : Input) (S k n : ℕ)
    (hname : max 1 (namingLength p) ≤ S) (hsmall : 2 * k * S < n) :
    (p.rows * p.columns) ^ k < 2 ^ n := by
  have hr : p.rows ≤ 2 ^ S := (Nat.le_pow_clog (by decide : 1 < 2) _).trans
    (Nat.pow_le_pow_right (by decide) ((le_max_left _ _).trans
      ((le_max_right _ _).trans hname)))
  have hc : p.columns ≤ 2 ^ S := (Nat.le_pow_clog (by decide : 1 < 2) _).trans
    (Nat.pow_le_pow_right (by decide) ((le_max_right _ _).trans
      ((le_max_right _ _).trans hname)))
  have hp := Nat.pow_le_pow_left (power_mul_bound hr hc) k
  rw [← pow_mul] at hp
  exact hp.trans_lt ((Nat.pow_lt_pow_iff_right (by decide)).2 (by nlinarith))

def sizeTestCoefficient (C k : ℕ) : ℕ := acceptanceCoefficient C + 2 * k + 1

theorem sizeTest_implies_acceptance {C k d v : ℕ}
    (h : CutoffTest (sizeTestCoefficient C k) d v) :
    CutoffTest (acceptanceCoefficient C) d v := by
  refine ⟨h.1, ?_⟩
  exact (Nat.mul_le_mul_right _ (by unfold sizeTestCoefficient; omega)).trans h.2

theorem test_level_le_sourceDepth {C k d n : ℕ} (hn : 2 ≤ n)
    (h : CutoffTest (sizeTestCoefficient C k) d (sourceLog n)) : k ≤ sourceDepth n := by
  have hpos : 1 ≤ (sourceLog n + 1) ^ d := one_le_pow₀ (by omega)
  have hmul : sizeTestCoefficient C k ≤
      sizeTestCoefficient C k * (sourceLog n + 1) ^ d := by
    simpa using Nat.mul_le_mul_left (sizeTestCoefficient C k) hpos
  have hm := hmul.trans h.2
  have hk : k ≤ 2 ^ sourceLog n := by unfold sizeTestCoefficient at hm; omega
  exact hk.trans (sourceLog_available n hn).1

theorem oneLevelBound_fits (p : Input) (C d v k n : ℕ)
    (hscale : scale p ≤ C * (v + 1) ^ d)
    (htest : CutoffTest (sizeTestCoefficient C k) (4 * d) v)
    (hn : sourceThreshold v ≤ n) : 2 * k * oneLevelBound p < n := by
  have hG := (demands_of_polynomial_scale hscale).2
  have hNG : nextScale (scale p) ≤ graphDemand (scale p) := by
    unfold nextScale graphDemand
    omega
  have hpos : 1 ≤ (v + 1) ^ (4 * d) := one_le_pow₀ (by omega)
  have hmargin : nextScale (scale p) + 2 * k + 1 ≤ 2 ^ v := by
    have hsum : nextScale (scale p) + 2 * k + 1 ≤
        sizeTestCoefficient C k * (v + 1) ^ (4 * d) := by
      unfold sizeTestCoefficient
      have hconst := Nat.mul_le_mul_left (2 * k + 1) hpos
      nlinarith
    exact hsum.trans htest.2
  have hk : 2 * k ≤ 2 ^ (2 * k) := Nat.le_of_lt Nat.lt_two_pow_self
  calc
    2 * k * oneLevelBound p ≤ 2 ^ (2 * k) * 2 ^ nextScale (scale p) :=
      Nat.mul_le_mul_right _ hk
    _ = 2 ^ (2 * k + nextScale (scale p)) := (pow_add _ _ _).symm
    _ < 2 ^ (2 ^ v) := (Nat.pow_lt_pow_iff_right (by decide)).2 (by omega)
    _ ≤ n := hn

def cutoffScale (c A d k : ℕ) : ℕ :=
  (Finset.range k).sup fun i =>
    cutoffWitness (sizeTestCoefficient (coefficient (initialCoefficient c A d) i) k)
      (4 * degree i)

def sourceCutoff (c A d k : ℕ) : ℕ :=
  max k (max 2 (sourceThreshold (cutoffScale c A d k)))

theorem cutoffScale_spec (c A d k i : ℕ) (hi : i < k) :
    CutoffTest (sizeTestCoefficient (coefficient (initialCoefficient c A d) i) k)
      (4 * degree i) (cutoffScale c A d k) := by
  apply cutoffTest_persistent (cutoffWitness_spec _ _)
  exact Finset.le_sup
    (f := fun j => cutoffWitness
      (sizeTestCoefficient (coefficient (initialCoefficient c A d) j) k) (4 * degree j))
    (Finset.mem_range.mpr hi)

theorem sourceCutoff_ge_level (c A d k : ℕ) : k ≤ sourceCutoff c A d k := le_max_left _ _

theorem scale_nextInput (p : Input) (vertices : ℕ) (hv : vertices ≤ 2 * p.edges) :
    scale (nextInput p vertices) ≤ nextScale (scale p) := by
  let T := balanceOrder p
  let H := nextScale (scale p)
  have hTH : T ≤ 2 ^ H := by
    rw [← nextScale_identity]
    have hT : 1 ≤ T := (by have := (parameter_size_bounds p).1; dsimp [T]; omega)
    have hpow := Nat.pow_le_pow_right hT (by decide : 1 ≤ 4)
    simp only [pow_one] at hpow
    change T ≤ 128 * T ^ 4
    omega
  have hscalar : scale p ≤ H := by
    have hL : 1 ≤ scale p := by have := scale_floor p; omega
    have hp := Nat.pow_le_pow_right hL (by decide : 1 ≤ 4)
    simp only [pow_one] at hp
    change scale p ≤ 400000000 * scale p ^ 4 + 7
    omega
  have hpublic : 2 ^ scale p ≤ 2 ^ H := Nat.pow_le_pow_right (by decide) hscalar
  have hcost : (nextInput p vertices).cost ≤ 2 ^ H := by
    obtain ⟨hlarge, _, hc, _, _, hsecond, _, _, ha, hs, hq, hQ, _⟩ := parameter_size_bounds p
    have hT : 1 ≤ T := by dsimp [T]; omega
    have hpow := Nat.pow_le_pow_right hT (by decide : 1 ≤ 4)
    simp only [pow_one] at hpow
    rw [← nextScale_identity]
    change p.cost + firstExponent p + secondExponent p + binExponent p +
      outerExponent p + restorationExponent p + 1 ≤ 128 * T ^ 4
    dsimp only [T] at *
    omega
  obtain ⟨hrows, hcolumns⟩ := next_cardinality_bounds p vertices hv
  have hnames : namingLength (nextInput p vertices) ≤ 2 ^ H := by
    apply max_le
    · have h := Nat.clog_le_of_le_pow hrows
      rw [nextScale_identity] at h
      exact h
    · have h := Nat.clog_le_of_le_pow hcolumns
      rw [nextScale_identity] at h
      exact h
  have hbound : scaleBound (nextInput p vertices) ≤ 2 ^ H := by
    obtain ⟨hc, hb, _, _, he⟩ := public_bounds p
    refine max_le (hc.trans hpublic) (max_le (hb.trans hpublic)
      (max_le hcost (max_le hnames (max_le (he.trans hpublic) ?_))))
    have hH : 1 ≤ H := by change 1 ≤ 400000000 * scale p ^ 4 + 7; omega
    exact (by norm_num : (2 : ℕ) = 2 ^ 1) ▸ Nat.pow_le_pow_right (by decide) hH
  exact max_le ((scale_floor p).trans hscalar) (Nat.clog_le_of_le_pow hbound)

section LiteralStep

open GuardedSourceGraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem step_exact_counts (G : EndpointGraph V E) (c b y i : ℕ) (M : Iteration.Matrix) :
    let p := Iteration.parameters G c b y i M
    (Iteration.step G c b y i M).rows = nextRows p ∧
    (Iteration.step G c b y i M).columns = nextColumns p (Fintype.card V) := by
  dsimp only
  obtain ⟨hr, hc⟩ := Iteration.step_dimensions G c b y i M
  constructor
  · rw [hr]
    unfold nextRows protectedColumnCount
    rw [Construction.card_protectedColumns]
    simp only [Fintype.card_fin, Construction.firstLength, firstLength, Nat.add_assoc]
    rfl
  · rw [hc]
    unfold nextColumns protectedRowCount
    rw [Construction.card_protectedRows]
    simp only [Fintype.card_fin, GraphVectors.vertexCount, GraphVectors.auxiliaryCount]
    congr 2
    rw [show Iteration.labels G c b y i M =
      familySize (Iteration.parameters G c b y i M) from rfl]
    change 2 ^ 22 * (_ + (_ + _) * M.rows) * _ * _ * _ = _
    dsimp only [Iteration.s, Iteration.stepParameters, Iteration.parameters]
    ring

theorem step_next_parameters (G : EndpointGraph V E) (c b y i : ℕ) (M : Iteration.Matrix) :
    Iteration.parameters G c b (y + Iteration.overhead G c b y i M) (i + 1)
        (Iteration.step G c b y i M) =
      nextInput (Iteration.parameters G c b y i M) (Fintype.card V) := by
  obtain ⟨hr, hc⟩ := step_exact_counts G c b y i M
  unfold Iteration.parameters nextInput
  congr 1 <;> first
  | exact hr
  | exact hc
  | simp only [Iteration.overhead, Iteration.a, Iteration.rq, Iteration.rQ,
      Iteration.stepParameters, Iteration.parameters, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm]

theorem step_scale_bound (G : EndpointGraph V E) (c b y i : ℕ) (M : Iteration.Matrix)
    (hv : Fintype.card V ≤ 2 * Fintype.card E) :
    scale (Iteration.parameters G c b (y + Iteration.overhead G c b y i M) (i + 1)
        (Iteration.step G c b y i M)) ≤
      nextScale (scale (Iteration.parameters G c b y i M)) := by
  rw [step_next_parameters]
  exact scale_nextInput _ _ hv

def runParameters (G : EndpointGraph V E) (c b : ℕ) (initial : Iteration.State) (i : ℕ) : Input :=
  let current := Iteration.run G c b initial i
  Iteration.parameters G c b current.budget i current.matrix

theorem runParameters_succ (G : EndpointGraph V E) (c b : ℕ)
    (initial : Iteration.State) (i : ℕ) :
    runParameters G c b initial (i + 1) =
      nextInput (runParameters G c b initial i) (Fintype.card V) :=
  step_next_parameters G c b _ i _

/-- The polynomial scale envelope follows by induction from the proved
cardinality bound for the actual step. No per-level size hypothesis is used. -/
theorem run_scale_bound (G : EndpointGraph V E) (c b : ℕ)
    (initial : Iteration.State) (C v : ℕ)
    (hv : Fintype.card V ≤ 2 * Fintype.card E)
    (hzero : scale (runParameters G c b initial 0) ≤ C * (v + 1) ^ 4) :
    ∀ i, scale (runParameters G c b initial i) ≤
      coefficient C i * (v + 1) ^ degree i := by
  intro i
  induction i with
  | zero => exact hzero
  | succ i ih =>
    rw [runParameters_succ]
    exact (scale_nextInput _ _ hv).trans (nextScale_polynomial_bound ih)

theorem runParameters_zero_indexing (G : EndpointGraph V E) (c b : ℕ) :
    runParameters G c b (Iteration.seedState b) 0 = initialInput c (Fintype.card E) b := rfl

theorem initial_domains (c e b : ℕ) :
    2 ≤ (initialInput c e b).rows ∧ 2 ≤ (initialInput c e b).columns := by
  change 2 ≤ 2 ^ IndexSeed.width b ∧ 2 ≤ IndexSeed.width b
  have hw : 2 ≤ IndexSeed.width b := by have := IndexSeed.width_lower b; omega
  refine ⟨?_, hw⟩
  simpa only [pow_one] using
    Nat.pow_le_pow_right (n := 2) (by decide) (show 1 ≤ IndexSeed.width b by omega)

theorem run_indexing_domains (G : EndpointGraph V E) (c b i : ℕ) :
    2 ≤ (runParameters G c b (Iteration.seedState b) i).rows ∧
    2 ≤ (runParameters G c b (Iteration.seedState b) i).columns := by
  induction i with
  | zero => rw [runParameters_zero_indexing]; exact initial_domains _ _ _
  | succ i ih =>
    rw [runParameters_succ]
    exact next_domains _ _ (by omega) (by omega) G.card_vertex_pos

theorem run_indexing_scale (G : EndpointGraph V E) (c A d n : ℕ)
    (hv : Fintype.card V ≤ 2 * Fintype.card E)
    (he : Fintype.card E ≤ A * n * sourceDepth n ^ d) :
    ∀ i, scale (runParameters G c (sourceDepth n) (Iteration.seedState (sourceDepth n)) i) ≤
      coefficient (initialCoefficient c A d) i * (sourceLog n + 1) ^ degree i := by
  apply run_scale_bound G c (sourceDepth n) (Iteration.seedState (sourceDepth n))
    (initialCoefficient c A d) (sourceLog n) hv
  rw [runParameters_zero_indexing]
  exact initial_scale_bound c A d n _ he

/-- The actual fixed-graph iteration is accepted and small whenever these
explicit finite tests succeed. Every scale bound and matrix-domain condition
is derived here, not supplied as a per-level oracle. -/
theorem run_indexing_of_tests (G : EndpointGraph V E) (c A d n k : ℕ)
    (hn : 2 ≤ n) (hv : Fintype.card V ≤ 2 * Fintype.card E)
    (hlower : n ≤ Fintype.card E)
    (hupper : Fintype.card E ≤ A * n * sourceDepth n ^ d)
    (htests : ∀ i < k,
      CutoffTest (sizeTestCoefficient (coefficient (initialCoefficient c A d) i) k)
        (4 * degree i) (sourceLog n)) :
    ∀ i < k,
      Accepted (runParameters G c (sourceDepth n) (Iteration.seedState (sourceDepth n)) i) ∧
      2 * k * oneLevelBound
        (runParameters G c (sourceDepth n) (Iteration.seedState (sourceDepth n)) i) < n := by
  intro i hi
  have hscale := run_indexing_scale G c A d n hv hupper i
  have hdomains := run_indexing_domains G c (sourceDepth n) i
  have havailable := sourceLog_available n hn
  constructor
  · exact accepted_of_cutoff_test _ _ _ _ hscale
      (sizeTest_implies_acceptance (htests i hi)) hdomains.1 hdomains.2
        havailable.1 (havailable.2.trans hlower)
  · exact oneLevelBound_fits _ _ _ _ _ _ hscale (htests i hi) havailable.2

/-- A concrete total cutoff for every fixed number of repetitions, with
persistence for every larger source length and uniformity across source
graphs satisfying the same size constants. -/
theorem run_indexing_beyond_cutoff (G : EndpointGraph V E) (c A d n k : ℕ)
    (hcut : sourceCutoff c A d k ≤ n)
    (hv : Fintype.card V ≤ 2 * Fintype.card E)
    (hlower : n ≤ Fintype.card E)
    (hupper : Fintype.card E ≤ A * n * sourceDepth n ^ d) :
    ∀ i < k,
      Accepted (runParameters G c (sourceDepth n) (Iteration.seedState (sourceDepth n)) i) ∧
      2 * k * oneLevelBound
        (runParameters G c (sourceDepth n) (Iteration.seedState (sourceDepth n)) i) < n := by
  have hn : 2 ≤ n := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hcut
  have hthreshold : sourceThreshold (cutoffScale c A d k) ≤ n :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans hcut
  apply run_indexing_of_tests G c A d n k hn hv hlower hupper
  intro i hi
  exact cutoffTest_persistent (cutoffScale_spec c A d k i hi)
    (sourceLog_ge_of_threshold hthreshold)

/-- Actual input-name lengths, including the final matrix after application
`k`, follow from the concrete per-application numerical bounds. -/
theorem run_naming_small (G : EndpointGraph V E) (c b : ℕ)
    (initial : Iteration.State) (k n : ℕ) (hk : 0 < k)
    (hv : Fintype.card V ≤ 2 * Fintype.card E)
    (hlevels : ∀ i < k, 2 * k * oneLevelBound (runParameters G c b initial i) < n) :
    ∀ j ≤ k, 2 * k * max 1 (namingLength (runParameters G c b initial j)) < n := by
  intro j hj
  cases j with
  | zero =>
    exact (Nat.mul_le_mul_left _ (current_naming_bound _)).trans_lt (hlevels 0 hk)
  | succ j =>
    rw [runParameters_succ]
    exact (Nat.mul_le_mul_left _ (next_naming_bound _ _ hv)).trans_lt
      (hlevels j (by omega))

theorem run_budget_small (G : EndpointGraph V E) (c b : ℕ)
    (initial : Iteration.State) (k n : ℕ) (hk : 0 < k) (hkb : k ≤ b)
    (hlevels : ∀ i < k, 2 * k * oneLevelBound (runParameters G c b initial i) < n) :
    ∀ j ≤ k, 2 * k * ((runParameters G c b initial j).cost + j) < n := by
  intro j hj
  cases j with
  | zero =>
    exact (Nat.mul_le_mul_left _ (current_budget_bound _ 0 (Nat.zero_le _))).trans_lt
      (hlevels 0 hk)
  | succ j =>
    rw [runParameters_succ]
    exact (Nat.mul_le_mul_left _ (next_budget_bound _ _ (j + 1)
      (show j + 1 ≤ b from hj.trans hkb))).trans_lt (hlevels j (by omega))

/-- The final truth table, as well as every preceding one, has fewer than
`2^(n/k)` entries in the equivalent integer-power formulation. This does not
assert a materialization-time bound. -/
theorem run_indexing_table_size_beyond_cutoff (G : EndpointGraph V E) (c A d n k : ℕ)
    (hk : 0 < k) (hcut : sourceCutoff c A d k ≤ n)
    (hv : Fintype.card V ≤ 2 * Fintype.card E)
    (hlower : n ≤ Fintype.card E)
    (hupper : Fintype.card E ≤ A * n * sourceDepth n ^ d) :
    ∀ j ≤ k,
      let p := runParameters G c (sourceDepth n) (Iteration.seedState (sourceDepth n)) j
      2 * k * max 1 (namingLength p) < n ∧ (p.rows * p.columns) ^ k < 2 ^ n := by
  have hlevels := run_indexing_beyond_cutoff G c A d n k hcut hv hlower hupper
  have hnames := run_naming_small G c (sourceDepth n)
    (Iteration.seedState (sourceDepth n)) k n hk hv (fun i hi => (hlevels i hi).2)
  intro j hj
  exact ⟨hnames j hj, entry_count_of_naming_bound _ _ _ _ (le_refl _) (hnames j hj)⟩

theorem run_indexing_budget_beyond_cutoff (G : EndpointGraph V E) (c A d n k : ℕ)
    (hk : 0 < k) (hcut : sourceCutoff c A d k ≤ n)
    (hv : Fintype.card V ≤ 2 * Fintype.card E)
    (hlower : n ≤ Fintype.card E)
    (hupper : Fintype.card E ≤ A * n * sourceDepth n ^ d) :
    ∀ j ≤ k,
      2 * k * ((runParameters G c (sourceDepth n) (Iteration.seedState (sourceDepth n)) j).cost
        + j) < n := by
  have hn : 2 ≤ n := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hcut
  have hthreshold : sourceThreshold (cutoffScale c A d k) ≤ n :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans hcut
  have htest := cutoffTest_persistent (cutoffScale_spec c A d k 0 hk)
    (sourceLog_ge_of_threshold hthreshold)
  apply run_budget_small G c (sourceDepth n) (Iteration.seedState (sourceDepth n)) k n hk
    (test_level_le_sourceDepth hn htest)
  exact fun i hi => (run_indexing_beyond_cutoff G c A d n k hcut hv hlower hupper i hi).2

end LiteralStep

end EthInapproximability.CurrentPaper.EffectiveIteration
