import EthInapproximability.CurrentPaper.ExactGap
import EthInapproximability.CurrentPaper.ExactFirstProfiles
import EthInapproximability.CurrentPaper.ExactSecondProfiles
import EthInapproximability.CurrentPaper.ExactCoordinateSeparation

/-!
# The finite exact reduction from balanced families and numerical gates

Source: v8 `03-exact-hardness.tex`, `E-exact-details.tex`, and
`G-exact-control.tex`. Every communication lower bound and message-control
test is proved internally. The input record contains only natural/real
parameters and explicitly displayed numerical inequalities. The actual two
labelled families and their balance proofs are supplied separately.

This is a finite theorem. It does not choose parameters, construct a sampler,
assert an algorithmic running time, or formalise the external source-hardness
theorem. Those obligations remain outside this statement.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.ExactFiniteReduction

open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace
open ExactConstruction ProtocolSeparation

/-- The explicit scalar gates consumed by the finite proof. No field mentions
communication cost, a restriction bound, or a protocol. `m₁` and `m₂` are
logarithmic stopping widths, and `R₁` is the first residual-width exponent. -/
structure NumericParameters where
  a : ℕ
  r : ℕ
  N₁ : ℕ
  N₂ : ℕ
  t₁ : ℕ
  m₁ : ℕ
  R₁ : ℕ
  p₁ : ℕ
  m₂ : ℕ
  τ : ℕ
  xIndex : ℝ
  yIndex : ℝ
  hIndex : ℝ
  zIndex : ℝ
  x : ℝ
  h : ℝ
  ε : ℝ
  yzero : ℝ
  a₀ : ℝ
  ha : 2 ≤ a
  haeq : a = m₁ + R₁
  hR₁ : 1 ≤ R₁
  hwidth : width a = 2 ^ R₁ * t₁
  ht₁ : 0 < t₁
  hm₁ : 1 ≤ m₁
  hlocalOrder : a + 2 ≤ t₁
  hxIndex : 0 < xIndex
  hxIndexOne : xIndex ≤ 1
  hyIndex : 1 / 2 < yIndex
  hyIndexOne : yIndex ≤ 1
  hhIndex : 0 < hIndex
  hzIndexOne : zIndex ≤ 1
  hε : 0 ≤ ε
  hpLow : t₁ ≤ 2 * p₁
  hpHigh : p₁ ≤ t₁
  hpFraction : 16 * p₁ = 9 * t₁
  hw : 128 ≤ width a
  hindexRank : 2 ^ (2 ^ (m₁ - 1)) < ⌈(2 : ℝ) ^ p₁ * zIndex⌉₊
  hindexOne : yIndex ≤ yLoss ε t₁ hIndex (R₁ + (m₁ + 1))
  hindexSeed : zIndex ≤ hIndex * (2 : ℝ) ^ (-((m₁ + 1 : ℕ) : ℝ)) / (1 + ε)
  hindexRows : (2 : ℝ) ^ R₁ * xIndex ≤ 1
  hindexDensity : hIndex ≤ x
  hx : 0 < x
  hxOne : x ≤ 1
  hyzeroOne : yzero ≤ 1
  hnonconstantRows : ((p₁ + 2 : ℕ) : ℝ) ≤ yzero * (width a : ℝ)
  hm₂ : 2 ^ 20 ≤ m₂
  hResidual : m₂ + 1 ≤ r
  hscale : (2 : ℝ) ^ m₂ * x ≤ 1
  hh : 0 < h
  hσ : 0 ≤ 1 - 8 * h
  ha₀ : 0 ≤ a₀
  hcoordinateOne : yzero ≤ yLoss ε (2 ^ m₂) h (a + 1 + r)
  hcoordinateSeed : HardSeed.columnDensity ((2 : ℝ) ^ m₂) ≤
    h * (2 : ℝ) ^ (-((a + 1 + m₂ : ℕ) : ℝ)) / (1 + ε)
  hcoordinateSmall : (2 : ℝ) ^ r * x < 1
  hcoordinateFull : 2 ^ (r - m₂) * HardSeed.copyCount m₂ ≤
    ⌈(2 : ℝ) ^ r * ((3 / 5 : ℝ) - (2 : ℝ) ^ r * x) /
      (1 - (2 : ℝ) ^ r * x)⌉₊
  hcoordinateHalf : 2 ^ (r - m₂ - 1) * HardSeed.copyCount m₂ ≤
    ⌈(2 : ℝ) ^ r * ((3 / 10 : ℝ) - (2 : ℝ) ^ (r - 1) * x) /
      (1 - (2 : ℝ) ^ (r - 1) * x)⌉₊
  hhalf : h ≤ (1 - 8 * h) / 2
  hproject : (1 + ε) * (3 / 5 : ℝ) ^ 2 ≤ (1 - 8 * h) / 2
  hsmallRow : ∀ j, j < r → r - j ≤ m₂ →
    ⌈(N₁ : ℝ) * ((2 : ℝ) ^ (r - j) * x)⌉₊ ≤ rowThreshold N₁ j
  hsmallOddRow : ∀ j, j + 1 < r → r - j ≤ m₂ →
    ⌈(N₁ : ℝ) * ((2 : ℝ) ^ (r - j) * x)⌉₊ ≤ rowThreshold N₁ (j + 1)
  hlargeRow : ∀ j, j < r → m₂ ≤ r - j →
    ⌈(2 : ℝ) ^ (r - j) * x * (N₁ : ℝ)⌉₊ ≤ rowThreshold N₁ j
  hbaseRow : ⌈(N₁ : ℝ) * ((2 : ℝ) ^ m₂ * x)⌉₊ ≤
    TerminalExcess.excessRows N₁ a₀ 0
  hexcessRow : ∀ ell, ell < r - m₂ →
    ⌈(2 : ℝ) ^ (ell + m₂) * x * (N₁ : ℝ)⌉₊ ≤
      TerminalExcess.excessRows N₁ a₀ (ell + 1)
  hexcessFinal : ∀ j, j + 1 < r → m₂ < r - j →
    TerminalExcess.excessRows N₁ a₀ (r - j - m₂) ≤ rowThreshold N₁ (j + 1)
  hpairRow : ⌈(N₁ : ℝ) * (2 * x)⌉₊ ≤ τ
  hτ : 1 ≤ τ
  hgap : 2 ^ r * τ < N₁
  hbin : 4 * ExactBinControl.densityThreshold N₂ h < N₂
  hbinLoss : (3 : ℝ) * ExactBinControl.densityThreshold N₂ h ≤ 8 * h * N₂
  hsurvive : ((3 * ExactBinControl.densityThreshold N₂ h : ℕ) : ℝ) <
    (1 - ε) * (N₂ : ℝ) / (width a : ℝ)
  hdensity : (1 + ε) * N₁ / 2 < ((N₁ - (2 ^ r - 1) * τ : ℕ) : ℝ)

/-- Both first-matrix profiles and the weaker early-leaf nonconstancy bound
come from residual indexing. The latter uses residual width exponent zero. -/
theorem first_inputs (p : NumericParameters) (C₁ : FirstFamily p.a p.N₁)
    (hC₁ : IsBalancedFamily p.t₁ C₁ p.ε) :
    p.a + 1 ≤ Dfamily (interlaceFun (ExactFirstProfiles.firstTranspose p.ha C₁) 1)
      (bracketGE (Fin p.N₁) (Fin (width p.a)) 1 p.x (3 / 5)) ∧
    p.a ≤ Dfamily (interlaceFun (ExactFirstProfiles.firstTranspose p.ha C₁) 1)
      (bracketGE (Fin p.N₁) (Fin (width p.a)) 1 p.x (3 / 10)) ∧
    1 ≤ Dfamily (interlaceFun (ExactFirstProfiles.firstTranspose p.ha C₁) 1)
      (bracketGE (Fin p.N₁) (Fin (width p.a)) 1 p.x p.yzero) := by
  obtain ⟨hfull, hhalf⟩ := ExactFirstProfiles.profile_row_gates
    p.hw p.hR₁ p.hwidth p.hpFraction
  obtain ⟨_, h1, h2⟩ := ExactFirstProfiles.transpose_profiles p.ha C₁ hC₁.1
    p.haeq p.hR₁ p.hwidth hC₁ p.ht₁ p.hm₁ p.hxIndex p.hxIndexOne
    p.hyIndex p.hyIndexOne p.hhIndex p.hε p.hzIndexOne p.hpLow p.hpHigh
    p.hindexRank p.hindexOne p.hindexSeed p.hindexRows p.hindexDensity p.hxOne hfull hhalf
  have hone := ExactFirstProfiles.transpose_oneCopy_lower p.ha C₁ hC₁.1
    p.hwidth hC₁ p.ht₁ p.hm₁ p.hxIndex p.hxIndexOne p.hyIndex p.hyIndexOne
    p.hhIndex p.hε p.hzIndexOne p.hpLow p.hpHigh p.hindexRank p.hindexOne p.hindexSeed
    0 (Nat.zero_le _) (by simpa using p.hxIndexOne) p.hindexDensity p.hxOne
    p.hyzeroOne (by simpa using p.hnonconstantRows)
  exact ⟨h1, h2, (by omega : 1 ≤ p.m₁ + 1 + 0).trans hone⟩

/-- Both bin-separation inputs for the literal second transpose, derived
from the two supplied balanced families and the scalar record. -/
theorem second_inputs (p : NumericParameters) (C₁ : FirstFamily p.a p.N₁)
    (C₂ : SecondFamily p.a (2 ^ p.r) p.N₂)
    (hC₁ : IsBalancedFamily p.t₁ C₁ p.ε)
    (hC₂ : IsBalancedFamily (2 ^ p.m₂) C₂ p.ε) :
    p.a + 1 + p.r ≤ Dfamily
      (interlaceFun (fun z x => secondMatrix p.ha C₁ C₂ x z) 1)
      (bracketGE (Fin p.N₂) (Fin (2 ^ p.r) × Fin p.N₁) 1 p.h (3 / 5)) ∧
    p.a + 1 + p.r - 1 ≤ Dfamily
      (interlaceFun (fun z x => secondMatrix p.ha C₁ C₂ x z) 1)
      (bracketGE (Fin p.N₂) (Fin (2 ^ p.r) × Fin p.N₁) 1 p.h ((3 / 5) / 2)) := by
  obtain ⟨h1, h2, hone⟩ := first_inputs p C₁ hC₁
  have hmk : p.m₂ ≤ p.r := by have := p.hResidual; omega
  have hr : p.r - p.m₂ + p.m₂ = p.r := Nat.sub_add_cancel hmk
  have hrHalf : p.r - p.m₂ - 1 + p.m₂ = p.r - 1 := by
    have := p.hResidual
    omega
  have hwidth : 2 ^ p.r = 2 ^ (p.r - p.m₂) * 2 ^ p.m₂ := by
    rw [← pow_add, hr]
  have h2' : p.a + 1 - 1 ≤ Dfamily
      (interlaceFun (fun ℓ i => duplicatedFirstMatrix p.ha C₁ i ℓ) 1)
      (bracketGE (Fin p.N₁) (Fin (width p.a)) 1 p.x (3 / 10)) := by
    simpa only [Nat.add_sub_cancel] using h2
  have hfull := ExactSecondProfiles.transpose_profiles p.ha hC₁.1 C₁ C₂
    hwidth (by have := p.ha; omega) p.hm₂ p.hx p.hscale p.hε p.hh
    h1 h2' hone hC₂
    (by simpa only [hr] using p.hcoordinateOne) p.hcoordinateSeed hC₂.1
    (by have := p.hResidual; omega) (by have := p.hσ; linarith)
    (by simpa only [hr] using p.hcoordinateSmall)
    (by simpa only [hr, Nat.cast_pow, Nat.cast_ofNat] using p.hcoordinateFull)
    (by simpa only [hrHalf, Nat.cast_pow, Nat.cast_ofNat] using p.hcoordinateHalf)
  constructor
  · simpa only [hr, ExactSecondProfiles.secondTranspose] using hfull.1
  · simpa only [hr, ExactSecondProfiles.secondTranspose,
      show (3 / 5 : ℝ) / 2 = 3 / 10 by norm_num] using hfull.2

/-- All three concrete coordinate tests are internal consequences. The
scalar record's ceiling inequalities keep the original row thresholds. -/
theorem coordinate_inputs (p : NumericParameters) (C₁ : FirstFamily p.a p.N₁)
    (C₂ : SecondFamily p.a (2 ^ p.r) p.N₂)
    (hC₁ : IsBalancedFamily p.t₁ C₁ p.ε)
    (hC₂ : IsBalancedFamily (2 ^ p.m₂) C₂ p.ε) :
    (∀ j, j < p.r → BlockLowerBound (secondMatrix p.ha C₁ C₂) Prod.fst Finset.univ
      (2 ^ (p.r - j)) (rowThreshold p.N₁ j) ((1 - 8 * p.h) / 2)
      (p.a + 1 + (p.r - j))) ∧
    (∀ j, j + 1 < p.r → BlockLowerBound (secondMatrix p.ha C₁ C₂) Prod.fst Finset.univ
      (2 ^ (p.r - j - 1) + 1) (rowThreshold p.N₁ (j + 1)) (1 - 8 * p.h)
      (p.a + 1 + (p.r - j))) ∧
    BlockLowerBound (secondMatrix p.ha C₁ C₂) Prod.fst Finset.univ
      2 p.τ (1 - 8 * p.h) (p.a + 1 + 1) := by
  letI : NeZero p.N₁ := ⟨Nat.ne_of_gt hC₁.1⟩
  letI : Nonempty (Fin (width p.a)) := ⟨⟨0, by unfold width; positivity⟩⟩
  obtain ⟨h1, h2, hone⟩ := first_inputs p C₁ hC₁
  have hr : p.r - p.m₂ + p.m₂ = p.r :=
    Nat.sub_add_cancel (by have := p.hResidual; omega)
  exact ExactCoordinateSeparation.coordinateTests
    (ExactFirstProfiles.firstTranspose p.ha C₁)
    (by have := p.ha; omega) p.hm₂ (by have := p.hResidual; omega)
    p.hx p.hscale p.hε p.hh p.hσ p.ha₀ h1
    (by simpa only [Nat.add_sub_cancel] using h2) hone C₂ hC₂
    (by simpa only [hr] using p.hcoordinateOne) p.hcoordinateSeed p.hhalf p.hproject
    (by simpa only [Fintype.card_fin] using p.hsmallRow)
    (by simpa only [Fintype.card_fin] using p.hsmallOddRow)
    (by simpa only [Fintype.card_fin] using p.hlargeRow)
    (by simpa only [Fintype.card_fin] using p.hbaseRow)
    (by simpa only [Fintype.card_fin] using p.hexcessRow)
    (by simpa only [Fintype.card_fin] using p.hexcessFinal)
    (by simpa only [Fintype.card_fin] using p.hpairRow)

/-- The finite exact gap on the literal graph matrix. Its hypotheses contain
only explicit scalar gates, balanced labelled families, and the source edge
list. Every communication profile, test, and actual protocol transfer is
proved in the dependency chain consumed here. -/
theorem finite_gap (p : NumericParameters) (C₁ : FirstFamily p.a p.N₁)
    (C₂ : SecondFamily p.a (2 ^ p.r) p.N₂)
    (hC₁ : IsBalancedFamily p.t₁ C₁ p.ε)
    (hC₂ : IsBalancedFamily (2 ^ p.m₂) C₂ p.ε)
    {n d : ℕ} (e : Fin d → Fin 2 → Fin n)
    (hD : 5 * d ≤ 2 ^ p.r) (hinj : ∀ α, Function.Injective (e α)) :
    (∀ colour : Fin n → Fin 4,
      (∀ α : Fin d, colour (e α 0) ≠ colour (e α 1)) →
      D (matrix p.ha C₁ C₂ (sourceVectors (2 ^ p.r) e) (sourceVectors_cap (2 ^ p.r) e)) =
        p.a + 1 + p.r + 2) ∧
    ((∀ colour : Fin n → Fin 4,
      ∃ α : Fin d, colour (e α 0) = colour (e α 1)) →
      D (matrix p.ha C₁ C₂ (sourceVectors (2 ^ p.r) e) (sourceVectors_cap (2 ^ p.r) e)) =
        p.a + 1 + p.r + 3) := by
  obtain ⟨h1, h2⟩ := second_inputs p C₁ C₂ hC₁ hC₂
  obtain ⟨hBob, hAlice, hpair⟩ := coordinate_inputs p C₁ C₂ hC₁ hC₂
  constructor
  · intro colour hproper
    exact ExactGap.source_yes_cost p.ha C₁ C₂ hC₁ hC₂ p.hh p.hσ h1 h2 e colour hproper
  · intro hbad
    exact ExactGap.source_no_cost p.ha C₁ C₂ hC₁ p.hlocalOrder hC₂
      (by have := pow_pos (by decide : 0 < (2 : ℕ)) p.m₂; omega)
      p.hh p.hσ h1 h2 p.hbin p.hbinLoss
      p.hsurvive p.hτ p.hgap hBob hAlice hpair p.hdensity e hD hinj hbad

/-- The same finite reduction as a decision equivalence. This is not a
polynomial-time reduction theorem: supplied families and scalar witnesses
must still be produced with the claimed effective size bounds. -/
theorem decision_equivalence (p : NumericParameters) (C₁ : FirstFamily p.a p.N₁)
    (C₂ : SecondFamily p.a (2 ^ p.r) p.N₂)
    (hC₁ : IsBalancedFamily p.t₁ C₁ p.ε)
    (hC₂ : IsBalancedFamily (2 ^ p.m₂) C₂ p.ε)
    {n d : ℕ} (e : Fin d → Fin 2 → Fin n)
    (hD : 5 * d ≤ 2 ^ p.r) (hinj : ∀ α, Function.Injective (e α)) :
    D (matrix p.ha C₁ C₂ (sourceVectors (2 ^ p.r) e) (sourceVectors_cap (2 ^ p.r) e)) ≤
      p.a + 1 + p.r + 2 ↔
    ∃ colour : Fin n → Fin 4, ∀ α : Fin d, colour (e α 0) ≠ colour (e α 1) := by
  classical
  obtain ⟨hyes, hno⟩ := finite_gap p C₁ C₂ hC₁ hC₂ e hD hinj
  constructor
  · intro hcost
    by_contra hbad
    push Not at hbad
    have := hno hbad
    omega
  · rintro ⟨colour, hproper⟩
    exact (hyes colour hproper).le

end EthInapproximability.CurrentPaper.ExactFiniteReduction
