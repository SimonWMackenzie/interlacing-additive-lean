import EthInapproximability.CurrentPaper.ExactCoordinateControl
import EthInapproximability.CurrentPaper.ExactSampledTests

/-!
# Coordinate separation in the exact reduction

Source: v8 `E-exact-details.tex`, `lem:exact-structure`. Small-width tests
come from indexed projection and the two-bound row ladder. Larger tests
come from scalar stopping, and the excess-block tests are proved by the
actual first-message induction. Only explicit numerical cutoff inequalities
remain inputs; no sampled restriction or protocol-control conclusion is an
assumption.
-/

namespace EthInapproximability.CurrentPaper.ExactCoordinateSeparation

open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace
open Workspace.Types.Protocol
open ProtocolSeparation TerminalExcess

private theorem rowScale_le {x : ℝ} {n m : ℕ} (hx : 0 ≤ x)
    (hn : n ≤ m) (hm : (2 : ℝ) ^ m * x ≤ 1) :
    (2 : ℝ) ^ n * x ≤ 1 :=
  (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) hx).trans hm

private theorem powerFactor {a b : ℕ} (hab : b ≤ a) :
    2 ^ (a - b) * 2 ^ b = (2 : ℕ) ^ a := by
  rw [← pow_add, Nat.sub_add_cancel hab]

private theorem oddFactor {a m : ℕ} (hm : 1 ≤ m) (hma : m ≤ a) :
    2 ^ (a - m) * 2 ^ (m - 1) = (2 : ℕ) ^ (a - 1) := by
  rw [← pow_add]
  congr 1
  omega

/-- The three restriction-test families used by coordinate separation,
proved from the sampled family, one-copy bounds and explicit scalar gates.
The conclusion is independent of a chosen protocol or retained rectangle,
so it also applies to the actual suffixes of the exact construction. -/
theorem coordinateTests {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq Y] [Nonempty X] [Nonempty Y]
    (f : X → Y → Bool) {H m k N T₀ τ : ℕ} {x h ε yzero σ a₀ : ℝ}
    (hH : 2 ≤ H) (hm : 2 ^ 20 ≤ m) (hmk : m ≤ k)
    (hx : 0 < x) (hscale : (2 : ℝ) ^ m * x ≤ 1)
    (hε : 0 ≤ ε) (hh : 0 < h) (hσ : 0 ≤ σ) (ha₀ : 0 ≤ a₀)
    (h1 : H ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (3 / 5)))
    (h2 : H - 1 ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (3 / 10)))
    (hone : 1 ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x yzero))
    (S : Fin N → Fin (2 ^ k) → Y) (hS : IsBalancedFamily (2 ^ m) S ε)
    (hgateOne : yzero ≤ yLoss ε (2 ^ m) h (H + ((k - m) + m)))
    (hgateSeed : HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
      h * (2 : ℝ) ^ (-((H + m : ℕ) : ℝ)) / (1 + ε))
    (hhalf : h ≤ σ / 2) (hproject : (1 + ε) * (3 / 5 : ℝ) ^ 2 ≤ σ / 2)
    (hsmallRow : ∀ j, j < k → k - j ≤ m →
      ⌈(Fintype.card X : ℝ) * ((2 : ℝ) ^ (k - j) * x)⌉₊ ≤ rowThreshold T₀ j)
    (hsmallOddRow : ∀ j, j + 1 < k → k - j ≤ m →
      ⌈(Fintype.card X : ℝ) * ((2 : ℝ) ^ (k - j) * x)⌉₊ ≤
        rowThreshold T₀ (j + 1))
    (hlargeRow : ∀ j, j < k → m ≤ k - j →
      ⌈(2 : ℝ) ^ (k - j) * x * (Fintype.card X : ℝ)⌉₊ ≤ rowThreshold T₀ j)
    (hbaseRow : ⌈(Fintype.card X : ℝ) * ((2 : ℝ) ^ m * x)⌉₊ ≤
      excessRows (Fintype.card X) a₀ 0)
    (hexcessRow : ∀ ell, ell < k - m →
      ⌈(2 : ℝ) ^ (ell + m) * x * (Fintype.card X : ℝ)⌉₊ ≤
        excessRows (Fintype.card X) a₀ (ell + 1))
    (hexcessFinal : ∀ j, j + 1 < k → m < k - j →
      excessRows (Fintype.card X) a₀ (k - j - m) ≤ rowThreshold T₀ (j + 1))
    (hpairRow : ⌈(Fintype.card X : ℝ) * (2 * x)⌉₊ ≤ τ)
    : (∀ j, j < k → BlockLowerBound (relaxedInterlace f S)
        Prod.fst Finset.univ (2 ^ (k - j)) (rowThreshold T₀ j)
        (σ / 2) (H + (k - j))) ∧
      (∀ j, j + 1 < k → BlockLowerBound (relaxedInterlace f S)
        Prod.fst Finset.univ (2 ^ (k - j - 1) + 1) (rowThreshold T₀ (j + 1))
        σ (H + (k - j))) ∧
      BlockLowerBound (relaxedInterlace f S) Prod.fst Finset.univ
        2 τ σ (H + 1) := by
  classical
  have hm1 : 1 ≤ m := by omega
  have hwidth : 2 ^ k = 2 ^ (k - m) * 2 ^ m := (powerFactor hmk).symm
  have hpBound := (HardSeed.copyCount_bounds (show 5 ≤ m by omega)).2.2
  have hhalfSeed : H - 1 ≤ Dfamily (interlaceFun f 1)
      (bracketGE X Y 1 x ((3 / 5 : ℝ) / 2)) := by
    convert h2 using 1
    norm_num
  have hprojectFull : (1 + ε) * (3 / 5 : ℝ) ^ 2 ≤ σ :=
    hproject.trans (half_le_self hσ)
  have hcoord (ell p T : ℕ) (he : ell ≤ k - m)
      (hp : 2 ^ ell * HardSeed.copyCount m ≤ p)
      (hT : ⌈(2 : ℝ) ^ (ell + m) * x * (Fintype.card X : ℝ)⌉₊ ≤ T) :
      BlockLowerBound (relaxedInterlace f S) Prod.fst Finset.univ p T
        (σ / 2) (H + (ell + m)) := by
    apply ExactCoordinateControl.coordinateBlockLowerBound_of_width f hwidth
      hH hm hx hscale hε hh h1 h2 hone S hS hgateOne hgateSeed
      0 ell p T (by omega) he hp hT
    simpa using hhalf
  have hBob : ∀ j, j < k → BlockLowerBound (relaxedInterlace f S)
      Prod.fst Finset.univ (2 ^ (k - j)) (rowThreshold T₀ j)
      (σ / 2) (H + (k - j)) := by
    intro j hj
    by_cases hn : k - j ≤ m
    · exact ExactSampledTests.powerOfTwoTest f hH hx (by norm_num) (by norm_num)
        h1 hhalfSeed (by omega) (pow_le_pow_right₀ (by omega) hn) hS hε
        (rowScale_le hx.le hn hscale) (hsmallRow j hj hn) hproject
    · have hn' : m ≤ k - j := by omega
      have hmul : 2 ^ (k - j - m) * 2 ^ m = 2 ^ (k - j) := powerFactor hn'
      have hh' := hcoord (k - j - m) (2 ^ (k - j)) (rowThreshold T₀ j)
        (by omega) (by rw [← hmul]; exact Nat.mul_le_mul_left _ hpBound)
        (by simpa [Nat.sub_add_cancel hn'] using hlargeRow j hj hn')
      simpa [Nat.sub_add_cancel hn'] using hh'
  have hbase : BlockLowerBound (relaxedInterlace f S) Prod.fst Finset.univ
      (2 ^ (m - 1) + 1) (excessRows (Fintype.card X) a₀ 0) σ (H + m) := by
    apply ExactSampledTests.oddBlockTest f hH hx (by norm_num) (by norm_num)
      h1 hhalfSeed hm1 _ hS hε hscale hbaseRow hprojectFull
    have hp : 1 ≤ (2 : ℕ) ^ (m - 1) := Nat.one_le_pow _ _ (by omega)
    have heq : (2 : ℕ) ^ m = 2 * 2 ^ (m - 1) := by
      rw [← Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel hm1]
    omega
  have hexcessHalf : ∀ ell < k - m,
      BlockLowerBound (relaxedInterlace f S) Prod.fst Finset.univ
        (excessWidth (2 ^ (m - 1)) (ell + 1))
        (excessRows (Fintype.card X) a₀ (ell + 1)) (σ / 2) ((H + m) + ell) := by
    intro ell he
    have hmul : 2 ^ (ell + 1) * 2 ^ (m - 1) = 2 ^ ell * 2 ^ m := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    have hh' := hcoord ell (excessWidth (2 ^ (m - 1)) (ell + 1))
      (excessRows (Fintype.card X) a₀ (ell + 1)) (by omega)
      (by unfold excessWidth; rw [hmul]; exact
        (Nat.mul_le_mul_left _ hpBound).trans (Nat.le_add_right _ _))
      (hexcessRow ell he)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh'
  have hexcess := TerminalExcess.excessBlocks (relaxedInterlace f S) Prod.fst
    Finset.univ (Fintype.card X) (2 ^ (m - 1)) (H + m) (k - m) a₀ σ
    (by omega) ha₀ hbase hexcessHalf
  have hAlice : ∀ j, j + 1 < k → BlockLowerBound (relaxedInterlace f S)
      Prod.fst Finset.univ (2 ^ (k - j - 1) + 1) (rowThreshold T₀ (j + 1))
      σ (H + (k - j)) := by
    intro j hj
    by_cases hn : k - j ≤ m
    · apply ExactSampledTests.oddBlockTest f hH hx (by norm_num) (by norm_num)
        h1 hhalfSeed (by omega) _ hS hε (rowScale_le hx.le hn hscale)
        (hsmallOddRow j hj hn) hprojectFull
      have hp : 1 ≤ (2 : ℕ) ^ (k - j - 1) := Nat.one_le_pow _ _ (by omega)
      have heq : (2 : ℕ) ^ (k - j) = 2 * 2 ^ (k - j - 1) := by
        rw [← Nat.pow_succ', Nat.succ_eq_add_one,
          Nat.sub_add_cancel (show 1 ≤ k - j by omega)]
      have hb : (2 : ℕ) ^ (k - j) ≤ 2 ^ m := pow_le_pow_right₀ (by omega) hn
      omega
    · have hn' : m < k - j := by omega
      have hh' := hexcess (k - j - m) (by omega)
      have hp : excessWidth (2 ^ (m - 1)) (k - j - m) =
          2 ^ (k - j - 1) + 1 := by
        unfold excessWidth
        rw [oddFactor hm1 (Nat.le_of_lt hn')]
      rw [hp] at hh'
      have hc : (H + m) + (k - j - m) = H + (k - j) := by omega
      rw [hc] at hh'
      intro R C Q hcsub hcden hq hr
      apply hh' R C Q hcsub hcden hq
      intro i hi
      exact (hexcessFinal j hj hn').trans (hr i hi)
  have hxhalf : x ≤ 1 / 2 := by
    have hh' := rowScale_le hx.le hm1 hscale
    norm_num at hh'
    linarith
  have hpair := ExactSampledTests.twoCopyTest f hH hx hxhalf (by norm_num)
    (by norm_num) h1 hhalfSeed (by
      simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hm1))
    hS hε hpairRow hprojectFull
  exact ⟨hBob, hAlice, hpair⟩

/-- Full message-order and no-waste conclusion for the actual sampled
coordinate matrix. The final block/routing conclusion has no oracle premise:
all three families of first-message tests are supplied by `coordinateTests`. The numerical
row gates are written as ceilings so the cutoff can discharge them directly. -/
theorem coordinateSeparation {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq Y] [Nonempty X] [Nonempty Y]
    (f : X → Y → Bool) {H m k N T₀ τ : ℕ} {x h ε yzero σ a₀ : ℝ}
    (hH : 2 ≤ H) (hm : 2 ^ 20 ≤ m) (hmk : m ≤ k)
    (hx : 0 < x) (hscale : (2 : ℝ) ^ m * x ≤ 1)
    (hε : 0 ≤ ε) (hh : 0 < h) (hσ : 0 ≤ σ) (ha₀ : 0 ≤ a₀)
    (h1 : H ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (3 / 5)))
    (h2 : H - 1 ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (3 / 10)))
    (hone : 1 ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x yzero))
    (S : Fin N → Fin (2 ^ k) → Y) (hS : IsBalancedFamily (2 ^ m) S ε)
    (hgateOne : yzero ≤ yLoss ε (2 ^ m) h (H + ((k - m) + m)))
    (hgateSeed : HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
      h * (2 : ℝ) ^ (-((H + m : ℕ) : ℝ)) / (1 + ε))
    (hhalf : h ≤ σ / 2) (hproject : (1 + ε) * (3 / 5 : ℝ) ^ 2 ≤ σ / 2)
    (hsmallRow : ∀ j, j < k → k - j ≤ m →
      ⌈(Fintype.card X : ℝ) * ((2 : ℝ) ^ (k - j) * x)⌉₊ ≤ rowThreshold T₀ j)
    (hsmallOddRow : ∀ j, j + 1 < k → k - j ≤ m →
      ⌈(Fintype.card X : ℝ) * ((2 : ℝ) ^ (k - j) * x)⌉₊ ≤
        rowThreshold T₀ (j + 1))
    (hlargeRow : ∀ j, j < k → m ≤ k - j →
      ⌈(2 : ℝ) ^ (k - j) * x * (Fintype.card X : ℝ)⌉₊ ≤ rowThreshold T₀ j)
    (hbaseRow : ⌈(Fintype.card X : ℝ) * ((2 : ℝ) ^ m * x)⌉₊ ≤
      excessRows (Fintype.card X) a₀ 0)
    (hexcessRow : ∀ ell, ell < k - m →
      ⌈(2 : ℝ) ^ (ell + m) * x * (Fintype.card X : ℝ)⌉₊ ≤
        excessRows (Fintype.card X) a₀ (ell + 1))
    (hexcessFinal : ∀ j, j + 1 < k → m < k - j →
      excessRows (Fintype.card X) a₀ (k - j - m) ≤ rowThreshold T₀ (j + 1))
    (hpairRow : ⌈(Fintype.card X : ℝ) * (2 * x)⌉₊ ≤ τ)
    (hτ : 1 ≤ τ) (hgap : 2 ^ k * τ < T₀)
    (Rs : Finset (Fin (2 ^ k) × X)) (Cs : Finset (Fin N))
    (P : Protocol (Fin (2 ^ k) × X) (Fin N) Bool)
    (hCs : Cs.Nonempty) (hCsden : σ * (N : ℝ) ≤ Cs.card)
    (hRs : IsEquipartitionedGE Rs Finset.univ T₀)
    (hcost : P.cost ≤ H + k)
    (hcomp : ∀ a ∈ Rs, ∀ c ∈ Cs, P.eval a c = relaxedInterlace f S a c) :
    Protocol.FirstKRowBitsOn Rs Cs k P ∧
    NoWasteConclusion (Finset.univ : Finset (Fin (2 ^ k))) Rs
      (Protocol.prefixCodeRaw k P) T₀ τ ∧
    ∀ j, (Rs.filter (fun a => Protocol.prefixCodeRaw k P a = j)).Nonempty := by
  obtain ⟨hBob, hAlice, hpair⟩ := coordinateTests f hH hm hmk hx hscale
    hε hh hσ ha₀ h1 h2 hone S hS hgateOne hgateSeed hhalf hproject
    hsmallRow hsmallOddRow hlargeRow hbaseRow hexcessRow hexcessFinal hpairRow
  exact twoTestRigidity k H T₀ τ (relaxedInterlace f S) Finset.univ σ
    (by omega) hσ hBob hAlice hpair hτ hgap Rs Cs P hCs (Finset.subset_univ _)
    (by simpa using hCsden) hRs hcost hcomp

end EthInapproximability.CurrentPaper.ExactCoordinateSeparation
