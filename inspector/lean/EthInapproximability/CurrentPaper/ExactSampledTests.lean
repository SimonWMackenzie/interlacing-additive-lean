import EthInapproximability.CurrentPaper.IndexedProjection
import EthInapproximability.CurrentPaper.ProtocolSeparation

/-!
# Sampled coordinate tests for the exact reduction

Source: v8, `E-exact-details.tex`, proof of `lem:exact-structure`.
The small-width cases are genuine restrictions of the indexed sampled
matrix. Balanced projection accounts for all original labels before the
current two-bound row ladder supplies the classical lower bound.

These lemmas do not assume the protocol-control tests they establish. The
inputs are the two one-copy lower bounds, the actual indexed-family balance,
and the displayed numerical row and column gates. The stopping argument for
widths larger than the balance order is a separate part of the proof.
-/

namespace EthInapproximability.CurrentPaper.ExactSampledTests

open NPCC
open Workspace.Types.CommComplexity Workspace.Types.Interlace
open ProtocolSeparation

/-- A classical restriction bound transfers to the actual sampled matrix,
on any specified set of at least `p` coordinate blocks. All column densities
refer to the complete original list of labels, including duplicate tuples. -/
theorem blockLowerBound_projection {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq Y]
    {q p t N T B : ℕ} (f : X → Y → Bool) {S : Fin N → Fin q → Y}
    {ε x z h : ℝ} (hp : 0 < p) (hpt : p ≤ t)
    (hS : IsBalancedFamily t S ε) (hε : 0 ≤ ε)
    (hrow : ⌈(Fintype.card X : ℝ) * x⌉₊ ≤ T)
    (hcol : (1 + ε) * z ≤ h)
    (hB : B ≤ Dfamily (interlaceFun f p) (bracketGE X Y p x z)) :
    BlockLowerBound (relaxedInterlace f S) Prod.fst Finset.univ p T h B := by
  classical
  apply blockLowerBound_of_exact
  intro R C Q _ hden hQ hR
  let e : Fin p ≃ {i // i ∈ Q} :=
    (Fintype.equivFinOfCardEq (by simpa using hQ)).symm
  have hrows : IsEquipartitionedGE R Q ⌈(Fintype.card X : ℝ) * x⌉₊ := by
    intro i hi
    exact hrow.trans (hR i hi)
  have hcols : ((1 + ε) * z) * (N : ℝ) ≤ C.card := by
    have hd : h * (N : ℝ) ≤ C.card := by simpa using hden
    exact (mul_le_mul_of_nonneg_right hcol (Nat.cast_nonneg N)).trans hd
  have hcost := IndexedProjection.balanced_projection_lower_bound f hp hpt
    hS hε e hrows hcols
  have heps : (1 + ε : ℝ) ≠ 0 := by linarith
  have hz : (1 + ε) * z / (1 + ε) = z := by field_simp
  rw [hz] at hcost
  exact hB.trans hcost

/-- A total row-population bound supplies the requisite coordinate blocks.
The row fraction is counted against the original block size, not against
the surviving rows. This is also applicable after transposing a restriction. -/
theorem lowerBound_of_total_rows {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq Y]
    {q p t N B : ℕ} (f : X → Y → Bool) {S : Fin N → Fin q → Y}
    {ε x z h : ℝ} (hp : 0 < p) (hpt : p ≤ t)
    (hS : IsBalancedFamily t S ε) (hε : 0 ≤ ε)
    (hx : 0 < x) (hx1 : x < 1) (hcol : (1 + ε) * z ≤ h)
    (hB : B ≤ Dfamily (interlaceFun f p) (bracketGE X Y p x z))
    (R : Finset (Fin q × X)) (C : Finset (Fin N))
    (hrows : p ≤ ⌈(q : ℝ) *
      ((R.card : ℝ) / ((q : ℝ) * (Fintype.card X : ℝ)) - x) / (1 - x)⌉₊)
    (hcols : h * (N : ℝ) ≤ C.card) :
    B ≤ D (subgame (relaxedInterlace f S) R C) := by
  classical
  obtain ⟨Q, hQ, hR⟩ := IndexedProjection.enough_good_blocks hx hx1 hp hrows
  have htest := blockLowerBound_projection f hp hpt hS hε (le_refl _) hcol hB
  apply htest R C Q (Finset.subset_univ _) (by simpa using hcols)
  · exact hQ.ge
  · exact hR

/-- Small-width half-column test: a power-of-two number of sampled blocks
inherits the certified classical row-doubling bound. -/
theorem powerOfTwoTest {X Y : Type*}
    [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y] [DecidableEq Y]
    {q t N T H k : ℕ} (f : X → Y → Bool) {S : Fin N → Fin q → Y}
    {ε x z h : ℝ} (hH : 2 ≤ H) (hx : 0 < x) (hz : 0 < z) (hz1 : z ≤ 1)
    (h1 : H ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x z))
    (h2 : H - 1 ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (z / 2)))
    (hk : 1 ≤ k) (hwidth : 2 ^ k ≤ t)
    (hS : IsBalancedFamily t S ε) (hε : 0 ≤ ε)
    (hscale : (2 : ℝ) ^ k * x ≤ 1)
    (hrow : ⌈(Fintype.card X : ℝ) * ((2 : ℝ) ^ k * x)⌉₊ ≤ T)
    (hcol : (1 + ε) * z ^ 2 ≤ h) :
    BlockLowerBound (relaxedInterlace f S) Prod.fst Finset.univ
      (2 ^ k) T h (H + k) := by
  apply blockLowerBound_projection f (by positivity) hwidth hS hε hrow hcol
  exact repeatedPowerOfTwo f hH hx hz hz1 h1 h2 k hk hscale

/-- The odd-block sampled test uses only one block more than half a power
of two. It retains the literal balanced-family labels throughout. -/
theorem oddBlockTest {X Y : Type*}
    [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y] [DecidableEq Y]
    {q t N T H k : ℕ} (f : X → Y → Bool) {S : Fin N → Fin q → Y}
    {ε x z h : ℝ} (hH : 2 ≤ H) (hx : 0 < x) (hz : 0 < z) (hz1 : z ≤ 1)
    (h1 : H ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x z))
    (h2 : H - 1 ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (z / 2)))
    (hk : 1 ≤ k) (hwidth : 2 ^ (k - 1) + 1 ≤ t)
    (hS : IsBalancedFamily t S ε) (hε : 0 ≤ ε)
    (hscale : (2 : ℝ) ^ k * x ≤ 1)
    (hrow : ⌈(Fintype.card X : ℝ) * ((2 : ℝ) ^ k * x)⌉₊ ≤ T)
    (hcol : (1 + ε) * z ^ 2 ≤ h) :
    BlockLowerBound (relaxedInterlace f S) Prod.fst Finset.univ
      (2 ^ (k - 1) + 1) T h (H + k) := by
  apply blockLowerBound_projection f (by positivity) hwidth hS hε hrow hcol
  exact (repeatedRowDoubling f hH hx hz hz1 h1 h2 k hk hscale).trans
    (min_le_left _ _)

/-- The two-block test used to forbid wasting a final Alice message. This
needs only the two certified input bounds, never exactness of `H = D f`. -/
theorem twoCopyTest {X Y : Type*}
    [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y] [DecidableEq Y]
    {q t N T H : ℕ} (f : X → Y → Bool) {S : Fin N → Fin q → Y}
    {ε x z h : ℝ} (hH : 2 ≤ H) (hx : 0 < x) (hx1 : x ≤ 1 / 2)
    (hz : 0 < z) (hz1 : z ≤ 1)
    (h1 : H ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x z))
    (h2 : H - 1 ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (z / 2)))
    (hwidth : 2 ≤ t) (hS : IsBalancedFamily t S ε) (hε : 0 ≤ ε)
    (hrow : ⌈(Fintype.card X : ℝ) * (2 * x)⌉₊ ≤ T)
    (hcol : (1 + ε) * z ^ 2 ≤ h) :
    BlockLowerBound (relaxedInterlace f S) Prod.fst Finset.univ 2 T h (H + 1) := by
  apply blockLowerBound_projection f (by norm_num) hwidth hS hε hrow hcol
  exact (twoCopyLambda f hH hx hx1 hz hz1 h1 h2).trans (min_le_left _ _)

end EthInapproximability.CurrentPaper.ExactSampledTests
