import EthInapproximability.CurrentPaper.JointTransfer
import EthInapproximability.CurrentPaper.FixedBin
import EthInapproximability.CurrentPaper.ProtocolFrontier

/-!
# Physical two-stream restrictions and their protocol budgets

Source: replacement v8, `A-stage4-details.tex`,
`lem:paper-terminal-two-stream`, the paragraph "Two fixed blocks" and
`eq:paper-terminal-fixed-bin`. The physical representatives are those of
`lem:paper-template-transfer`.

The paired sampler and the physical two-copy game previously had different
row and column carriers. This module constructs their exact input maps and
transfers the proved fixed-bin bound to the literal protected matrix and
its actual protocol suffix. No local communication conclusion is assumed.

The further `log s` outer-selector contribution in the final paragraph of
the source lemma is a separate remaining obligation. The theorems here do
not assert that stronger conclusion.
-/

noncomputable section
open scoped BigOperators Classical
open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace
open Workspace.Types.Protocol

namespace EthInapproximability.CurrentPaper.TerminalTwoStreams

open FixedBin TerminalExcess JointTransfer

section PairCarriers

variable {X Y : Type*} [Fintype X] [DecidableEq X]

/-- Tag one row by its actual position in the independently labelled pair. -/
def encodeRow {q : ℕ} (b : Bool) (r : Fin q × X) : Fin (2 * q) × X :=
  ((pairCoordinate q).symm (b, r.1), r.2)

omit [Fintype X] [DecidableEq X] in
theorem encodeRow_injective {q : ℕ} (b : Bool) :
    Function.Injective (encodeRow (X := X) (q := q) b) := by
  intro r r' h
  have hi := congrArg (fun t : Fin (2 * q) × X => (pairCoordinate q t.1).2) h
  exact Prod.ext (by simpa [encodeRow] using hi)
    (congrArg (fun t : Fin (2 * q) × X => t.2) h)

/-- The two streams have separate coordinate labels even if their rows agree. -/
def pairRows {q : ℕ} (Eo Ef : Finset (Fin q × X)) : Finset (Fin (2 * q) × X) :=
  Eo.image (encodeRow false) ∪ Ef.image (encodeRow true)

omit [Fintype X] in
@[simp] theorem mem_pairRows {q : ℕ} {Eo Ef : Finset (Fin q × X)}
    {r : Fin (2 * q) × X} :
    r ∈ pairRows Eo Ef ↔
      if (pairCoordinate q r.1).1 then
        ((pairCoordinate q r.1).2, r.2) ∈ Ef
      else ((pairCoordinate q r.1).2, r.2) ∈ Eo := by
  have hr : r = encodeRow (pairCoordinate q r.1).1
      ((pairCoordinate q r.1).2, r.2) := by simp [encodeRow]
  rw [hr]
  cases (pairCoordinate q r.1).1 <;>
    simp [pairRows, encodeRow, Prod.mk.injEq]

/-- Column labels enumerate the actual retained pairs, without multiplying
their two marginal projections. -/
def pairColumns {L : ℕ} (K : Finset (Fin L × Fin L)) : Finset (Fin (L * L)) :=
  K.image finProdFinEquiv

@[simp] theorem mem_pairColumns {L : ℕ} {K : Finset (Fin L × Fin L)}
    {j : Fin (L * L)} : j ∈ pairColumns K ↔ finProdFinEquiv.symm j ∈ K := by
  simp [pairColumns, Equiv.apply_eq_iff_eq_symm_apply]

@[simp] theorem pairColumns_card {L : ℕ} (K : Finset (Fin L × Fin L)) :
    (pairColumns K).card = K.card :=
  Finset.card_image_of_injective _ finProdFinEquiv.injective

theorem pairFamily_value {q L : ℕ} (S : Fin L → Fin q → Y)
    (j : Fin (L * L)) (k : Fin (2 * q)) :
    ProductBalancedness.pairFamily S j k =
      if (pairCoordinate q k).1 then
        S (finProdFinEquiv.symm j).2 (pairCoordinate q k).2
      else S (finProdFinEquiv.symm j).1 (pairCoordinate q k).2 := by
  obtain ⟨⟨b, i⟩, rfl⟩ := finProdFinEquiv.surjective k
  fin_cases b <;>
    simp [ProductBalancedness.pairFamily, ProductBalancedness.pairedFamily,
      pairCoordinate, finTwoArrowEquiv, finTwoEquiv]

omit [Fintype X] in
/-- A literal pair-family restriction is an input pullback of the two-copy
game on exactly the retained row sets and exactly the retained column pairs. -/
theorem pair_restriction_le_pairedGame {q L : ℕ}
    (f : X → Y → Bool) (S : Fin L → Fin q → Y)
    (Eo Ef : Finset (Fin q × X)) (K : Finset (Fin L × Fin L)) :
    D (subgame (relaxedInterlace f (ProductBalancedness.pairFamily S))
      (pairRows Eo Ef) (pairColumns K)) ≤
    D (pairedGame (relaxedInterlace f S) Eo Ef K) := by
  let rowMap : {r // r ∈ pairRows Eo Ef} →
      ({r // r ∈ Eo} ⊕ {r // r ∈ Ef}) := fun r =>
    if hb : (pairCoordinate q r.val.1).1 then
      .inr ⟨((pairCoordinate q r.val.1).2, r.val.2),
        by simpa [hb] using (mem_pairRows.mp r.property)⟩
    else
      .inl ⟨((pairCoordinate q r.val.1).2, r.val.2),
        by simpa [hb] using (mem_pairRows.mp r.property)⟩
  let colMap : {j // j ∈ pairColumns K} → {k // k ∈ K} :=
    fun j => ⟨finProdFinEquiv.symm j.val, mem_pairColumns.mp j.property⟩
  have heq : subgame (relaxedInterlace f (ProductBalancedness.pairFamily S))
      (pairRows Eo Ef) (pairColumns K) =
      fun r j => pairedGame (relaxedInterlace f S) Eo Ef K (rowMap r) (colMap j) := by
    funext r j
    change f r.val.2 (ProductBalancedness.pairFamily S j.val r.val.1) = _
    rw [pairFamily_value]
    cases hb : (pairCoordinate q r.val.1).1 <;>
      simp [rowMap, colMap, hb, pairedGame, relaxedInterlace]
  rw [heq]
  exact D_mapNodes_le _ rowMap colMap

omit [Fintype X] in
/-- Each labelled fibre of the paired encoding has exactly its original rows. -/
theorem pairRows_fibre_card {q : ℕ} (Eo Ef : Finset (Fin q × X))
    (b : Bool) (i : Fin q) :
    ((pairRows Eo Ef).filter (fun r => pairCoordinate q r.1 = (b, i))).card =
      (((if b then Ef else Eo).filter (fun r => r.1 = i))).card := by
  have heq : (pairRows Eo Ef).filter (fun r => pairCoordinate q r.1 = (b, i)) =
      (((if b then Ef else Eo).filter (fun r => r.1 = i))).image (encodeRow b) := by
    ext r
    simp only [Finset.mem_filter, mem_pairRows, Finset.mem_image]
    constructor
    · rintro ⟨hr, htag⟩
      refine ⟨(i, r.2), ⟨?_, rfl⟩, ?_⟩
      · cases b <;> simpa [htag] using hr
      · have hk : (pairCoordinate q).symm (b, i) = r.1 := by
          rw [← htag, Equiv.symm_apply_apply]
        simp [encodeRow, hk]
    · rintro ⟨r', ⟨hr', hi⟩, rfl⟩
      have hr'i : (i, r'.2) = r' := Prod.ext hi.symm rfl
      cases b <;> simpa [encodeRow, hi, hr'i] using hr'
  rw [heq, Finset.card_image_of_injective _ (encodeRow_injective b)]

/-- The two fibre-density sums are actual quotient row cardinalities. -/
theorem pairRows_fibre_sum {q : ℕ} (Eo Ef : Finset (Fin q × X)) (b : Bool) :
    (∑ i, fibreDensity (pairRows Eo Ef) (fun r => pairCoordinate q r.1)
      (Fintype.card X) (b, i)) =
      ((if b then Ef else Eo).card : ℝ) / Fintype.card X := by
  simp only [fibreDensity, pairRows_fibre_card, ← Finset.sum_div]
  congr 1
  rw [← Nat.cast_sum]
  congr 1
  simpa using Finset.sum_card_fiberwise_eq_card_filter
    (if b then Ef else Eo) Finset.univ Prod.fst

end PairCarriers

section FixedBinBound

variable {X Y : Type*} [Fintype X] [Fintype Y]
  [Nonempty X] [Nonempty Y] [DecidableEq X] [DecidableEq Y]

/-- The fixed-bin theorem now applies directly to the actual two-copy game.
Its density hypotheses refer to the two retained sets and the joint pairs.
The two one-copy input profiles and numerical stopping gates are explicit. -/
theorem paired_fixedBin (f : X → Y → Bool) {H m R q L : ℕ} {x ε eps delta : ℝ}
    (hqpos : 0 < q) (hq : q = 2 ^ R * 2 ^ (m - 1))
    (hH : 2 ≤ H) (hm : 2 ^ 20 ≤ m) (hx : 0 < x)
    (hrow : (2 : ℝ) ^ m * x ≤ 1) (hε : 0 ≤ ε)
    (hεsmall : 2 * ε + ε ^ 2 ≤ 1 / 50)
    (h1 : H ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (3 / 5)))
    (h2 : H - 1 ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (3 / 10)))
    (S : Fin L → Fin q → Y) (hS : IsBalancedFamily (2 ^ m) S ε)
    (hgateOne : (3 / 5 : ℝ) ≤
      yLoss (2 * ε + ε ^ 2) (2 ^ m) (49 / 64) (H + (R + m)))
    (hgateSeed : HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
      (49 / 64) * (2 : ℝ) ^ (-((H + m : ℕ) : ℝ)) / (1 + (2 * ε + ε ^ 2)))
    (Eo Ef : Finset (Fin q × X)) (K : Finset (Fin L × Fin L))
    (hEo : (1 - eps) * Fintype.card (Fin q × X) ≤ (Eo.card : ℝ))
    (hEf : delta * Fintype.card (Fin q × X) ≤ (Ef.card : ℝ))
    (hlam : (2 : ℝ) ^ R * ((2 : ℝ) ^ m * x) < 1)
    (hdelta : (2 : ℝ) ^ R * ((2 : ℝ) ^ m * x) + eps < delta)
    (hK : (49 / 64 : ℝ) * (L * L : ℕ) ≤ (K.card : ℝ)) :
    H + m + R ≤ D (pairedGame (relaxedInterlace f S) Eo Ef K) := by
  have hxpos : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have ho : (q : ℝ) * (1 - eps) ≤
      ∑ i, fibreDensity (pairRows Eo Ef) (fun r => pairCoordinate q r.1)
        (Fintype.card X) (false, i) := by
    rw [pairRows_fibre_sum]
    apply (le_div_iff₀ hxpos).mpr
    simpa [Fintype.card_prod, mul_assoc, mul_comm, mul_left_comm] using hEo
  have hf : (q : ℝ) * delta ≤
      ∑ i, fibreDensity (pairRows Eo Ef) (fun r => pairCoordinate q r.1)
        (Fintype.card X) (true, i) := by
    rw [pairRows_fibre_sum]
    apply (le_div_iff₀ hxpos).mpr
    simpa [Fintype.card_prod, mul_assoc, mul_comm, mul_left_comm] using hEf
  have hfixed := pair_fixedBin f hqpos hq hH hm hx hrow hε hεsmall h1 h2
    S hS hgateOne hgateSeed (pairRows Eo Ef) (pairColumns K) ho hf hlam hdelta
    (by simpa using hK)
  exact hfixed.trans (pair_restriction_le_pairedGame f S Eo Ef K)

end FixedBinBound

section PhysicalBound

open Construction
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem

universe u
variable {X Y : Type u} [Fintype X] [Fintype Y]
  [Nonempty X] [Nonempty Y]

/-- Deleting actual physical pairs and then forgetting copy labels preserves
the required joint density. The normalization uses a whole physical bin;
the independent sampler labels are the quotient, not a product of marginals. -/
theorem physical_pair_density_after_deletion
    (s L nv nb : ℕ) (hs : 0 < s) (hL : 0 < L) (hv : 0 < nv) (hb : 0 < nb)
    (po pf : Fin s)
    (Pstar P' : Finset (ProtectedRows s L nv nb X × ProtectedRows s L nv nb X))
    (hstar : Pstar ⊆ templateBin s L nv nb po ×ˢ templateBin s L nv nb pf)
    (hsub : P' ⊆ Pstar) {density loss : ℝ}
    (hdensity : density ≤ (Pstar.card : ℝ) /
      ((L * Fintype.card (TemplateLabels s L nv nb X) : ℕ) : ℝ) ^ 2)
    (hloss : ((Pstar \ P').card : ℝ) /
      ((L * Fintype.card (TemplateLabels s L nv nb X) : ℕ) : ℝ) ^ 2 ≤ loss)
    (hmargin : (49 / 64 : ℝ) ≤ density - loss) :
    (49 / 64 : ℝ) * (L * L : ℕ) ≤
      ((P'.image (fun y => (templateQuotient hL y.1, templateQuotient hL y.2))).card : ℝ) := by
  have h := surviving_pair_density
    (templateBin s L nv nb po) (templateBin s L nv nb pf)
    (templateQuotient hL) (templateQuotient hL)
    (template_regular s L nv nb hL po) (template_regular s L nv nb hL pf)
    (template_labels_pos s L nv nb hs hL hv hb)
    (template_bin_card s L nv nb po) (template_bin_card s L nv nb pf)
    Pstar P' hstar hsub hdensity hloss
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have h' := (le_div_iff₀ (sq_pos_of_pos hLpos)).mp
    (show (49 / 64 : ℝ) ≤
      ((P'.image (fun y => (templateQuotient hL y.1, templateQuotient hL y.2))).card : ℝ) /
        (L : ℝ) ^ 2 from by simpa using hmargin.trans h)
  simpa [pow_two] using h'

set_option maxHeartbeats 1600000 in
/-- The literal protected matrix inherits the fixed-bin bound through fixed
physical row representatives and one common completion of joint columns.
The second conclusion charges every actual Alice-prefix bit to its parent
protocol. Its execution hypothesis concerns all retained rows and columns;
there is no pruning, replacement protocol, or row-dependent column section.

This is the `D2+1` fixed-bin conclusion. The `log s` selector contribution
of the full two-stream theorem remains a separate routing obligation. -/
theorem physical_fixedBin_and_suffixBudget
    (base : X → Y → Bool) (a s q L nv nb Q H m ell : ℕ)
    (ha : 0 < qOne a) (hs : 0 < s) (hL : 0 < L)
    (hqpos : 0 < q) (hq : q = 2 ^ ell * 2 ^ (m - 1))
    {x ε eps delta : ℝ}
    (hH : 2 ≤ H) (hm : 2 ^ 20 ≤ m) (hx : 0 < x)
    (hrow : (2 : ℝ) ^ m * x ≤ 1) (hε : 0 ≤ ε)
    (hεsmall : 2 * ε + ε ^ 2 ≤ 1 / 50)
    (h1 : H ≤ Dfamily (interlaceFun (Function.swap (firstMatrix base a s)) 1)
      (bracketGE (FirstColumns a s Y) (FirstRows a X) 1 x (3 / 5)))
    (h2 : H - 1 ≤ Dfamily (interlaceFun (Function.swap (firstMatrix base a s)) 1)
      (bracketGE (FirstColumns a s Y) (FirstRows a X) 1 x (3 / 10)))
    (family : SecondFamily a q L X) (hS : IsBalancedFamily (2 ^ m) family ε)
    (hgateOne : (3 / 5 : ℝ) ≤
      yLoss (2 * ε + ε ^ 2) (2 ^ m) (49 / 64) (H + (ell + m)))
    (hgateSeed : HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
      (49 / 64) * (2 : ℝ) ^ (-((H + m : ℕ) : ℝ)) / (1 + (2 * ε + ε ^ 2)))
    (hlam : (2 : ℝ) ^ ell * ((2 : ℝ) ^ m * x) < 1)
    (hdelta : (2 : ℝ) ^ ell * ((2 : ℝ) ^ m * x) + eps < delta)
    (order : ItemOrder nv nb) (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (i j : Fin Q) (po pf : Fin s)
    (A : Finset (Fin Q × ProtectedColumns a s q Y))
    (S : Finset (Fin Q → ProtectedRows s L nv nb X))
    (Ao Af : Finset (ProtectedColumns a s q Y))
    (hAo : ∀ r ∈ Ao, (i, r) ∈ A) (hAf : ∀ r ∈ Af, (j, r) ∈ A)
    (hAoRef : Ao ⊆ referenceRows a s q) (hAfDiag : Af ⊆ diagonalRows a s q)
    (hAoDensity : 1 - eps ≤ (Ao.card : ℝ) / (referenceRows (Y := Y) a s q).card)
    (hAfDensity : delta ≤ (Af.card : ℝ) / (diagonalRows (Y := Y) a s q).card)
    (P' : Finset (ProtectedRows s L nv nb X × ProtectedRows s L nv nb X))
    (hP : P' ⊆ templateBin s L nv nb po ×ˢ templateBin s L nv nb pf)
    (sigma : ProtectedRows s L nv nb X × ProtectedRows s L nv nb X →
      Fin Q → ProtectedRows s L nv nb X)
    (hsigma : ∀ y ∈ P', sigma y ∈ S ∧ sigma y i = y.1 ∧ sigma y j = y.2)
    (hK : (49 / 64 : ℝ) * (L * L : ℕ) ≤
      ((P'.image (fun y => (templateQuotient hL y.1, templateQuotient hL y.2))).card : ℝ)) :
    let F := interlaceFun
      (protectedMatrix base a s q L nv nb hs family order vectors cap) Q
    H + m + ell ≤ D (subgame F A S) ∧
      ∀ (P : Protocol (Fin Q × ProtectedColumns a s q Y)
          (Fin Q → ProtectedRows s L nv nb X) Bool) (path : List Bool),
        IsAlicePath P path →
        (∀ r ∈ A, ∀ y ∈ S, P.eval r y = F r y) →
        (∀ r ∈ A, ∀ y ∈ S, (descend P path).eval r y = P.eval r y) →
        H + m + ell + path.length ≤ P.cost := by
  classical
  letI : Nonempty (Fin (qOne a)) := Fin.pos_iff_nonempty.mp ha
  letI : Nonempty (Fin q) := Fin.pos_iff_nonempty.mp hqpos
  let Eo : Finset (SecondRows a s q Y) :=
    Ao.image (fun r => selectorTuple (a := a) (s := s) (q := q) r po)
  let Ef : Finset (SecondRows a s q Y) :=
    Af.image (fun r => selectorTuple (a := a) (s := s) (q := q) r pf)
  let K : Finset (Fin L × Fin L) :=
    P'.image (fun y => (templateQuotient hL y.1, templateQuotient hL y.2))
  have hN : (0 : ℝ) < Fintype.card (SecondRows a s q Y) := by
    exact_mod_cast (Fintype.card_pos (α := SecondRows a s q Y))
  have ho : (1 - eps) * Fintype.card (SecondRows a s q Y) ≤ (Eo.card : ℝ) := by
    apply (le_div_iff₀ hN).mp
    simpa only [Eo] using
      hAoDensity.trans (reference_selected_density a s q hqpos po Ao hAoRef)
  have hf : delta * Fintype.card (SecondRows a s q Y) ≤ (Ef.card : ℝ) := by
    apply (le_div_iff₀ hN).mp
    simpa only [Ef] using
      hAfDensity.trans (diagonal_selected_density a s q hqpos pf Af hAfDiag)
  have hfixed := paired_fixedBin (Function.swap (firstMatrix base a s))
    hqpos hq hH hm hx hrow hε hεsmall h1 h2 family hS hgateOne hgateSeed
    Eo Ef K ho hf hlam hdelta hK
  have hphysical := hfixed.trans (pairedGame_le_actual_interlace base a s q L nv nb Q
    hs hL family order vectors cap i j po pf A S Ao Af hAo hAf P' hP sigma hsigma)
  refine ⟨hphysical, ?_⟩
  intro P path hpath hcompute hexec
  have hcost := ProtocolSeparation.restrictionCost_le_of_agrees
    (interlaceFun (protectedMatrix base a s q L nv nb hs family order vectors cap) Q)
    A S (descend P path) (by
      intro r hr y hy
      rw [hexec r hr y hy]
      exact hcompute r hr y hy)
  exact (Nat.add_le_add_right (hphysical.trans hcost) path.length).trans
    (cost_descend_add_length_le_of_isAlicePath hpath)

end PhysicalBound

end EthInapproximability.CurrentPaper.TerminalTwoStreams
