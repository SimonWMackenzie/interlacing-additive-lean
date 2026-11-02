import EthInapproximability.CurrentPaper.TerminalExcess
import EthInapproximability.CurrentPaper.IndexedProjection
import EthInapproximability.CurrentPaper.CertifiedStopping
import EthInapproximability.CurrentPaper.ProductBalancedness

/-!
# The current paper's fixed-bin lower bound

Source: v8 `A-stage4-details.tex`, `lem:paper-terminal-two-stream`,
the paragraph "Two fixed blocks". The base and half-column tests of the
excess-block induction are proved here from the two one-copy bounds,
balancedness and the numerical stopping gates. They are not assumed.

This module first treats an arbitrary indexed family at the required
dyadic ambient width. This includes the paired family once its actual
balancedness and coordinate numbering have been supplied.
-/

namespace EthInapproximability.CurrentPaper.FixedBin

open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace
open ProtocolSeparation TerminalExcess IndexedProjection CertifiedStopping

variable {X Y : Type*} [Fintype X] [Fintype Y]
  [Nonempty X] [Nonempty Y] [DecidableEq Y]

/-- The base test follows from actual balanced projection and the certified
row ladder, using only the two one-copy bounds. -/
theorem baseTest (f : X → Y → Bool) {H m q L : ℕ} {x h ε : ℝ}
    (hH : 2 ≤ H) (hm : 1 ≤ m) (hx : 0 < x)
    (hrow : (2 : ℝ) ^ m * x ≤ 1) (hε : 0 ≤ ε)
    (h1 : H ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (3 / 5)))
    (h2 : H - 1 ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (3 / 10)))
    (S : Fin L → Fin q → Y) (hS : IsBalancedFamily (2 ^ m) S ε)
    (hdensity : (9 / 25 : ℝ) ≤ h / (1 + ε)) :
    BlockLowerBound (relaxedInterlace f S) Prod.fst Finset.univ
      (2 ^ (m - 1) + 1)
      (excessRows (Fintype.card X) ((2 : ℝ) ^ m * x) 0) h (H + m) := by
  classical
  apply blockLowerBound_of_exact
  intro Rs Cs Q _ hCs hQ hRs
  let e : Fin (2 ^ (m - 1) + 1) ≃ {i // i ∈ Q} :=
    Fintype.equivOfCardEq (by simpa using hQ.symm)
  have hu : 0 < (2 : ℕ) ^ (m - 1) + 1 := by positivity
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel hm]
  have hut : 2 ^ (m - 1) + 1 ≤ 2 ^ m := by
    have hp : 1 ≤ 2 ^ (m - 1) := Nat.one_le_pow _ _ (by omega)
    omega
  have hRs' : IsEquipartitionedGE Rs Q
      ⌈(Fintype.card X : ℝ) * ((2 : ℝ) ^ m * x)⌉₊ := by
    simpa only [HasRowsInBlocks, excessRows, pow_zero, one_mul, mul_comm]
      using hRs
  have hCs' : h * (L : ℝ) ≤ (Cs.card : ℝ) := by simpa using hCs
  obtain ⟨RC, hRC, _, _, hcost⟩ :=
    balanced_projection f hu hut hS hε e hRs' hCs'
  have hhalf : H - 1 ≤ Dfamily (interlaceFun f 1)
      (bracketGE X Y 1 x ((3 / 5 : ℝ) / 2)) := by
    convert h2 using 1; norm_num
  have hladder := repeatedRowDoubling f hH hx
    (by norm_num : (0 : ℝ) < 3 / 5) (by norm_num : (3 / 5 : ℝ) ≤ 1)
    h1 hhalf m hm hrow
  have htop : H + m ≤ Dfamily (interlaceFun f (2 ^ (m - 1) + 1))
      (bracketGE X Y (2 ^ (m - 1) + 1) ((2 : ℝ) ^ m * x) (9 / 25)) := by
    have hh := hladder.trans (min_le_left _ _)
    norm_num only [show (3 / 5 : ℝ) ^ 2 = 9 / 25 by norm_num] at hh
    exact hh
  have hRC' : RC ∈ bracketGE X Y (2 ^ (m - 1) + 1)
      ((2 : ℝ) ^ m * x) (9 / 25) :=
    bracketGE.anti_mono_params _ (le_refl _) hdensity hRC
  have hRCcost : Dfamily (interlaceFun f (2 ^ (m - 1) + 1))
      (bracketGE X Y (2 ^ (m - 1) + 1) ((2 : ℝ) ^ m * x) (9 / 25)) ≤
      D (subgame (interlaceFun f (2 ^ (m - 1) + 1)) RC.1 RC.2) :=
    Nat.sInf_le ⟨RC, hRC', rfl⟩
  exact htop.trans (hRCcost.trans hcost)

/-- Each higher-level half-column test is a direct application of localized
stopping. Only an actual subset of block labels is selected; the ambient
row and column sets, and therefore the protocol being bounded, stay fixed. -/
theorem halfColumnTest (f : X → Y → Bool) {H m R d L : ℕ} {x h ε : ℝ}
    (hH : 2 ≤ H) (hm : 2 ^ 20 ≤ m) (hx : 0 < x)
    (hrow : (2 : ℝ) ^ m * x ≤ 1) (hε : 0 ≤ ε) (hh : 0 < h)
    (h1 : H ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (3 / 5)))
    (h2 : H - 1 ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (3 / 10)))
    (S : Fin L → Fin (2 ^ R * 2 ^ m) → Y)
    (hS : IsBalancedFamily (2 ^ m) S ε)
    (hgateOne : (3 / 5 : ℝ) ≤ yLoss ε (2 ^ m) h (H + (R + m)))
    (hgateSeed : HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
      h * (2 : ℝ) ^ (-((H + m : ℕ) : ℝ)) / (1 + ε))
    (hd : d < R) :
    BlockLowerBound (relaxedInterlace f S) Prod.fst Finset.univ
      (excessWidth (2 ^ (m - 1)) (d + 1))
      (excessRows (Fintype.card X) ((2 : ℝ) ^ m * x) (d + 1))
      (h / 2) (H + m + d) := by
  classical
  intro Rs Cs Q _ hCs hQ hRs
  have hm1 : 1 ≤ m := by omega
  have hpseed : HardSeed.copyCount m ≤ 2 ^ m :=
    (HardSeed.copyCount_bounds (by omega : 5 ≤ m)).2.2
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel hm1]
  have hselected : 2 ^ d * HardSeed.copyCount m ≤ Q.card := by
    calc
      2 ^ d * HardSeed.copyCount m ≤ 2 ^ d * 2 ^ m := Nat.mul_le_mul_left _ hpseed
      _ ≤ excessWidth (2 ^ (m - 1)) (d + 1) := by
        simp only [excessWidth, pow_succ, hpow, mul_assoc]
        omega
      _ ≤ Q.card := hQ
  obtain ⟨Q', hsub, hcard⟩ := Finset.exists_subset_card_eq hselected
  have hRs' : ∃ Qs : Finset (Fin (2 ^ R * 2 ^ m)),
      Qs.card = 2 ^ d * HardSeed.copyCount m ∧
      IsEquipartitionedGE Rs Qs
        ⌈(2 : ℝ) ^ (d + m) * x * (Fintype.card X : ℝ)⌉₊ := by
    refine ⟨Q', hcard, ?_⟩
    intro i hi
    apply le_trans _ (hRs i (hsub hi))
    apply Nat.ceil_mono
    dsimp [excessRows]
    have hp : (2 : ℝ) ^ d ≤ (2 : ℝ) ^ (d + 1) := by
      apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      omega
    rw [pow_add]
    nlinarith [mul_le_mul_of_nonneg_right hp
      (show 0 ≤ (2 : ℝ) ^ m * x * (Fintype.card X : ℝ) by positivity)]
  have hCs' : h * (2 : ℝ) ^ (-(1 : ℝ)) * (L : ℝ) ≤ (Cs.card : ℝ) := by
    simpa [Real.rpow_neg_one, div_eq_mul_inv, mul_assoc] using hCs
  have hs := localized_stopping f hH hm hx hrow hε hh h1 h2 S hS
    hgateOne hgateSeed 1 d (le_refl _) (by omega) Rs Cs hRs'
    (by simpa only [Nat.cast_one] using hCs')
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs

/-- All excess-block levels are now proved for the actual indexed family;
no first-message lower-bound tests remain as hypotheses. -/
theorem excessBlocks_balanced (f : X → Y → Bool) {H m R L : ℕ} {x h ε : ℝ}
    (hH : 2 ≤ H) (hm : 2 ^ 20 ≤ m) (hx : 0 < x)
    (hrow : (2 : ℝ) ^ m * x ≤ 1) (hε : 0 ≤ ε) (hh : 0 < h)
    (h1 : H ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (3 / 5)))
    (h2 : H - 1 ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (3 / 10)))
    (S : Fin L → Fin (2 ^ R * 2 ^ m) → Y)
    (hS : IsBalancedFamily (2 ^ m) S ε)
    (hdensity : (9 / 25 : ℝ) ≤ h / (1 + ε))
    (hgateOne : (3 / 5 : ℝ) ≤ yLoss ε (2 ^ m) h (H + (R + m)))
    (hgateSeed : HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
      h * (2 : ℝ) ^ (-((H + m : ℕ) : ℝ)) / (1 + ε)) :
    ∀ d ≤ R, BlockLowerBound (relaxedInterlace f S) Prod.fst Finset.univ
      (excessWidth (2 ^ (m - 1)) d)
      (excessRows (Fintype.card X) ((2 : ℝ) ^ m * x) d)
      h (H + m + d) := by
  apply excessBlocks (relaxedInterlace f S) Prod.fst Finset.univ
    (Fintype.card X) (2 ^ (m - 1)) (H + m) R ((2 : ℝ) ^ m * x) h
    (by omega) (by positivity)
  · exact baseTest f hH (by omega) hx hrow hε h1 h2 S hS hdensity
  · intro d hd
    exact halfColumnTest f hH hm hx hrow hε hh h1 h2 S hS hgateOne hgateSeed hd

omit [Nonempty X] in
/-- Relabelled row fibres contain no more than the original base row count.
This uses the injectivity of the actual coordinate numbering. -/
theorem tagged_fibre_card_le {q : ℕ} {J : Type*} [DecidableEq J] (e : Fin q ≃ J)
    (Rs : Finset (Fin q × X)) (j : J) :
    (Rs.filter (fun a => e a.1 = j)).card ≤ Fintype.card X := by
  classical
  let T := Rs.filter (fun a => e a.1 = j)
  have hi : Set.InjOn Prod.snd {a | a ∈ T} := by
    intro a ha b hb hab
    apply Prod.ext
    · apply e.injective
      exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
    · exact hab
  have hc : (T.image Prod.snd).card = T.card := Finset.card_image_iff.mpr hi
  exact hc ▸ Finset.card_le_univ (T.image Prod.snd)

/-- The sharp large-fibre count feeds the fully proved excess-block theorem.
The two streams are different coordinate labels under `e`; all restrictions
and communication costs are those of the same indexed family. -/
theorem fixedBin_from_tagged {J : Type*} [Fintype J] [Nonempty J] [DecidableEq J]
    (f : X → Y → Bool) {H m R L : ℕ} {x h ε eps delta : ℝ}
    (hH : 2 ≤ H) (hm : 2 ^ 20 ≤ m) (hx : 0 < x)
    (hrow : (2 : ℝ) ^ m * x ≤ 1) (hε : 0 ≤ ε) (hh : 0 < h)
    (h1 : H ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (3 / 5)))
    (h2 : H - 1 ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (3 / 10)))
    (S : Fin L → Fin (2 ^ R * 2 ^ m) → Y)
    (hS : IsBalancedFamily (2 ^ m) S ε)
    (hdensity : (9 / 25 : ℝ) ≤ h / (1 + ε))
    (hgateOne : (3 / 5 : ℝ) ≤ yLoss ε (2 ^ m) h (H + (R + m)))
    (hgateSeed : HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
      h * (2 : ℝ) ^ (-((H + m : ℕ) : ℝ)) / (1 + ε))
    (e : Fin (2 ^ R * 2 ^ m) ≃ Bool × J)
    (hq : Fintype.card J = 2 ^ R * 2 ^ (m - 1))
    (Rs : Finset (Fin (2 ^ R * 2 ^ m) × X)) (Cs : Finset (Fin L))
    (hsr : (Fintype.card J : ℝ) * (1 - eps) ≤
      ∑ i, fibreDensity Rs (fun a => e a.1) (Fintype.card X) (false, i))
    (hsf : (Fintype.card J : ℝ) * delta ≤
      ∑ i, fibreDensity Rs (fun a => e a.1) (Fintype.card X) (true, i))
    (hlam : (2 : ℝ) ^ R * ((2 : ℝ) ^ m * x) < 1)
    (hdelta : (2 : ℝ) ^ R * ((2 : ℝ) ^ m * x) + eps < delta)
    (hCs : h * (L : ℝ) ≤ (Cs.card : ℝ)) :
    H + m + R ≤ D (subgame (relaxedInterlace f S) Rs Cs) := by
  classical
  obtain ⟨Qtag, hQtag, hRtag⟩ := actual_large_packet Rs (fun a => e a.1)
    (Fintype.card X) Fintype.card_pos
    ((2 : ℝ) ^ R * ((2 : ℝ) ^ m * x)) eps delta
    (tagged_fibre_card_le e Rs) hsr hsf hlam hdelta
  let Q := Qtag.image e.symm
  have hQcard : Q.card = Fintype.card J + 1 := by
    rw [Finset.card_image_of_injective _ e.symm.injective]
    exact hQtag
  have hRs : HasRowsInBlocks Prod.fst Rs Q
      (excessRows (Fintype.card X) ((2 : ℝ) ^ m * x) R) := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    have hfilter : Rs.filter (fun a => e a.1 = j) =
        Rs.filter (fun a => a.1 = e.symm j) := by
      ext a
      simp only [Finset.mem_filter]
      rw [e.apply_eq_iff_eq_symm_apply]
    simpa only [excessRows, hfilter] using hRtag j hj
  apply excessBlocks_balanced f hH hm hx hrow hε hh h1 h2 S hS
    hdensity hgateOne hgateSeed R (le_refl _) Rs Cs Q (Finset.subset_univ _)
  · simpa using hCs
  · simp only [excessWidth, hQcard, hq, le_refl]
  · exact hRs

/-- The density margin used in the manuscript, checked as exact arithmetic. -/
theorem projected_pair_density {ε : ℝ} (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 50) :
    (9 / 25 : ℝ) ≤ (49 / 64) / (1 + ε) := by
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 + ε)]
  linarith

/-- Width-equality wrapper: it keeps the original family and retained sets
literally unchanged, rather than asking consumers to cast their matrices. -/
theorem fixedBin_from_tagged_width {J : Type*} [Fintype J] [Nonempty J] [DecidableEq J]
    (f : X → Y → Bool) {H m R q L : ℕ} {x h ε eps delta : ℝ}
    (hwidth : q = 2 ^ R * 2 ^ m)
    (hH : 2 ≤ H) (hm : 2 ^ 20 ≤ m) (hx : 0 < x)
    (hrow : (2 : ℝ) ^ m * x ≤ 1) (hε : 0 ≤ ε) (hh : 0 < h)
    (h1 : H ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (3 / 5)))
    (h2 : H - 1 ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (3 / 10)))
    (S : Fin L → Fin q → Y) (hS : IsBalancedFamily (2 ^ m) S ε)
    (hdensity : (9 / 25 : ℝ) ≤ h / (1 + ε))
    (hgateOne : (3 / 5 : ℝ) ≤ yLoss ε (2 ^ m) h (H + (R + m)))
    (hgateSeed : HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
      h * (2 : ℝ) ^ (-((H + m : ℕ) : ℝ)) / (1 + ε))
    (e : Fin q ≃ Bool × J)
    (hq : Fintype.card J = 2 ^ R * 2 ^ (m - 1))
    (Rs : Finset (Fin q × X)) (Cs : Finset (Fin L))
    (hsr : (Fintype.card J : ℝ) * (1 - eps) ≤
      ∑ i, fibreDensity Rs (fun a => e a.1) (Fintype.card X) (false, i))
    (hsf : (Fintype.card J : ℝ) * delta ≤
      ∑ i, fibreDensity Rs (fun a => e a.1) (Fintype.card X) (true, i))
    (hlam : (2 : ℝ) ^ R * ((2 : ℝ) ^ m * x) < 1)
    (hdelta : (2 : ℝ) ^ R * ((2 : ℝ) ^ m * x) + eps < delta)
    (hCs : h * (L : ℝ) ≤ (Cs.card : ℝ)) :
    H + m + R ≤ D (subgame (relaxedInterlace f S) Rs Cs) := by
  subst q
  exact fixedBin_from_tagged f hH hm hx hrow hε hh h1 h2 S hS hdensity
    hgateOne hgateSeed e hq Rs Cs hsr hsf hlam hdelta hCs

/-- The two tags used by the literal independently labelled pair family. -/
def pairCoordinate (q : ℕ) : Fin (2 * q) ≃ Bool × Fin q :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr finTwoEquiv (Equiv.refl _))

/-- Fixed-bin lower bound for the actual independently labelled product
family. Balancedness of that product is proved, not an additional input.
The only communication premises are the original two one-copy bounds.
Numerical stopping gates remain explicit, as in the manuscript's lemma. -/
theorem pair_fixedBin (f : X → Y → Bool) {H m R q L : ℕ} {x ε eps delta : ℝ}
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
    (Rs : Finset (Fin (2 * q) × X)) (Cs : Finset (Fin (L * L)))
    (hsr : (q : ℝ) * (1 - eps) ≤
      ∑ i, fibreDensity Rs (fun a => pairCoordinate q a.1) (Fintype.card X) (false, i))
    (hsf : (q : ℝ) * delta ≤
      ∑ i, fibreDensity Rs (fun a => pairCoordinate q a.1) (Fintype.card X) (true, i))
    (hlam : (2 : ℝ) ^ R * ((2 : ℝ) ^ m * x) < 1)
    (hdelta : (2 : ℝ) ^ R * ((2 : ℝ) ^ m * x) + eps < delta)
    (hCs : (49 / 64 : ℝ) * (L * L : ℕ) ≤ (Cs.card : ℝ)) :
    H + m + R ≤ D (subgame
      (relaxedInterlace f (ProductBalancedness.pairFamily S)) Rs Cs) := by
  letI : Nonempty (Fin q) := Fin.pos_iff_nonempty.mp hqpos
  have hwidth : 2 * q = 2 ^ R * 2 ^ m := by
    have hp : 2 ^ m = 2 * 2 ^ (m - 1) := by
      rw [← Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega : 1 ≤ m)]
    rw [hq, hp]
    ring
  have hpairε : 0 ≤ 2 * ε + ε ^ 2 := by positivity
  exact fixedBin_from_tagged_width f hwidth hH hm hx hrow hpairε
    (by norm_num : (0 : ℝ) < 49 / 64) h1 h2
    (ProductBalancedness.pairFamily S) (ProductBalancedness.pair_balanced hS hε)
    (projected_pair_density hpairε hεsmall) hgateOne hgateSeed
    (pairCoordinate q) (by simpa using hq) Rs Cs
    (by simpa using hsr) (by simpa using hsf) hlam hdelta hCs

end EthInapproximability.CurrentPaper.FixedBin
