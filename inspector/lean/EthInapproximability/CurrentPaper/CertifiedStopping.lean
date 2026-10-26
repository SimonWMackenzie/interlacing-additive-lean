import NPCC.Transfer
import EthInapproximability.CurrentPaper.HardSeed

/-!
# Certified stopping for the current replacement paper

Source: v8, sections/02-foundations.tex, lem:paper-scalar-stopping.
The protocol induction is adapted from the private generic induction in
NPCC.Transfer, with an arbitrary certified lower bound K in place of D(f)+T.
The balance strength t is an arbitrary positive integer, not a power of two.
Only r=2^R and r'=2^R' use powers of two, as in the paper.
No claim about D(f) being the certified level is assumed.
-/

namespace EthInapproximability.CurrentPaper.CertifiedStopping

open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace
open Workspace.Types.Protocol

private theorem card_filter_image_val {α : Type*} [DecidableEq α] {s : Finset α}
    (u : Finset {x // x ∈ s}) (pr : α → Prop) [DecidablePred pr] :
    ((u.image Subtype.val).filter pr).card
      = (u.filter (fun x => pr x.val)).card := by
  rw [← Finset.card_image_of_injective (u.filter (fun x => pr x.val))
    Subtype.val_injective]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hpr⟩
    exact ⟨w, ⟨hw, hpr⟩, rfl⟩
  · rintro ⟨w, ⟨hw, hpr⟩, rfl⟩
    exact ⟨⟨w, hw, rfl⟩, hpr⟩

/-- `2^(−K) ≤ (2^k)⁻¹` (rpow left, monoid pow right) whenever `k ≤ K`. -/
private theorem rpow_neg_le_inv_npow {k K : ℕ} (hkK : k ≤ K) :
    (2 : ℝ) ^ (-(K : ℝ)) ≤ ((2 : ℝ) ^ k)⁻¹ := by
  rw [← Real.rpow_natCast 2 k, ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact neg_le_neg (by exact_mod_cast hkK)

/-- A nonconstant one-copy certificate forces a nonempty column carrier.
With `card Y = 0`, `(univ, ∅)` would be a bracket member of cost zero. -/
private theorem card_Y_pos_of_clause_one {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) {xzero z₀ : ℝ} (hxb1 : xzero ≤ 1)
    (hone : 1 ≤ Dfamily (interlaceFun f 1)
      (bracketGE X Y 1 (xzero) z₀)) :
    0 < Fintype.card Y := by
  by_contra hY
  have hY0 : Fintype.card Y = 0 := by omega
  have hmem : ((Finset.univ : Finset (Fin 1 × X)), (∅ : Finset (Fin 1 → Y)))
      ∈ bracketGE X Y 1 (xzero) z₀ := by
    refine ⟨?_, ?_⟩
    · intro i _
      have hfill : (Finset.univ : Finset (Fin 1 × X)).filter (fun p => p.1 = i)
          = Finset.univ := by
        apply Finset.filter_true_of_mem
        intro p _
        have h1 := p.1.2
        have h2 := i.2
        exact Fin.ext (by omega)
      rw [hfill, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, one_mul,
        Nat.ceil_le]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) hxb1
    · simp [hY0]
  have hcomp : (Protocol.leaf true).Computes
      (subgame (interlaceFun f 1) (Finset.univ : Finset (Fin 1 × X))
        (∅ : Finset (Fin 1 → Y))) := by
    intro x y
    exact absurd y.2 (Finset.notMem_empty _)
  have hD0 : D (subgame (interlaceFun f 1) (Finset.univ : Finset (Fin 1 × X))
      (∅ : Finset (Fin 1 → Y))) ≤ 0 := by
    have h0 : (0 : ℕ) ∈ AchievableCosts (subgame (interlaceFun f 1)
        (Finset.univ : Finset (Fin 1 × X)) (∅ : Finset (Fin 1 → Y))) :=
      ⟨Protocol.leaf true, rfl, hcomp⟩
    simpa [D] using Nat.sInf_le h0
  have hfam : Dfamily (interlaceFun f 1) (bracketGE X Y 1 (xzero) z₀)
      ≤ D (subgame (interlaceFun f 1) (Finset.univ : Finset (Fin 1 × X))
        (∅ : Finset (Fin 1 → Y))) := by
    have hm : D (subgame (interlaceFun f 1) (Finset.univ : Finset (Fin 1 × X))
        (∅ : Finset (Fin 1 → Y)))
        ∈ { d : ℕ | ∃ RC ∈ bracketGE X Y 1 (xzero) z₀,
            d = D (subgame (interlaceFun f 1) RC.1 RC.2) } := ⟨_, hmem, rfl⟩
    simpa [Dfamily] using Nat.sInf_le hm
  omega

/-- Typed `lem:max-projection` at one copy: a `t`-fold column set of size
`≥ n^t·y'` projects, on SOME coordinate, to `≥ n·y'^{1/t}` distinct values
(`|C| ≤ ∏ᵢ |projᵢ C|`, so the max factor is `≥ |C|^{1/t}`). -/
private theorem exists_dense_coordinate {Y : Type*} [Fintype Y] [DecidableEq Y]
    {t : ℕ} (ht : 0 < t) (hY : 0 < Fintype.card Y)
    (Cols : Finset (Fin t → Y)) {y' : ℝ} (hy' : 0 < y')
    (hcols : ⌈((Fintype.card Y : ℝ) ^ t) * y'⌉₊ ≤ Cols.card) :
    ∃ i₀ : Fin t, (Fintype.card Y : ℝ) * y' ^ (1 / (t : ℝ))
      ≤ ((Cols.image (fun c => c i₀)).card : ℝ) := by
  classical
  by_contra hnone
  simp only [not_exists, not_le] at hnone
  have hroot_pos : 0 < y' ^ (1 / (t : ℝ)) := Real.rpow_pos_of_pos hy' _
  have hnR : (0:ℝ) < (Fintype.card Y : ℝ) := by exact_mod_cast hY
  have hlow : ((Fintype.card Y : ℝ) ^ t) * y' ≤ (Cols.card : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hcols)
  have hColsNe : Cols.Nonempty := by
    rw [← Finset.card_pos]
    by_contra hc
    have hc0 : Cols.card = 0 := by omega
    rw [hc0] at hlow
    have : (0:ℝ) < ((Fintype.card Y : ℝ) ^ t) * y' := by positivity
    norm_num at hlow
    linarith
  have hsub : Cols ⊆ Fintype.piFinset (fun i => Cols.image (fun c => c i)) := by
    intro c hc
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_image_of_mem _ hc
  have hprod : (Cols.card : ℝ)
      ≤ ∏ i : Fin t, ((Cols.image (fun c => c i)).card : ℝ) := by
    have h1 : Cols.card ≤ ∏ i : Fin t, (Cols.image (fun c => c i)).card := by
      calc Cols.card
          ≤ (Fintype.piFinset (fun i => Cols.image (fun c => c i))).card :=
            Finset.card_le_card hsub
        _ = ∏ i : Fin t, (Cols.image (fun c => c i)).card :=
            Fintype.card_piFinset _
    exact_mod_cast h1
  have hlt : ∏ i : Fin t, ((Cols.image (fun c => c i)).card : ℝ)
      < ∏ _i : Fin t, ((Fintype.card Y : ℝ) * y' ^ (1 / (t : ℝ))) := by
    haveI : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp ht
    apply Finset.prod_lt_prod_of_nonempty
    · intro i _
      have hne : (Cols.image (fun c => c i)).Nonempty := hColsNe.image _
      have hpos : 0 < (Cols.image (fun c => c i)).card := Finset.card_pos.mpr hne
      exact_mod_cast hpos
    · intro i _
      exact hnone i
    · exact Finset.univ_nonempty
  have hBt : ∏ _i : Fin t, ((Fintype.card Y : ℝ) * y' ^ (1 / (t : ℝ)))
      = ((Fintype.card Y : ℝ) ^ t) * y' := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]
    congr 1
    rw [← Real.rpow_natCast (y' ^ (1 / (t : ℝ))) t, ← Real.rpow_mul hy'.le,
      one_div, inv_mul_cancel₀ (by exact_mod_cast ht.ne' : (t:ℝ) ≠ 0),
      Real.rpow_one]
  rw [hBt] at hlt
  linarith

/-- At the first node with all prescribed Alice bits spent, projection
produces a classical restriction with certified cost at least `K`.
Pulling back the genuine residual protocol contradicts its cost `< K`. -/
private theorem certified_seed_step {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] (f : X → Y → Bool) {ε : ℝ} (hε : 0 ≤ ε)
    (t R K : ℕ) (ht : 0 < t) {L : ℕ} (S : Fin L → Fin (2 ^ R * t) → Y)
    (hS : IsBalancedFamily (t) S ε)
    (pseed : ℕ) {xseed h hseed : ℝ}
    (hh0 : 0 < h)
    (hp1 : t ≤ 2 * pseed) (hp2 : pseed ≤ t)
    (hseedbd : K ≤ Dfamily (interlaceFun f pseed)
        (bracketGE X Y pseed xseed hseed))
    (hbridge : hseed ≤ h * (2 : ℝ) ^ (-((K : ℕ) : ℝ)) / (1 + ε))
    (a : ℕ) (Rs : Finset (Fin (2 ^ R * t) × X)) (Cs : Finset (Fin L))
    (P : Protocol {p // p ∈ Rs} {j // j ∈ Cs} Bool)
    (c : ℕ) (Qc : Finset (Fin (2 ^ R * t)))
    (Rc : Finset {p // p ∈ Rs}) (Cc : Finset {j // j ∈ Cs})
    (hcomp : ∀ x ∈ Rc, ∀ y ∈ Cc,
      P.eval x y = subgame (relaxedInterlace f S) Rs Cs x y)
    (hQcard : pseed ≤ Qc.card)
    (hQfib : ∀ qq ∈ Qc, ⌈(Fintype.card X : ℝ) * xseed⌉₊
        ≤ (Rc.filter (fun p => p.val.1 = qq)).card)
    (hCcard : h * (L : ℝ) ≤ (2 : ℝ) ^ (a + c) * (Cc.card : ℝ))
    (hac : a + c ≤ K)
    (hPcost : P.cost < K) : False := by
  classical
  have hεpos : (0:ℝ) < 1 + ε := by linarith
  have hpseed : 0 < pseed := by
    have h1 : 0 < t := ht
    omega
  have h2pow_pos : (0:ℝ) < (2 : ℝ) ^ (a + c) := by positivity
  obtain ⟨J, hJsub, hJcard⟩ := Finset.exists_subset_card_eq hQcard
  set e : Fin pseed ≃ {i // i ∈ J} := (J.orderIsoOfFin hJcard).toEquiv with he
  have hrow : IsEquipartitionedGE (Rc.image Subtype.val) J
      ⌈(Fintype.card X : ℝ) * xseed⌉₊ := by
    intro qq hqq
    rw [card_filter_image_val]
    exact hQfib qq (hJsub hqq)
  have hcol : (h * ((2 : ℝ) ^ (a + c))⁻¹) * (L : ℝ)
      ≤ ((Cc.image Subtype.val).card : ℝ) := by
    rw [Finset.card_image_of_injective Cc Subtype.val_injective]
    have hrw : (h * ((2 : ℝ) ^ (a + c))⁻¹) * (L : ℝ)
        = h * (L : ℝ) / (2 : ℝ) ^ (a + c) := by
      rw [div_eq_mul_inv]; ring
    rw [hrw, div_le_iff₀ h2pow_pos]
    calc h * (L : ℝ) ≤ (2 : ℝ) ^ (a + c) * (Cc.card : ℝ) := hCcard
      _ = (Cc.card : ℝ) * (2 : ℝ) ^ (a + c) := mul_comm _ _
  obtain ⟨RC', hmem, hRowsProv, hColsProv⟩ :=
    relaxed_to_classical (x := xseed) hpseed hp2 hS hε e hrow hcol (le_refl _)
  -- upgrade the member to density `hseed`
  have hseed_le : hseed ≤ (h * ((2 : ℝ) ^ (a + c))⁻¹) / (1 + ε) := by
    refine le_trans hbridge ?_
    rw [div_eq_mul_inv, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hεpos.le)
    exact mul_le_mul_of_nonneg_left (rpow_neg_le_inv_npow hac) hh0.le
  have hmem' : RC' ∈ bracketGE X Y pseed xseed hseed := by
    refine ⟨hmem.1, le_trans ?_ hmem.2⟩
    apply Nat.ceil_le_ceil
    exact mul_le_mul_of_nonneg_left hseed_le (by positivity)
  have hDlow : K ≤ D (subgame (interlaceFun f pseed) RC'.1 RC'.2) := by
    refine le_trans hseedbd ?_
    have hm : D (subgame (interlaceFun f pseed) RC'.1 RC'.2)
        ∈ { d : ℕ | ∃ RC ∈ bracketGE X Y pseed xseed hseed,
            d = D (subgame (interlaceFun f pseed) RC.1 RC.2) } := ⟨RC', hmem', rfl⟩
    simpa [Dfamily] using Nat.sInf_le hm
  -- transport the residual protocol onto the member
  have hρex : ∀ p : {p // p ∈ RC'.1}, ∃ w, w ∈ Rc ∧
      (w : Fin (2 ^ R * t) × X) = ((e p.val.1).val, p.val.2) := by
    intro p
    have hm2 := hRowsProv p.val p.2
    rw [Finset.mem_image] at hm2
    obtain ⟨w, hw, hweq⟩ := hm2
    exact ⟨w, hw, hweq⟩
  choose ρ hρmem hρval using hρex
  have hσex : ∀ cc : {c' // c' ∈ RC'.2}, ∃ w, w ∈ Cc ∧
      ∀ i : Fin pseed, cc.val i = S (w : Fin L) (e i).val := by
    intro cc
    obtain ⟨j, hj, hjeq⟩ := hColsProv cc.val cc.2
    rw [Finset.mem_image] at hj
    obtain ⟨w, hw, hweq⟩ := hj
    refine ⟨w, hw, ?_⟩
    intro i
    rw [← hweq] at hjeq
    exact hjeq i
  choose σ hσmem hσval using hσex
  have hPb : (Protocol.pullback ρ σ P).Computes
      (subgame (interlaceFun f pseed) RC'.1 RC'.2) := by
    intro p cc
    rw [Protocol.pullback_eval]
    rw [hcomp (ρ p) (hρmem p) (σ cc) (hσmem cc)]
    simp only [subgame, relaxedInterlace, interlaceFun]
    rw [hρval p, hσval cc p.val.1]
  have hDup : D (subgame (interlaceFun f pseed) RC'.1 RC'.2) ≤ P.cost := by
    have hmem2 : P.cost
        ∈ AchievableCosts (subgame (interlaceFun f pseed) RC'.1 RC'.2) :=
      ⟨Protocol.pullback ρ σ P, Protocol.pullback_cost ρ σ P, hPb⟩
    simpa [D] using Nat.sInf_le hmem2
  omega

/-- A leaf before all prescribed Alice bits have been spent is impossible.
At least `t` blocks survive. Indexed projection followed by a maximum
coordinate projection produces a monochromatic one-copy restriction at
the certified row and column densities. -/
private theorem certified_leaf_step {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] (f : X → Y → Bool) {xzero yzero ε : ℝ} (hε : 0 ≤ ε)
    (t R K : ℕ) (ht : 0 < t) {L : ℕ} (S : Fin L → Fin (2 ^ R * t) → Y)
    (hS : IsBalancedFamily (t) S ε)
    {h : ℝ} (hh0 : 0 < h)
    (hY : 0 < Fintype.card Y)
    (hone : 1 ≤ Dfamily (interlaceFun f 1)
        (bracketGE X Y 1 (xzero) yzero))
    (hyzero : yzero ≤ yLoss ε t h (R + K))
    (a : ℕ) (Rs : Finset (Fin (2 ^ R * t) × X)) (Cs : Finset (Fin L))
    (z : Bool) (c : ℕ) (Qc : Finset (Fin (2 ^ R * t)))
    (Rc : Finset {p // p ∈ Rs}) (Cc : Finset {j // j ∈ Cs})
    (hconst : ∀ x ∈ Rc, ∀ y ∈ Cc,
      subgame (relaxedInterlace f S) Rs Cs x y = z)
    (hQcard : t ≤ Qc.card)
    (hQfib : ∀ qq ∈ Qc, ⌈(Fintype.card X : ℝ) * (xzero)⌉₊
        ≤ (Rc.filter (fun p => p.val.1 = qq)).card)
    (hCcard : h * (L : ℝ) ≤ (2 : ℝ) ^ (a + c) * (Cc.card : ℝ))
    (hac : a + c ≤ R + K) : False := by
  classical
  have hεpos : (0:ℝ) < 1 + ε := by linarith
  have h2pow_pos : (0:ℝ) < (2 : ℝ) ^ (a + c) := by positivity
  obtain ⟨J, hJsub, hJcard⟩ := Finset.exists_subset_card_eq hQcard
  set e : Fin (t) ≃ {i // i ∈ J} := (J.orderIsoOfFin hJcard).toEquiv with he
  have hrow : IsEquipartitionedGE (Rc.image Subtype.val) J
      ⌈(Fintype.card X : ℝ) * (xzero)⌉₊ := by
    intro qq hqq
    rw [card_filter_image_val]
    exact hQfib qq (hJsub hqq)
  have hcol : (h * ((2 : ℝ) ^ (a + c))⁻¹) * (L : ℝ)
      ≤ ((Cc.image Subtype.val).card : ℝ) := by
    rw [Finset.card_image_of_injective Cc Subtype.val_injective]
    have hrw : (h * ((2 : ℝ) ^ (a + c))⁻¹) * (L : ℝ)
        = h * (L : ℝ) / (2 : ℝ) ^ (a + c) := by
      rw [div_eq_mul_inv]; ring
    rw [hrw, div_le_iff₀ h2pow_pos]
    calc h * (L : ℝ) ≤ (2 : ℝ) ^ (a + c) * (Cc.card : ℝ) := hCcard
      _ = (Cc.card : ℝ) * (2 : ℝ) ^ (a + c) := mul_comm _ _
  obtain ⟨RC', hmem, hRowsProv, hColsProv⟩ :=
    relaxed_to_classical (x := xzero) ht (le_refl (t)) hS hε e
      hrow hcol (le_refl _)
  -- the member is monochromatic with value `z`
  have hmono : ∀ p ∈ RC'.1, ∀ c' ∈ RC'.2, f p.2 (c' p.1) = z := by
    intro p hp c' hc'
    have hr := hRowsProv p hp
    rw [Finset.mem_image] at hr
    obtain ⟨w, hw, hweq⟩ := hr
    obtain ⟨j, hj, hjeq⟩ := hColsProv c' hc'
    rw [Finset.mem_image] at hj
    obtain ⟨jc, hjc, hjceq⟩ := hj
    rw [← hjceq] at hjeq
    have hval : f (w : Fin (2 ^ R * t) × X).2
        (S (jc : Fin L) (w : Fin (2 ^ R * t) × X).1) = z := hconst w hw jc hjc
    rw [hweq] at hval
    rw [hjeq p.1]
    exact hval
  -- max projection to one copy
  have hy'pos : 0 < (h * ((2 : ℝ) ^ (a + c))⁻¹) / (1 + ε) :=
    div_pos (mul_pos hh0 (inv_pos.mpr h2pow_pos)) hεpos
  obtain ⟨i₀, hi₀⟩ := exists_dense_coordinate ht hY RC'.2 hy'pos hmem.2
  set R₀ : Finset (Fin 1 × X) :=
    (RC'.1.filter (fun p => p.1 = i₀)).image (fun p => ((0 : Fin 1), p.2)) with hR₀
  set C₀ : Finset (Fin 1 → Y) :=
    ((RC'.2.image (fun c' => c' i₀)).image (fun yv => (fun _ : Fin 1 => yv))) with hC₀
  have hR₀card : R₀.card = (RC'.1.filter (fun p => p.1 = i₀)).card := by
    rw [hR₀]
    apply Finset.card_image_of_injOn
    intro p hp p' hp' hpp
    have h1 : p.1 = i₀ := (Finset.mem_filter.mp hp).2
    have h2 : p'.1 = i₀ := (Finset.mem_filter.mp hp').2
    simp only [Prod.mk.injEq] at hpp
    exact Prod.ext (h1.trans h2.symm) hpp.2
  have hC₀card : C₀.card = (RC'.2.image (fun c' => c' i₀)).card := by
    rw [hC₀]
    apply Finset.card_image_of_injective
    intro y1 y2 h12
    exact congrFun h12 ⟨0, Nat.one_pos⟩
  -- The first stopping gate guarantees the certified one-copy density.
  have hz₀le : yzero
      ≤ ((h * ((2 : ℝ) ^ (a + c))⁻¹) / (1 + ε)) ^ (1 / ((t : ℕ) : ℝ)) := by
    refine le_trans hyzero ?_
    unfold yLoss
    apply Real.rpow_le_rpow
    · exact div_nonneg (mul_nonneg hh0.le
        (Real.rpow_nonneg (by norm_num) _)) hεpos.le
    · rw [div_eq_mul_inv, div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hεpos.le)
      exact mul_le_mul_of_nonneg_left (rpow_neg_le_inv_npow hac) hh0.le
    · positivity
  have hrows₀ : IsEquipartitionedGE R₀ (Finset.univ : Finset (Fin 1))
      ⌈(Fintype.card X : ℝ) * (xzero)⌉₊ := by
    intro i _
    have hall : ∀ p ∈ R₀, p.1 = i := by
      intro p _
      have h1 := p.1.2
      have h2 := i.2
      exact Fin.ext (by omega)
    rw [Finset.filter_true_of_mem hall, hR₀card]
    exact hmem.1 i₀ (Finset.mem_univ i₀)
  have hcols₀ : ⌈((Fintype.card Y : ℝ) ^ 1)
      * yzero⌉₊ ≤ C₀.card := by
    rw [pow_one, Nat.ceil_le]
    calc (Fintype.card Y : ℝ) * yzero
        ≤ (Fintype.card Y : ℝ)
            * (((h * ((2 : ℝ) ^ (a + c))⁻¹) / (1 + ε)) ^ (1 / ((t : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hz₀le (Nat.cast_nonneg _)
      _ ≤ ((RC'.2.image (fun c' => c' i₀)).card : ℝ) := hi₀
      _ = (C₀.card : ℝ) := by rw [hC₀card]
  have hmem₀ : (R₀, C₀) ∈ bracketGE X Y 1 (xzero)
      yzero := ⟨hrows₀, hcols₀⟩
  -- the induced subgame is the constant `z`
  have hcz : (Protocol.leaf z).Computes (subgame (interlaceFun f 1) R₀ C₀) := by
    intro aa cc
    have haa : (aa : Fin 1 × X)
        ∈ (RC'.1.filter (fun p => p.1 = i₀)).image (fun p => ((0 : Fin 1), p.2)) := by
      rw [← hR₀]
      exact aa.2
    rw [Finset.mem_image] at haa
    obtain ⟨p, hpf, hpeq⟩ := haa
    rw [Finset.mem_filter] at hpf
    have hcc : (cc : Fin 1 → Y)
        ∈ (RC'.2.image (fun c' => c' i₀)).image (fun yv => (fun _ : Fin 1 => yv)) := by
      rw [← hC₀]
      exact cc.2
    rw [Finset.mem_image] at hcc
    obtain ⟨yv, hyv, hyveq⟩ := hcc
    rw [Finset.mem_image] at hyv
    obtain ⟨c', hc', hc'eq⟩ := hyv
    change z = subgame (interlaceFun f 1) R₀ C₀ aa cc
    have hgoal : subgame (interlaceFun f 1) R₀ C₀ aa cc
        = f (aa : Fin 1 × X).2 ((cc : Fin 1 → Y) (aa : Fin 1 × X).1) := rfl
    rw [hgoal, ← hpeq, ← hyveq, ← hc'eq]
    have hz := hmono p hpf.1 c' hc'
    rw [hpf.2] at hz
    exact hz.symm
  have hD0 : D (subgame (interlaceFun f 1) R₀ C₀) ≤ 0 := by
    have h0 : (0 : ℕ) ∈ AchievableCosts (subgame (interlaceFun f 1) R₀ C₀) :=
      ⟨Protocol.leaf z, rfl, hcz⟩
    simpa [D] using Nat.sInf_le h0
  have hfam : Dfamily (interlaceFun f 1)
      (bracketGE X Y 1 (xzero) yzero)
      ≤ D (subgame (interlaceFun f 1) R₀ C₀) := by
    have hm : D (subgame (interlaceFun f 1) R₀ C₀)
        ∈ { d : ℕ | ∃ RC ∈ bracketGE X Y 1 (xzero)
              yzero,
            d = D (subgame (interlaceFun f 1) RC.1 RC.2) } := ⟨(R₀, C₀), hmem₀, rfl⟩
    simpa [Dfamily] using Nat.sInf_le hm
  omega

set_option maxHeartbeats 1000000 in
-- The structural induction maintains both cardinal and real-valued invariants.
/-- The paper's root-to-leaf chain, as a structural induction over the
protocol tree with the frozen invariant (see the section docstring).
Bob nodes halve the surviving column set (`c ↦ c+1`); Alice nodes halve
each block fiber and keep the half of the blocks whose heavy side agrees
(`s ↦ s+1`); the FIRST node with `s = R'e` fires `certified_seed_step`,
and a leaf with `s < R'e` fires `certified_leaf_step`. -/
private theorem certified_chain {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] (f : X → Y → Bool) {xzero yzero ε : ℝ} (hε : 0 ≤ ε)
    (t R K : ℕ) (ht : 0 < t) {L : ℕ} (S : Fin L → Fin (2 ^ R * t) → Y)
    (hS : IsBalancedFamily (t) S ε)
    (pseed : ℕ) {xseed h hseed : ℝ}
    (hxzero0 : 0 < xzero) (hx1 : xzero ≤ xseed)
    (hh0 : 0 < h)
    (hp1 : t ≤ 2 * pseed) (hp2 : pseed ≤ t)
    (hone : 1 ≤ Dfamily (interlaceFun f 1)
      (bracketGE X Y 1 xzero yzero))
    (hyzero : yzero ≤ yLoss ε t h (R + K))
    (hseedbd : K ≤ Dfamily (interlaceFun f pseed)
        (bracketGE X Y pseed xseed hseed))
    (hbridge : hseed ≤ h * (2 : ℝ) ^ (-((K : ℕ) : ℝ)) / (1 + ε))
    (a R'e : ℕ) (ha : a ≤ 1) (hR'R : R'e ≤ R)
    (Rs : Finset (Fin (2 ^ R * t) × X)) (Cs : Finset (Fin L))
    (hY : 0 < Fintype.card Y)
    (P : Protocol {p // p ∈ Rs} {j // j ∈ Cs} Bool)
    (s c : ℕ) (Qc : Finset (Fin (2 ^ R * t)))
    (Rc : Finset {p // p ∈ Rs}) (Cc : Finset {j // j ∈ Cs})
    (hs : s ≤ R'e)
    (hcomp : ∀ x ∈ Rc, ∀ y ∈ Cc,
      P.eval x y = subgame (relaxedInterlace f S) Rs Cs x y)
    (hQcard : 2 ^ (R'e - s) * pseed ≤ Qc.card)
    (hQfib : ∀ qq ∈ Qc, ⌈(2 : ℝ) ^ (R'e - s) * xseed * (Fintype.card X : ℝ)⌉₊
        ≤ (Rc.filter (fun p => p.val.1 = qq)).card)
    (hCcard : h * (L : ℝ) ≤ (2 : ℝ) ^ (a + c) * (Cc.card : ℝ))
    (hcost : P.cost + s + c < K + R'e) : False := by
  have hxseed0 : 0 < xseed :=
    lt_of_lt_of_le hxzero0 hx1
  -- Case-2 firing wrapper, protocol-shape agnostic.
  have hfire : ∀ (P' : Protocol {p // p ∈ Rs} {j // j ∈ Cs} Bool) (c' : ℕ)
      (Qc' : Finset (Fin (2 ^ R * t))) (Rc' : Finset {p // p ∈ Rs})
      (Cc' : Finset {j // j ∈ Cs}),
      (∀ x ∈ Rc', ∀ y ∈ Cc',
        P'.eval x y = subgame (relaxedInterlace f S) Rs Cs x y) →
      2 ^ (R'e - R'e) * pseed ≤ Qc'.card →
      (∀ qq ∈ Qc', ⌈(2 : ℝ) ^ (R'e - R'e) * xseed * (Fintype.card X : ℝ)⌉₊
          ≤ (Rc'.filter (fun p => p.val.1 = qq)).card) →
      h * (L : ℝ) ≤ (2 : ℝ) ^ (a + c') * (Cc'.card : ℝ) →
      P'.cost + R'e + c' < K + R'e →
      False := by
    intro P' c' Qc' Rc' Cc' hcomp' hQcard' hQfib' hCcard' hcost'
    rw [Nat.sub_self, pow_zero, one_mul] at hQcard'
    have hQfib'' : ∀ qq ∈ Qc', ⌈(Fintype.card X : ℝ) * xseed⌉₊
        ≤ (Rc'.filter (fun p => p.val.1 = qq)).card := by
      intro qq hqq
      refine le_trans (Nat.ceil_le_ceil (le_of_eq ?_)) (hQfib' qq hqq)
      rw [Nat.sub_self, pow_zero]
      ring
    exact certified_seed_step f hε t R K ht S hS pseed hh0 hp1 hp2 hseedbd hbridge
      a Rs Cs P' c' Qc' Rc' Cc' hcomp' hQcard' hQfib'' hCcard'
      (by omega) (by omega)
  induction P generalizing s c Qc Rc Cc with
  | leaf z =>
    rcases eq_or_lt_of_le hs with heq | hslt
    · subst heq
      exact hfire (Protocol.leaf z) c Qc Rc Cc hcomp hQcard hQfib hCcard hcost
    · -- Case 1: monochromatic leaf before the row bits are exhausted.
      have hconst : ∀ x ∈ Rc, ∀ y ∈ Cc,
          subgame (relaxedInterlace f S) Rs Cs x y = z := by
        intro x hx y hy
        exact (hcomp x hx y hy).symm
      have hQcard' : t ≤ Qc.card := by
        have h1 : 1 ≤ R'e - s := by omega
        have h2 : 2 ≤ 2 ^ (R'e - s) := by
          calc 2 = 2 ^ 1 := (pow_one 2).symm
            _ ≤ 2 ^ (R'e - s) := Nat.pow_le_pow_right (by norm_num) h1
        have h3 : 2 * pseed ≤ 2 ^ (R'e - s) * pseed :=
          Nat.mul_le_mul_right pseed h2
        omega
      have hQfib' : ∀ qq ∈ Qc, ⌈(Fintype.card X : ℝ) * (xzero)⌉₊
          ≤ (Rc.filter (fun p => p.val.1 = qq)).card := by
        intro qq hqq
        refine le_trans (Nat.ceil_le_ceil ?_) (hQfib qq hqq)
        have hone2 : (1:ℝ) ≤ (2 : ℝ) ^ (R'e - s) := one_le_pow₀ (by norm_num)
        have hxx : xzero ≤ (2 : ℝ) ^ (R'e - s) * xseed := by
          calc xzero ≤ xseed := hx1
            _ = 1 * xseed := (one_mul _).symm
            _ ≤ (2 : ℝ) ^ (R'e - s) * xseed :=
                mul_le_mul_of_nonneg_right hone2 hxseed0.le
        calc (Fintype.card X : ℝ) * (xzero)
            ≤ (Fintype.card X : ℝ) * ((2 : ℝ) ^ (R'e - s) * xseed) :=
              mul_le_mul_of_nonneg_left hxx (Nat.cast_nonneg _)
          _ = (2 : ℝ) ^ (R'e - s) * xseed * (Fintype.card X : ℝ) := by ring
      have hac : a + c ≤ R + K := by
        have hc0 : (Protocol.leaf z : Protocol {p // p ∈ Rs} {j // j ∈ Cs} Bool).cost
            = 0 := rfl
        omega
      exact certified_leaf_step f hε t R K ht S hS hh0 hY hone hyzero a Rs Cs z c Qc Rc Cc
        hconst hQcard' hQfib' hCcard hac
  | aNode pred l r ihl ihr =>
    rcases eq_or_lt_of_le hs with heq | hslt
    · subst heq
      exact hfire (Protocol.aNode pred l r) c Qc Rc Cc hcomp hQcard hQfib hCcard hcost
    · -- Alice (row) bit: halve the fibers, keep the majority half of the blocks.
      set Rt : Finset {p // p ∈ Rs} := Rc.filter (fun p => pred p = true) with hRt
      set Rf : Finset {p // p ∈ Rs} := Rc.filter (fun p => ¬ (pred p = true)) with hRf
      have hsum : ∀ qq : Fin (2 ^ R * t),
          (Rt.filter (fun p => p.val.1 = qq)).card
            + (Rf.filter (fun p => p.val.1 = qq)).card
          = (Rc.filter (fun p => p.val.1 = qq)).card := by
        intro qq
        have e1 : Rt.filter (fun p => p.val.1 = qq)
            = (Rc.filter (fun p => p.val.1 = qq)).filter (fun p => pred p = true) := by
          rw [hRt, Finset.filter_comm]
        have e2 : Rf.filter (fun p => p.val.1 = qq)
            = (Rc.filter (fun p => p.val.1 = qq)).filter
                (fun p => ¬ (pred p = true)) := by
          rw [hRf, Finset.filter_comm]
        rw [e1, e2]
        exact Finset.card_filter_add_card_filter_not (fun p => pred p = true)
      -- threshold halving: 2·⌈u⌉ ≤ ⌈2u⌉ + 1
      have hkey : 2 * ⌈(2 : ℝ) ^ (R'e - (s+1)) * xseed * (Fintype.card X : ℝ)⌉₊
          ≤ ⌈(2 : ℝ) ^ (R'e - s) * xseed * (Fintype.card X : ℝ)⌉₊ + 1 := by
        have hu0 : (0:ℝ) ≤ (2 : ℝ) ^ (R'e - (s+1)) * xseed * (Fintype.card X : ℝ) :=
          mul_nonneg (mul_nonneg (by positivity) hxseed0.le) (Nat.cast_nonneg _)
        have hsplit2 : (2 : ℝ) ^ (R'e - s) * xseed * (Fintype.card X : ℝ)
            = 2 * ((2 : ℝ) ^ (R'e - (s+1)) * xseed * (Fintype.card X : ℝ)) := by
          have hexp : R'e - s = (R'e - (s+1)) + 1 := by omega
          rw [hexp, pow_succ]
          ring
        rw [hsplit2]
        have h1 : (⌈(2 : ℝ) ^ (R'e - (s+1)) * xseed * (Fintype.card X : ℝ)⌉₊ : ℝ)
            < (2 : ℝ) ^ (R'e - (s+1)) * xseed * (Fintype.card X : ℝ) + 1 :=
          Nat.ceil_lt_add_one hu0
        have h2 : 2 * ((2 : ℝ) ^ (R'e - (s+1)) * xseed * (Fintype.card X : ℝ))
            ≤ (⌈2 * ((2 : ℝ) ^ (R'e - (s+1)) * xseed * (Fintype.card X : ℝ))⌉₊ : ℝ) :=
          Nat.le_ceil _
        have h3 : ((2 * ⌈(2 : ℝ) ^ (R'e - (s+1)) * xseed
              * (Fintype.card X : ℝ)⌉₊ : ℕ) : ℝ)
            < ((⌈2 * ((2 : ℝ) ^ (R'e - (s+1)) * xseed
              * (Fintype.card X : ℝ))⌉₊ + 2 : ℕ) : ℝ) := by
          push_cast
          linarith
        have h4 := Nat.cast_lt.mp h3
        omega
      set QT : Finset (Fin (2 ^ R * t)) := Qc.filter (fun qq =>
        ⌈(2 : ℝ) ^ (R'e - (s+1)) * xseed * (Fintype.card X : ℝ)⌉₊
          ≤ (Rt.filter (fun p => p.val.1 = qq)).card) with hQT
      set QF : Finset (Fin (2 ^ R * t)) := Qc.filter (fun qq =>
        ¬ (⌈(2 : ℝ) ^ (R'e - (s+1)) * xseed * (Fintype.card X : ℝ)⌉₊
          ≤ (Rt.filter (fun p => p.val.1 = qq)).card)) with hQF
      have hQTF : QT.card + QF.card = Qc.card := by
        rw [hQT, hQF]
        exact Finset.card_filter_add_card_filter_not _
      have hQFfib : ∀ qq ∈ QF,
          ⌈(2 : ℝ) ^ (R'e - (s+1)) * xseed * (Fintype.card X : ℝ)⌉₊
            ≤ (Rf.filter (fun p => p.val.1 = qq)).card := by
        intro qq hqq
        rw [hQF, Finset.mem_filter] at hqq
        obtain ⟨hqqQ, hlight⟩ := hqq
        have hfib := hQfib qq hqqQ
        have hsq := hsum qq
        omega
      have hhalf : 2 ^ (R'e - (s+1)) * pseed ≤ QT.card
          ∨ 2 ^ (R'e - (s+1)) * pseed ≤ QF.card := by
        have hexp : R'e - s = (R'e - (s+1)) + 1 := by omega
        rw [hexp, pow_succ] at hQcard
        have h2 : 2 * (2 ^ (R'e - (s+1)) * pseed) ≤ QT.card + QF.card := by
          rw [hQTF]
          calc 2 * (2 ^ (R'e - (s+1)) * pseed)
              = 2 ^ (R'e - (s+1)) * 2 * pseed := by ring
            _ ≤ Qc.card := hQcard
        omega
      have hcost' : max l.cost r.cost + (s + 1) + c < K + R'e := by
        have hc1 : (Protocol.aNode pred l r).cost = 1 + max l.cost r.cost := rfl
        omega
      rcases hhalf with hhT | hhF
      · -- keep the `pred = true` side; the residual subtree is `r`
        refine ihr (s+1) c QT Rt Cc (by omega) ?_ hhT ?_ hCcard ?_
        · intro x hx y hy
          rw [hRt, Finset.mem_filter] at hx
          have hev := hcomp x hx.1 y hy
          simp only [Protocol.eval] at hev
          rw [if_pos hx.2] at hev
          exact hev
        · intro qq hqq
          rw [hQT, Finset.mem_filter] at hqq
          exact hqq.2
        · have hle : r.cost ≤ max l.cost r.cost := le_max_right _ _
          omega
      · -- keep the `pred = false` side; the residual subtree is `l`
        refine ihl (s+1) c QF Rf Cc (by omega) ?_ hhF hQFfib hCcard ?_
        · intro x hx y hy
          rw [hRf, Finset.mem_filter] at hx
          have hev := hcomp x hx.1 y hy
          simp only [Protocol.eval] at hev
          rw [if_neg hx.2] at hev
          exact hev
        · have hle : l.cost ≤ max l.cost r.cost := le_max_left _ _
          omega
  | bNode pred l r ihl ihr =>
    rcases eq_or_lt_of_le hs with heq | hslt
    · subst heq
      exact hfire (Protocol.bNode pred l r) c Qc Rc Cc hcomp hQcard hQfib hCcard hcost
    · -- Bob (column) bit: one child keeps at least half the columns.
      set Ct : Finset {j // j ∈ Cs} := Cc.filter (fun j => pred j = true) with hCt
      set Cf : Finset {j // j ∈ Cs} := Cc.filter (fun j => ¬ (pred j = true)) with hCf
      have hCTF : Ct.card + Cf.card = Cc.card := by
        rw [hCt, hCf]
        exact Finset.card_filter_add_card_filter_not _
      have h2pos : (0:ℝ) < (2 : ℝ) ^ (a + c) := by positivity
      have hchoice : h * (L : ℝ) ≤ (2 : ℝ) ^ (a + (c+1)) * (Ct.card : ℝ)
          ∨ h * (L : ℝ) ≤ (2 : ℝ) ^ (a + (c+1)) * (Cf.card : ℝ) := by
        by_contra hno
        simp only [not_or, not_le] at hno
        obtain ⟨h1, h2⟩ := hno
        have hpe : (2 : ℝ) ^ (a + (c+1)) = (2 : ℝ) ^ (a + c) * 2 := by
          rw [show a + (c+1) = (a+c) + 1 from rfl, pow_succ]
        rw [hpe] at h1 h2
        have hcast : ((Ct.card : ℝ) + (Cf.card : ℝ)) = (Cc.card : ℝ) := by
          exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hCTF
        have hXC : (2 : ℝ) ^ (a + c) * (Cc.card : ℝ)
            = (2 : ℝ) ^ (a + c) * (Ct.card : ℝ)
              + (2 : ℝ) ^ (a + c) * (Cf.card : ℝ) := by
          rw [← hcast]
          ring
        linarith [hCcard]
      have hcost' : max l.cost r.cost + s + (c + 1) < K + R'e := by
        have hc1 : (Protocol.bNode pred l r).cost = 1 + max l.cost r.cost := rfl
        omega
      rcases hchoice with hct | hcf
      · refine ihr s (c+1) Qc Rc Ct hs ?_ hQcard hQfib hct ?_
        · intro x hx y hy
          rw [hCt, Finset.mem_filter] at hy
          have hev := hcomp x hx y hy.1
          simp only [Protocol.eval] at hev
          rw [if_pos hy.2] at hev
          exact hev
        · have hle : r.cost ≤ max l.cost r.cost := le_max_right _ _
          omega
      · refine ihl s (c+1) Qc Rc Cf hs ?_ hQcard hQfib hcf ?_
        · intro x hx y hy
          rw [hCf, Finset.mem_filter] at hy
          have hev := hcomp x hx y hy.1
          simp only [Protocol.eval] at hev
          rw [if_neg hy.2] at hev
          exact hev
        · have hle : l.cost ≤ max l.cost r.cost := le_max_left _ _
          omega

/-- Current-v8 `lem:paper-scalar-stopping`.

Write `r = 2^R` and `r' = 2^R'e`. The arbitrary positive balance strength
is `t`; `pseed` satisfies `t/2 ≤ pseed ≤ t`. The two supplied family
bounds certify nonconstancy at `(xzero,yzero)` and cost `K` at
`(xseed,hseed)`. No equality or comparison between `K` and `D f` is used.

The first gate uses `yLoss ε t h (R+K)`, exactly
`(h * 2^(-(K+log r)) / (1+ε))^(1/t)`. The row/column assumptions use
actual finite sets, including ceilings and indexed-label multiplicities.
The bound follows by contradiction from a minimum-cost actual protocol
and the majority-child structural induction above.

The proof does not require `1 ≤ K`, nor the upper/positivity bounds on
`yzero` and `hseed` separately: their usefulness is enforced by the
certified family bounds and the displayed gates. Thus the interface is a
safe generalization of the paper's statement. -/
theorem scalar_stopping {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] (f : X → Y → Bool) {xzero yzero ε : ℝ} (hε : 0 ≤ ε)
    (t R K : ℕ) (ht : 0 < t)
    {L : ℕ} (S : Fin L → Fin (2 ^ R * t) → Y)
    (hS : IsBalancedFamily (t) S ε)
    (pseed : ℕ) {xseed h hseed : ℝ}
    (hxzero0 : 0 < xzero) (hx1 : xzero ≤ xseed) (hx2 : xseed ≤ 1)
    (hh0 : 0 < h)
    (hp1 : t ≤ 2 * pseed) (hp2 : pseed ≤ t)
    (hone : 1 ≤ Dfamily (interlaceFun f 1)
      (bracketGE X Y 1 xzero yzero))
    (hyzero : yzero ≤ yLoss ε t h (R + K))
    (hseedbd : K ≤ Dfamily (interlaceFun f pseed)
        (bracketGE X Y pseed xseed hseed))
    (hbridge : hseed ≤ h * (2 : ℝ) ^ (-((K : ℕ) : ℝ)) / (1 + ε))
    (a R'e : ℕ) (ha : a ≤ 1) (hR'R : R'e ≤ R)
    (Rs : Finset (Fin (2 ^ R * t) × X)) (Cs : Finset (Fin L))
    (hRs : ∃ Qs : Finset (Fin (2 ^ R * t)), Qs.card = 2 ^ R'e * pseed ∧
        IsEquipartitionedGE Rs Qs
          ⌈(2 : ℝ) ^ (R'e : ℕ) * xseed * (Fintype.card X : ℝ)⌉₊)
    (hCs : h * (2 : ℝ) ^ (-(a : ℝ)) * (L : ℝ) ≤ (Cs.card : ℝ)) :
    K + R'e ≤ D (subgame (relaxedInterlace f S) Rs Cs) := by
  classical
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨Qs, hQscard, hQseq⟩ := hRs
  have hxb1 : xzero ≤ 1 := le_trans hx1 hx2
  have hY : 0 < Fintype.card Y := card_Y_pos_of_clause_one f hxb1 hone
  have hne : (AchievableCosts (subgame (relaxedInterlace f S) Rs Cs)).Nonempty :=
    Workspace.UpperBound.AchievableCosts_nonempty _
  have hDmem : D (subgame (relaxedInterlace f S) Rs Cs)
      ∈ AchievableCosts (subgame (relaxedInterlace f S) Rs Cs) := by
    simpa [D] using Nat.sInf_mem hne
  obtain ⟨P₀, hP₀cost, hP₀comp⟩ := hDmem
  -- base invariant
  have hQbase : 2 ^ (R'e - 0) * pseed ≤ Qs.card := by
    rw [Nat.sub_zero, hQscard]
  have hQfibbase : ∀ qq ∈ Qs,
      ⌈(2 : ℝ) ^ (R'e - 0) * xseed * (Fintype.card X : ℝ)⌉₊
        ≤ (Rs.attach.filter (fun p => p.val.1 = qq)).card := by
    intro qq hqq
    calc ⌈(2 : ℝ) ^ (R'e - 0) * xseed * (Fintype.card X : ℝ)⌉₊
        ≤ (Rs.filter (fun p => p.1 = qq)).card := hQseq qq hqq
      _ = (Rs.attach.filter (fun p => p.val.1 = qq)).card := by
          have h1 := card_filter_image_val (s := Rs) Rs.attach (fun p => p.1 = qq)
          rw [Finset.attach_image_val] at h1
          exact h1
  have hCbase : h * (L : ℝ) ≤ (2 : ℝ) ^ (a + 0) * ((Cs.attach.card : ℕ) : ℝ) := by
    rw [Finset.card_attach, Nat.add_zero]
    have hpp : (2 : ℝ) ^ a * ((2 : ℝ) ^ (-(a : ℝ))) = 1 := by
      rw [← Real.rpow_natCast 2 a, ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      simp
    calc h * (L : ℝ)
        = ((2 : ℝ) ^ a * ((2 : ℝ) ^ (-(a : ℝ)))) * (h * (L : ℝ)) := by
          rw [hpp, one_mul]
      _ = (2 : ℝ) ^ a * (h * (2 : ℝ) ^ (-(a : ℝ)) * (L : ℝ)) := by ring
      _ ≤ (2 : ℝ) ^ a * ((Cs.card : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hCs (by positivity)
  exact certified_chain f hε t R K ht S hS pseed hxzero0 hx1 hh0 hp1 hp2 hone hyzero hseedbd hbridge
    a R'e ha hR'R Rs Cs hY P₀ 0 0 Qs Rs.attach Cs.attach
    (Nat.zero_le _) (fun x _ y _ => hP₀comp x y) hQbase hQfibbase hCbase
    (by omega)


/-- Current-v8 `lem:paper-localized-stopping`: the scalar stopping proof
specialized to the newly proved small-column-density theorem. The certified
integer `H` need not be the complexity of `f`. The selected width is
`2^R * 2^m`, and the selected number of row blocks is
`2^R' * (9 * 2^m / 16)`, with the exact integer form `copyCount m`. -/
theorem localized_stopping {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] [Nonempty X] [Nonempty Y]
    (f : X → Y → Bool) {H m R : ℕ} {x h ε : ℝ}
    (hH : 2 ≤ H) (hm : 2 ^ 20 ≤ m) (hx : 0 < x)
    (hrow : (2 : ℝ) ^ m * x ≤ 1) (hε : 0 ≤ ε) (hh : 0 < h)
    (h1 : H ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (3 / 5)))
    (h2 : H - 1 ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (3 / 10)))
    {L : ℕ} (S : Fin L → Fin (2 ^ R * 2 ^ m) → Y)
    (hS : IsBalancedFamily (2 ^ m) S ε)
    (hgateOne : (3 / 5 : ℝ) ≤ yLoss ε (2 ^ m) h (H + (R + m)))
    (hgateSeed : HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
      h * (2 : ℝ) ^ (-((H + m : ℕ) : ℝ)) / (1 + ε))
    (a R' : ℕ) (ha : a ≤ 1) (hR' : R' ≤ R)
    (Rs : Finset (Fin (2 ^ R * 2 ^ m) × X)) (Cs : Finset (Fin L))
    (hRs : ∃ Qs : Finset (Fin (2 ^ R * 2 ^ m)),
      Qs.card = 2 ^ R' * HardSeed.copyCount m ∧
      IsEquipartitionedGE Rs Qs
        ⌈(2 : ℝ) ^ (R' + m) * x * (Fintype.card X : ℝ)⌉₊)
    (hCs : h * (2 : ℝ) ^ (-(a : ℝ)) * (L : ℝ) ≤ (Cs.card : ℝ)) :
    H + (R' + m) ≤ D (subgame (relaxedInterlace f S) Rs Cs) := by
  have hgamma : (3 / 5 : ℝ) ≤ 1 / Real.sqrt 2 := by
    rw [le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))]
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hhalf : H - 1 ≤ Dfamily (interlaceFun f 1)
      (bracketGE X Y 1 x ((3 / 5 : ℝ) / 2)) := by
    convert h2 using 1; norm_num
  have hseed := HardSeed.hardSeed f hH hm hx
    (by norm_num : (0 : ℝ) < 3 / 5) hgamma h1 hhalf hrow
  have hseedCost : H + m ≤ Dfamily
      (interlaceFun f (HardSeed.copyCount m))
      (bracketGE X Y (HardSeed.copyCount m) ((2 : ℝ) ^ m * x)
        (HardSeed.columnDensity ((2 : ℝ) ^ m))) :=
    hseed.trans (min_le_left _ _)
  have hm5 : 5 ≤ m := by omega
  obtain ⟨hp, hpLow, hpHigh⟩ := HardSeed.copyCount_bounds hm5
  have hxGrow : x ≤ (2 : ℝ) ^ m * x := by
    simpa using mul_le_mul_of_nonneg_right
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hx.le
  have hRs' : ∃ Qs : Finset (Fin (2 ^ R * 2 ^ m)),
      Qs.card = 2 ^ R' * HardSeed.copyCount m ∧
      IsEquipartitionedGE Rs Qs
        ⌈(2 : ℝ) ^ R' * ((2 : ℝ) ^ m * x) * (Fintype.card X : ℝ)⌉₊ := by
    simpa [pow_add, mul_assoc] using hRs
  have hgateOne' : (3 / 5 : ℝ) ≤ yLoss ε (2 ^ m) h (R + (H + m)) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hgateOne
  have hs := scalar_stopping f hε (2 ^ m) R (H + m)
    (by positivity) S hS (HardSeed.copyCount m) hx hxGrow hrow hh hpLow hpHigh
    ((show 1 ≤ H by omega).trans h1) hgateOne' hseedCost hgateSeed
    a R' ha hR' Rs Cs hRs' hCs
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs

end EthInapproximability.CurrentPaper.CertifiedStopping
