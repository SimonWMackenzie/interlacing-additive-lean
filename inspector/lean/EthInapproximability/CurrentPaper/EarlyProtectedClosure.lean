import EthInapproximability.CurrentPaper.JointTransfer
import EthInapproximability.CurrentPaper.CertifiedStopping
import EthInapproximability.CurrentPaper.ProductBalancedness
import EthInapproximability.CurrentPaper.PacketFibres
import EthInapproximability.CurrentPaper.ProductExtraction

/-!
# Several diagonal row groups on common surviving columns

Source: v8 `A-stage4-details.tex`, `lem:paper-uniform-protected-packet`
and `lem:paper-early-protected-closure`.

The restrictions here retain the original indexed columns. One representative
is chosen for an entire tuple, and one completion of that tuple is used in
every selected coordinate. Independently chosen marginal completions would
not define a restriction and are not used.
-/

noncomputable section
open scoped Classical
open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace

namespace EthInapproximability.CurrentPaper.EarlyProtectedClosure

open Construction JointTransfer

universe u

/-- A set of rows for each of several copies, evaluated on the same tuple. -/
def selectedCopies {B K : Type*} (M : B → K → Bool) {v : ℕ}
    (E : Fin v → Finset B) (T : Finset (Fin v → K)) :
    (Σ j : Fin v, {b // b ∈ E j}) → {t // t ∈ T} → Bool :=
  fun r t => M r.2.val (t.val r.1)

/-- Flattening the coordinates of independently labelled inner interlaces
does not replace their common surviving column tuple by marginal sets. -/
theorem product_restriction_le_selectedCopies
    {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B → Bool) {v q L : ℕ} (family : Fin L → Fin q → B)
    (E : Fin v → Finset (Fin q × A)) (T : Finset (Fin v → Fin L))
    (Rs : Finset (Fin (v * q) × A)) (Cs : Finset (Fin (L ^ v)))
    (hRs : ∀ r ∈ Rs,
      ((finProdFinEquiv.symm r.1).2, r.2) ∈ E (finProdFinEquiv.symm r.1).1)
    (hCs : ∀ c ∈ Cs, finFunctionFinEquiv.symm c ∈ T) :
    D (subgame (relaxedInterlace f (ProductBalancedness.productFamily v family)) Rs Cs) ≤
      D (selectedCopies (relaxedInterlace f family) E T) := by
  classical
  let rowMap : {r // r ∈ Rs} → (Σ j : Fin v, {r // r ∈ E j}) := fun r =>
    ⟨(finProdFinEquiv.symm r.val.1).1,
      ⟨((finProdFinEquiv.symm r.val.1).2, r.val.2), hRs r.val r.property⟩⟩
  let colMap : {c // c ∈ Cs} → {t // t ∈ T} := fun c =>
    ⟨finFunctionFinEquiv.symm c.val, hCs c.val c.property⟩
  exact D_mapNodes_le (selectedCopies (relaxedInterlace f family) E T) rowMap colMap

/-- The array of diagonal selector rows is exactly a family of inner
interlaces of the transpose of the first matrix. -/
theorem secondMatrix_eq_relaxed_transpose
    {X Y : Type u} (R : X → Y → Bool) (a s q L : ℕ)
    (family : SecondFamily a q L X) :
    secondMatrix R a s q L family =
      relaxedInterlace (fun γ r => firstMatrix R a s r γ) family := rfl

/-- The stopping theorem on the caller's actual ambient coordinate type.
The equality changes no rows, column labels or protocol semantics. -/
theorem localized_stopping_of_width {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B] [Nonempty A] [Nonempty B]
    (f : A → B → Bool) {H m R n : ℕ} {x h ε : ℝ}
    (hn : n = 2 ^ R * 2 ^ m)
    (hH : 2 ≤ H) (hm : 2 ^ 20 ≤ m) (hx : 0 < x)
    (hrow : (2 : ℝ) ^ m * x ≤ 1) (hε : 0 ≤ ε) (hh : 0 < h)
    (h1 : H ≤ Dfamily (interlaceFun f 1) (bracketGE A B 1 x (3 / 5)))
    (h2 : H - 1 ≤ Dfamily (interlaceFun f 1) (bracketGE A B 1 x (3 / 10)))
    {L : ℕ} (S : Fin L → Fin n → B)
    (hS : IsBalancedFamily (2 ^ m) S ε)
    (hgateOne : (3 / 5 : ℝ) ≤ yLoss ε (2 ^ m) h (H + (R + m)))
    (hgateSeed : HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
      h * (2 : ℝ) ^ (-((H + m : ℕ) : ℝ)) / (1 + ε))
    (e R' : ℕ) (he : e ≤ 1) (hR' : R' ≤ R)
    (Rs : Finset (Fin n × A)) (Cs : Finset (Fin L))
    (hRs : ∃ Qs : Finset (Fin n),
      Qs.card = 2 ^ R' * HardSeed.copyCount m ∧
      IsEquipartitionedGE Rs Qs
        ⌈(2 : ℝ) ^ (R' + m) * x * (Fintype.card A : ℝ)⌉₊)
    (hCs : h * (2 : ℝ) ^ (-(e : ℝ)) * (L : ℝ) ≤ (Cs.card : ℝ)) :
    H + (R' + m) ≤ D (subgame (relaxedInterlace f S) Rs Cs) := by
  subst n
  exact CertifiedStopping.localized_stopping f hH hm hx hrow hε hh h1 h2
    S hS hgateOne hgateSeed e R' he hR' Rs Cs hRs hCs

/-- The communication part of the several-copy bound: actual donor row
densities supply the blocks and their rows; the actual common label set
supplies the columns. No selected-block or communication-bound hypothesis
is assumed. The remaining conditions are exactly the stopping inequalities. -/
theorem selectedCopies_lower_bound
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    [Nonempty A] [Nonempty B]
    (f : A → B → Bool) {v q L H m R R' : ℕ} {x d h ε : ℝ}
    (family : Fin L → Fin q → B)
    (E : Fin v → Finset (Fin q × A)) (T : Finset (Fin v → Fin L))
    (hn : v * q = 2 ^ R * 2 ^ m)
    (hH : 2 ≤ H) (hm : 2 ^ 20 ≤ m) (hx : 0 < x)
    (hrow : (2 : ℝ) ^ m * x ≤ 1) (hε : 0 ≤ ε) (hh : 0 < h)
    (h1 : H ≤ Dfamily (interlaceFun f 1) (bracketGE A B 1 x (3 / 5)))
    (h2 : H - 1 ≤ Dfamily (interlaceFun f 1) (bracketGE A B 1 x (3 / 10)))
    (hS : IsBalancedFamily (2 ^ m) (ProductBalancedness.productFamily v family) ε)
    (hgateOne : (3 / 5 : ℝ) ≤ yLoss ε (2 ^ m) h (H + (R + m)))
    (hgateSeed : HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
      h * (2 : ℝ) ^ (-((H + m : ℕ) : ℝ)) / (1 + ε))
    (hR' : R' ≤ R) (hd : 0 ≤ d)
    (hE : ∀ j, d * q * Fintype.card A ≤ ((E j).card : ℝ))
    (hcount : (2 : ℝ) ^ (R' + m) ≤ (v : ℝ) * d * q / 2)
    (hthreshold : (2 : ℝ) ^ (R' + m) * x ≤ d / 2)
    (hT : h * (L : ℝ) ^ v ≤ T.card) :
    H + (R' + m) ≤ D (selectedCopies (relaxedInterlace f family) E T) := by
  classical
  have hp : 2 ^ R' * HardSeed.copyCount m ≤ 2 ^ (R' + m) := by
    rw [pow_add]
    exact Nat.mul_le_mul_left _ (HardSeed.copyCount_bounds (by omega : 5 ≤ m)).2.2
  obtain ⟨Qs, Rs, hQs, hRs, _, _, hequip⟩ := PacketFibres.protected_packet_rows
    (K := 2 ^ (R' + m)) (p := 2 ^ R' * HardSeed.copyCount m) E hd hE
      (by exact_mod_cast hcount) (by exact_mod_cast hthreshold) hp
  let Cs : Finset (Fin (L ^ v)) := T.map finFunctionFinEquiv.toEmbedding
  have hCsCard : Cs.card = T.card := Finset.card_map _
  have hCs : ∀ c ∈ Cs, finFunctionFinEquiv.symm c ∈ T := by
    intro c hc
    rcases Finset.mem_map.mp hc with ⟨t, ht, rfl⟩
    simpa using ht
  have hrowMember : ∀ r ∈ Rs,
      ((finProdFinEquiv.symm r.1).2, r.2) ∈ E (finProdFinEquiv.symm r.1).1 := by
    intro r hr
    have hh' := hRs hr
    have heq : finProdFinEquiv
        ((finProdFinEquiv.symm r.1).1, (finProdFinEquiv.symm r.1).2) = r.1 :=
      finProdFinEquiv.apply_symm_apply r.1
    apply (PacketFibres.mem_packetRows E (finProdFinEquiv.symm r.1).1
      (finProdFinEquiv.symm r.1).2 r.2).mp
    simpa only [heq] using hh'
  have hselected : ∃ Qs : Finset (Fin (v * q)),
      Qs.card = 2 ^ R' * HardSeed.copyCount m ∧
      IsEquipartitionedGE Rs Qs
        ⌈(2 : ℝ) ^ (R' + m) * x * (Fintype.card A : ℝ)⌉₊ := by
    refine ⟨Qs, hQs, ?_⟩
    convert hequip using 1
    push_cast
    ring_nf
  have hcolumns : h * (2 : ℝ) ^ (-(0 : ℝ)) * ((L ^ v : ℕ) : ℝ) ≤ Cs.card := by
    simpa only [neg_zero, Real.rpow_zero, mul_one, Nat.cast_pow, hCsCard] using hT
  have hlower := localized_stopping_of_width f hn hH hm hx hrow hε hh h1 h2
    (ProductBalancedness.productFamily v family) hS hgateOne hgateSeed
    0 R' (by omega) hR' Rs Cs hselected (by simpa only [Nat.cast_zero] using hcolumns)
  exact hlower.trans (product_restriction_le_selectedCopies f family E T Rs Cs
    hrowMember hCs)

variable {X Y : Type u} [Fintype X] [Fintype Y]

/-- The simultaneous quotient of arbitrarily many selected physical groups
is a genuine restriction of the original outer interlace. The map `sigma`
completes a WHOLE surviving tuple, not its coordinates separately. -/
theorem selectedCopies_le_actual_interlace
    (R : X → Y → Bool) (a s q L nv nb Q v : ℕ)
    (hs : 0 < s) (hL : 0 < L) (family : SecondFamily a q L X)
    (order : ItemOrder nv nb) (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (coords : Fin v → Fin Q) (bins : Fin v → Fin s)
    (A : Finset (Fin Q × ProtectedColumns a s q Y))
    (S : Finset (Fin Q → ProtectedRows s L nv nb X))
    (rows : Fin v → Finset (ProtectedColumns a s q Y))
    (hrows : ∀ j r, r ∈ rows j → (coords j, r) ∈ A)
    (T : Finset (Fin v → ProtectedRows s L nv nb X))
    (hbins : ∀ t ∈ T, ∀ j, t j ∈ templateBin s L nv nb (bins j))
    (sigma : (Fin v → ProtectedRows s L nv nb X) →
      Fin Q → ProtectedRows s L nv nb X)
    (hsigma : ∀ t ∈ T, sigma t ∈ S ∧ ∀ j, sigma t (coords j) = t j) :
    D (selectedCopies (secondMatrix R a s q L family)
      (fun j => (rows j).image (fun r => selectorTuple r (bins j)))
      (T.image (fun t j => templateQuotient hL (t j)))) ≤
      D (subgame
        (interlaceFun (protectedMatrix R a s q L nv nb hs family order vectors cap) Q)
        A S) := by
  classical
  let rowSection (j : Fin v) := selectedRowSection (rows j)
    (fun r => selectorTuple r (bins j))
  let tupleSection := selectedRowSection T (fun t j => templateQuotient hL (t j))
  let rowMap :
      (Σ j : Fin v, {b // b ∈ (rows j).image (fun r => selectorTuple r (bins j))}) →
      {r // r ∈ A} := fun r =>
    ⟨(coords r.1, rowSection r.1 r.2),
      hrows r.1 _ (selectedRowSection_mem _ _ r.2)⟩
  let colMap : {t // t ∈ T.image (fun t j => templateQuotient hL (t j))} →
      {t // t ∈ S} := fun t =>
    ⟨sigma (tupleSection t), (hsigma _ (selectedRowSection_mem _ _ t)).1⟩
  have heq : selectedCopies (secondMatrix R a s q L family)
      (fun j => (rows j).image (fun r => selectorTuple r (bins j)))
      (T.image (fun t j => templateQuotient hL (t j))) =
      fun r t => subgame
        (interlaceFun (protectedMatrix R a s q L nv nb hs family order vectors cap) Q)
        A S (rowMap r) (colMap t) := by
    funext r t
    have ht := selectedRowSection_mem T
      (fun t j => templateQuotient hL (t j)) t
    have ht' := selectedRowSection_apply T
      (fun t j => templateQuotient hL (t j)) t
    have hr := selectedRowSection_apply (rows r.1)
      (fun r' => selectorTuple r' (bins r.1)) r.2
    change secondMatrix R a s q L family r.2.val (t.val r.1) =
      protectedMatrix R a s q L nv nb hs family order vectors cap
        (rowSection r.1 r.2) (sigma (tupleSection t) (coords r.1))
    rw [(hsigma _ ht).2 r.1,
      protected_template_entry R a s q L nv nb hs hL family order vectors cap
        (bins r.1) ((tupleSection t) r.1) (hbins _ ht r.1) (rowSection r.1 r.2)]
    rw [show selectorTuple (rowSection r.1 r.2) (bins r.1) = r.2.val from hr,
      show templateQuotient hL (tupleSection t r.1) = t.val r.1 from congrFun ht' r.1]
  rw [heq]
  exact D_mapNodes_le _ rowMap colMap

/-- The several-copy lower bound applies to the actual protected interlace.
The row assumption is measured before forgetting physical duplication labels;
the column assumption is measured on one common surviving set in the product
of the chosen physical bins. Regular quotient maps supply the two density
hypotheses needed by localized stopping.

The extraction of these coordinates, bins and common tuples from a large
incoming mass is a separate obligation. This theorem does not assume a
communication lower bound for the packet or its ambient rectangle. -/
theorem physical_packet_lower_bound [Nonempty X] [Nonempty Y]
    (R : X → Y → Bool) (a s q L nv nb Q v : ℕ)
    (ha : 0 < qOne a) (hs : 0 < s) (hq : 0 < q) (hL : 0 < L)
    (hv : 0 < nv) (hb : 0 < nb) (family : SecondFamily a q L X)
    (order : ItemOrder nv nb) (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (coords : Fin v → Fin Q) (bins : Fin v → Fin s)
    (A : Finset (Fin Q × ProtectedColumns a s q Y))
    (S : Finset (Fin Q → ProtectedRows s L nv nb X))
    (rows : Fin v → Finset (ProtectedColumns a s q Y))
    (hrows : ∀ j r, r ∈ rows j → (coords j, r) ∈ A)
    (hdiagonal : ∀ j, rows j ⊆ diagonalRows a s q)
    (T : Finset (Fin v → ProtectedRows s L nv nb X))
    (hbins : ∀ t ∈ T, ∀ j, t j ∈ templateBin s L nv nb (bins j))
    (sigma : (Fin v → ProtectedRows s L nv nb X) →
      Fin Q → ProtectedRows s L nv nb X)
    (hsigma : ∀ t ∈ T, sigma t ∈ S ∧ ∀ j, sigma t (coords j) = t j)
    {H m R₀ R' : ℕ} {x d h ε : ℝ}
    (hn : v * q = 2 ^ R₀ * 2 ^ m)
    (hH : 2 ≤ H) (hm : 2 ^ 20 ≤ m) (hx : 0 < x)
    (hrow : (2 : ℝ) ^ m * x ≤ 1) (hε : 0 ≤ ε) (hh : 0 < h)
    (h1 : H ≤ Dfamily (interlaceFun (fun γ r => firstMatrix R a s r γ) 1)
      (bracketGE (FirstColumns a s Y) (FirstRows a X) 1 x (3 / 5)))
    (h2 : H - 1 ≤ Dfamily (interlaceFun (fun γ r => firstMatrix R a s r γ) 1)
      (bracketGE (FirstColumns a s Y) (FirstRows a X) 1 x (3 / 10)))
    (hbalanced : IsBalancedFamily (2 ^ m)
      (ProductBalancedness.productFamily v family) ε)
    (hgateOne : (3 / 5 : ℝ) ≤ yLoss ε (2 ^ m) h (H + (R₀ + m)))
    (hgateSeed : HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
      h * (2 : ℝ) ^ (-((H + m : ℕ) : ℝ)) / (1 + ε))
    (hR' : R' ≤ R₀) (hd : 0 ≤ d)
    (hdensity : ∀ j, d ≤ (rows j).card / ((diagonalRows (Y := Y) a s q).card : ℝ))
    (hcount : (2 : ℝ) ^ (R' + m) ≤ (v : ℝ) * d * q / 2)
    (hthreshold : (2 : ℝ) ^ (R' + m) * x ≤ d / 2)
    (hT : h * ((Fintype.piFinset
      (fun j => templateBin (X := X) s L nv nb (bins j))).card : ℝ) ≤ T.card) :
    H + (R' + m) ≤ D (subgame
      (interlaceFun (protectedMatrix R a s q L nv nb hs family order vectors cap) Q)
      A S) := by
  classical
  letI : Nonempty (Fin (qOne a)) := ⟨⟨0, ha⟩⟩
  letI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  let E : Fin v → Finset (SecondRows a s q Y) :=
    fun j => (rows j).image (fun r => selectorTuple r (bins j))
  let T₀ : Finset (Fin v → Fin L) := T.image (fun t j => templateQuotient
    (X := X) (s := s) (nv := nv) (nb := nb) hL (t j))
  have hE : ∀ j, d * q * Fintype.card (FirstColumns a s Y) ≤ ((E j).card : ℝ) := by
    intro j
    have ht := (hdensity j).trans
      (diagonal_selected_density (Y := Y) a s q hq (bins j) (rows j) (hdiagonal j))
    have hcard : (0 : ℝ) < Fintype.card (SecondRows a s q Y) := by
      exact_mod_cast Fintype.card_pos
    have hc := (le_div_iff₀ hcard).mp ht
    simpa only [SecondRows, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
      mul_assoc] using hc
  have hquotient : h * (L : ℝ) ^ v ≤ (T₀.card : ℝ) := by
    have ht := ProductExtraction.regular_product_density_bound
      (fun j => templateBin (X := X) s L nv nb (bins j))
      (fun _ => templateQuotient (X := X) (s := s) (nv := nv) (nb := nb) hL)
      (fun _ => Fintype.card (TemplateLabels s L nv nb X))
      (fun j => template_regular (X := X) s L nv nb hL (bins j))
      (fun _ => template_labels_pos (X := X) s L nv nb hs hL hv hb)
      T (fun t ht => Fintype.mem_piFinset.mpr (hbins t ht)) hT
    simpa only [Fintype.card_fin] using ht
  have hlower : H + (R' + m) ≤
      D (selectedCopies (relaxedInterlace
        (fun γ r => firstMatrix R a s r γ) family) E T₀) := selectedCopies_lower_bound
    (A := FirstColumns a s Y) (B := FirstRows a X)
    (v := v) (q := q) (L := L) (H := H) (m := m) (R := R₀) (R' := R')
    (x := x) (d := d) (h := h) (ε := ε)
    (fun γ r => firstMatrix R a s r γ) family E T₀
    hn hH hm hx hrow hε hh h1 h2 hbalanced hgateOne hgateSeed
    hR' hd hE hcount hthreshold hquotient
  exact hlower.trans (selectedCopies_le_actual_interlace R a s q L nv nb Q v
    hs hL family order vectors cap coords bins A S rows hrows T hbins sigma hsigma)

end EthInapproximability.CurrentPaper.EarlyProtectedClosure
