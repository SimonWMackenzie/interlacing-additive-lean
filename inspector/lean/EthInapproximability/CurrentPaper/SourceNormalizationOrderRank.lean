import EthInapproximability.CurrentPaper.SourceNormalizationNumeric

/-!
# Numeric labels of finite ordered graph vertices

The public serializer labels a vertex by its inverse increasing enumeration.
For any finite linear order, that label is the number of smaller elements.
This is the bridge needed to compare the abstract ordered normalization with
the concrete prefix-count implementation.
-/

namespace EthInapproximability.CurrentPaper.SourceNormalizationOrderRank

variable {α : Type*} [Fintype α] [LinearOrder α]

theorem inverse_enum_eq_card_below (a : α) :
    ((Fintype.orderIsoFinOfCardEq α rfl).symm a).val =
      (Finset.univ.filter (fun x : α => x < a)).card := by
  let e := Fintype.orderIsoFinOfCardEq α rfl
  have hst : ∀ x : α,
      x ∈ (Finset.univ.filter (fun y : α => y < a)) ↔
        e.symm x ∈ Finset.Iio (e.symm a) := by
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    exact e.symm.lt_iff_lt.symm
  have hc := Finset.card_bijective (s := Finset.univ.filter (fun x : α => x < a))
    (t := Finset.Iio (e.symm a)) e.symm e.symm.bijective hst
  simpa only [Fin.card_Iio] using hc.symm

theorem count_true_range_decide (p : ℕ → Prop) [DecidablePred p] (v : ℕ) :
    ((List.range v).map (fun i => decide (p i))).count true =
      (Finset.range v |>.filter p).card := by
  induction v with
  | zero => simp
  | succ v ih =>
      simp only [List.range_succ, List.map_append, List.map_singleton,
        List.count_append, List.count_cons, List.count_nil,
        Finset.range_add_one, ih]
      by_cases hp : p v <;> simp [hp, Finset.filter_insert]

theorem count_true_take_range_decide (p : ℕ → Prop) [DecidablePred p]
    (N v : ℕ) (hv : v ≤ N) :
    (((List.range N).map (fun i => decide (p i))).take v).count true =
      (Finset.range v |>.filter p).card := by
  rw [← List.map_take]
  have hr : (List.range N).take v = List.range v := by
    simp [List.take_range, Nat.min_eq_left hv]
  rw [hr]
  exact count_true_range_decide p v

theorem fin_inverse_enum_eq_val {N : ℕ} (i : Fin N) :
    ((Fintype.orderIsoFinOfCardEq (Fin N) rfl).symm i).val = i.val := by
  rw [inverse_enum_eq_card_below]
  have h : Finset.univ.filter (fun x : Fin N => x < i) = Finset.Iio i := by
    ext x
    simp
  rw [h]
  exact Fin.card_Iio i

theorem fin_order_enum_eq_cast {N : ℕ}
    (i : Fin (Fintype.card (Fin N))) :
    (Fintype.orderIsoFinOfCardEq (Fin N) rfl).toEquiv i =
      Fin.cast (Fintype.card_fin N) i := by
  let k : Fin N := Fin.cast (Fintype.card_fin N) i
  apply (Fintype.orderIsoFinOfCardEq (Fin N) rfl).toEquiv.symm.injective
  apply Fin.ext
  simpa only [Equiv.symm_apply_apply, k, Fin.val_cast] using
    (fin_inverse_enum_eq_val k).symm

theorem support_iff_endpoint (g : EncodedGraph.Graph) (hg : g.Valid)
    (v : Fin g.vertices) :
    (∃ e : Fin g.edges.length,
      v = (EncodedETHSource.rawGraph g hg).bd₀ e ∨
      v = (EncodedETHSource.rawGraph g hg).bd₁ e) ↔
      v.val ∈ SourceNormalizationNumeric.endpoints g := by
  simp only [SourceNormalizationNumeric.endpoints, List.mem_flatMap]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨g.edges.get e, List.get_mem .., ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases he with he | he
    · left
      simpa only [EncodedETHSource.rawGraph, EncodedGraph.endpoints_zero] using
        congrArg Fin.val he
    · right
      simpa only [EncodedETHSource.rawGraph, EncodedGraph.endpoints_one] using
        congrArg Fin.val he
  · rintro ⟨p, hp, hv⟩
    obtain ⟨e, he⟩ := List.mem_iff_get.mp hp
    rw [← he] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with hv | hv
    · refine ⟨e, Or.inl (Fin.ext ?_)⟩
      simpa [EncodedETHSource.rawGraph] using hv
    · refine ⟨e, Or.inr (Fin.ext ?_)⟩
      simpa [EncodedETHSource.rawGraph] using hv

theorem support_card_eq_numeric (g : EncodedGraph.Graph) (hg : g.Valid) :
    Fintype.card (EncodedETHSource.rawGraph g hg).Support =
      (SourceNormalizationNumeric.support g).count true := by
  let p : Fin g.vertices → Prop := fun v =>
    ∃ e : Fin g.edges.length,
      v = (EncodedETHSource.rawGraph g hg).bd₀ e ∨
      v = (EncodedETHSource.rawGraph g hg).bd₁ e
  have hc : (Finset.univ.filter p).card =
      ((Finset.range g.vertices).filter
        (fun v => v ∈ SourceNormalizationNumeric.endpoints g)).card := by
    apply Finset.card_bij (fun v _ => v.val)
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨v.isLt, (support_iff_endpoint g hg v).mp
        ((Finset.mem_filter.mp hv).2)⟩
    · intro a _ b _ h
      exact Fin.ext h
    · intro x hx
      have hmem := Finset.mem_filter.mp hx
      let v : Fin g.vertices := ⟨x, Finset.mem_range.mp hmem.1⟩
      refine ⟨v, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (support_iff_endpoint g hg v).mpr hmem.2⟩
  change Fintype.card {v : Fin g.vertices // p v} = _
  rw [Fintype.card_subtype]
  rw [hc]
  simpa only [SourceNormalizationNumeric.support] using
    (count_true_range_decide
      (fun v => v ∈ SourceNormalizationNumeric.endpoints g) g.vertices).symm

theorem support_label_eq_rank (g : EncodedGraph.Graph) (hg : g.Valid)
    (v : Fin g.vertices)
    (hv : ∃ e : Fin g.edges.length,
      v = (EncodedETHSource.rawGraph g hg).bd₀ e ∨
      v = (EncodedETHSource.rawGraph g hg).bd₁ e) :
    ((Fintype.orderIsoFinOfCardEq
      (EncodedETHSource.rawGraph g hg).Support rfl).symm ⟨v, hv⟩).val =
      SourceNormalizationNumeric.rank g v.val := by
  let a : (EncodedETHSource.rawGraph g hg).Support := ⟨v, hv⟩
  rw [inverse_enum_eq_card_below]
  have hc : (Finset.univ.filter (fun x : (EncodedETHSource.rawGraph g hg).Support =>
      x < a)).card =
      ((Finset.range v.val).filter
        (fun j => j ∈ SourceNormalizationNumeric.endpoints g)).card := by
    apply Finset.card_bij (fun x _ => x.val.val)
    · intro x hx
      have hlt : x.val.val < v.val := by
        exact (Finset.mem_filter.mp hx).2
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨hlt, (support_iff_endpoint g hg x.val).mp x.property⟩
    · intro x _ y _ h
      apply Subtype.ext
      exact Fin.ext h
    · intro j hj
      have hmem := Finset.mem_filter.mp hj
      have hlt : j < g.vertices := lt_trans (Finset.mem_range.mp hmem.1) v.isLt
      let w : Fin g.vertices := ⟨j, hlt⟩
      have hw := (support_iff_endpoint g hg w).mpr hmem.2
      let x : (EncodedETHSource.rawGraph g hg).Support := ⟨w, hw⟩
      refine ⟨x, ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact Finset.mem_range.mp hmem.1
  rw [hc]
  unfold SourceNormalizationNumeric.rank SourceNormalizationNumeric.support
  rw [count_true_take_range_decide
    (fun j => j ∈ SourceNormalizationNumeric.endpoints g)
    g.vertices v.val v.isLt.le]

theorem normalized_vertex_card (g : EncodedGraph.Graph) (hg : g.Valid) (n : ℕ) :
    Fintype.card ((EncodedETHSource.rawGraph g hg).NormalizedVertex n) =
      SourceNormalizationNumeric.repetitions g n *
        ((SourceNormalizationNumeric.support g).count true + 2) := by
  simp only [SourceNormalization.RawGraph.NormalizedVertex, Fintype.card_prod,
    Fintype.card_fin, SourceNormalization.RawGraph.PaddedVertex,
    Fintype.card_sum, Fintype.card_fin, support_card_eq_numeric g hg]
  simp [SourceNormalization.RawGraph.repetitions,
    SourceNormalizationNumeric.repetitions]

theorem rank_sum_inl {β : Type*} [Fintype β] [LinearOrder β]
    (a : α) :
    ((Fintype.orderIsoFinOfCardEq (α ⊕ₗ β) rfl).symm
      (toLex (Sum.inl a))).val =
      ((Fintype.orderIsoFinOfCardEq α rfl).symm a).val := by
  rw [inverse_enum_eq_card_below, inverse_enum_eq_card_below]
  refine (Finset.card_bij (s := Finset.univ.filter (fun x : α => x < a))
    (t := Finset.univ.filter (fun y : α ⊕ₗ β => y < toLex (Sum.inl a)))
    (fun x _ => toLex (Sum.inl x)) ?_ ?_ ?_).symm
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    simpa using hx
  · intro x _ y _ h
    exact Sum.inl_injective (congrArg ofLex h)
  · intro y hy
    cases h : ofLex y with
    | inl x =>
        have hyEq : y = toLex (Sum.inl x) := by
          calc y = toLex (ofLex y) := (toLex_ofLex y).symm
               _ = toLex (Sum.inl x) := congrArg toLex h
        refine ⟨x, ?_, ?_⟩
        · rw [hyEq] at hy
          exact (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            Sum.Lex.inl_lt_inl_iff.mp (Finset.mem_filter.mp hy).2⟩)
        · exact hyEq.symm
    | inr x =>
        have hyEq : y = toLex (Sum.inr x) := by
          calc y = toLex (ofLex y) := (toLex_ofLex y).symm
               _ = toLex (Sum.inr x) := congrArg toLex h
        have hnot : ¬ y < toLex (Sum.inl a) := by
          rw [hyEq]
          exact Sum.Lex.not_inr_lt_inl
        exact (hnot (Finset.mem_filter.mp hy).2).elim

theorem rank_sum_inr_zero :
    ((Fintype.orderIsoFinOfCardEq (α ⊕ₗ Fin 2) rfl).symm
      (toLex (Sum.inr (0 : Fin 2)))).val = Fintype.card α := by
  rw [inverse_enum_eq_card_below]
  have h := Finset.card_bij (s := (Finset.univ : Finset α))
    (t := Finset.univ.filter
      (fun y : α ⊕ₗ Fin 2 => y < toLex (Sum.inr (0 : Fin 2))))
    (fun x _ => toLex (Sum.inl x))
    (by intro x _; simp)
    (by intro x _ y _ he; exact Sum.inl_injective (congrArg ofLex he))
    (by
      intro y hy
      cases he : ofLex y with
      | inl x =>
          refine ⟨x, Finset.mem_univ _, ?_⟩
          calc toLex (Sum.inl x) = toLex (ofLex y) := congrArg toLex he.symm
               _ = y := toLex_ofLex y
      | inr x =>
          have hyEq : y = toLex (Sum.inr x) := by
            calc y = toLex (ofLex y) := (toLex_ofLex y).symm
                 _ = toLex (Sum.inr x) := congrArg toLex he
          rw [hyEq] at hy
          have hx : x < (0 : Fin 2) :=
            Sum.Lex.inr_lt_inr_iff.mp (Finset.mem_filter.mp hy).2
          exact (Nat.not_lt_zero x.val hx).elim)
  simpa using h.symm

theorem rank_sum_inr_one :
    ((Fintype.orderIsoFinOfCardEq (α ⊕ₗ Fin 2) rfl).symm
      (toLex (Sum.inr (1 : Fin 2)))).val = Fintype.card α + 1 := by
  rw [inverse_enum_eq_card_below]
  have h := Finset.card_bij (s := (Finset.univ : Finset (α ⊕ Unit)))
    (t := Finset.univ.filter
      (fun y : α ⊕ₗ Fin 2 => y < toLex (Sum.inr (1 : Fin 2))))
    (fun x _ => match x with
      | .inl a => toLex (Sum.inl a)
      | .inr _ => toLex (Sum.inr (0 : Fin 2)))
    (by intro x _; cases x <;> simp)
    (by
      intro x _ y _ he
      cases x <;> cases y <;> simp_all)
    (by
      intro y hy
      cases he : ofLex y with
      | inl x =>
          refine ⟨.inl x, Finset.mem_univ _, ?_⟩
          calc toLex (Sum.inl x) = toLex (ofLex y) := congrArg toLex he.symm
               _ = y := toLex_ofLex y
      | inr x =>
          have hyEq : y = toLex (Sum.inr x) := by
            calc y = toLex (ofLex y) := (toLex_ofLex y).symm
                 _ = toLex (Sum.inr x) := congrArg toLex he
          rw [hyEq] at hy
          have hx : x < (1 : Fin 2) :=
            Sum.Lex.inr_lt_inr_iff.mp (Finset.mem_filter.mp hy).2
          have hx0 : x = 0 := by ext; omega
          refine ⟨.inr (), Finset.mem_univ _, ?_⟩
          simpa only [hx0] using hyEq.symm)
  simpa [Fintype.card_sum] using h.symm

private theorem mixed_radix_lt_iff (w k i a b : ℕ)
    (ha : a < w) (hb : b < w) :
    (k < i ∨ k = i ∧ a < b) ↔ a + w * k < b + w * i := by
  constructor
  · rintro (h | ⟨rfl, h⟩)
    · have hm := Nat.mul_le_mul_left w (Nat.succ_le_of_lt h)
      simp only [Nat.mul_succ] at hm
      omega
    · omega
  · intro h
    rcases lt_trichotomy k i with hki | hki | hki
    · exact Or.inl hki
    · subst i
      exact Or.inr ⟨rfl, by omega⟩
    · have hm := Nat.mul_le_mul_left w (Nat.succ_le_of_lt hki)
      simp only [Nat.mul_succ] at hm
      omega

theorem lex_fin_product_rank {r w : ℕ} (i : Fin r) (j : Fin w) :
    ((Fintype.orderIsoFinOfCardEq (Fin r ×ₗ Fin w) rfl).symm
      (toLex (i,j))).val = i.val * w + j.val := by
  rw [inverse_enum_eq_card_below]
  let f : Fin r ×ₗ Fin w → Fin (r * w) :=
    fun p => finProdFinEquiv (ofLex p)
  have hf : Function.Bijective f :=
    finProdFinEquiv.bijective.comp ofLex.bijective
  have hlt : ∀ x : Fin r ×ₗ Fin w,
      x < toLex (i,j) ↔ f x < f (toLex (i,j)) := by
    intro x
    let p := ofLex x
    have hx : x = toLex p := (toLex_ofLex x).symm
    rw [hx]
    rcases p with ⟨k,l⟩
    simp only [Prod.Lex.toLex_lt_toLex, f, ofLex_toLex, Fin.lt_def]
    change (k < i ∨ k = i ∧ l < j) ↔
      (finProdFinEquiv (k,l)).val < (finProdFinEquiv (i,j)).val
    have hk : (finProdFinEquiv (k,l)).val = l.val + w * k.val := rfl
    have hi : (finProdFinEquiv (i,j)).val = j.val + w * i.val := rfl
    rw [hk, hi]
    simpa only [Fin.lt_def, Fin.ext_iff] using
      (mixed_radix_lt_iff w k.val i.val l.val j.val l.isLt j.isLt)
  have hc := Finset.card_bijective (s := Finset.univ.filter
      (fun x : Fin r ×ₗ Fin w => x < toLex (i,j)))
    (t := Finset.Iio (f (toLex (i,j)))) f hf (by
      intro x
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_Iio] using hlt x)
  have hv : (f (toLex (i,j))).val = j.val + w * i.val := rfl
  calc
    (Finset.univ.filter (fun x : Fin r ×ₗ Fin w => x < toLex (i,j))).card =
        (Finset.Iio (f (toLex (i,j)))).card := hc
    _ = (f (toLex (i,j))).val := Fin.card_Iio _
    _ = j.val + w * i.val := hv
    _ = i.val * w + j.val := by ac_rfl

theorem lex_product_rank {β : Type*} [Fintype β] [LinearOrder β]
    {r : ℕ} (i : Fin r) (b : β) :
    ((Fintype.orderIsoFinOfCardEq (Fin r ×ₗ β) rfl).symm
      (toLex (i,b))).val =
      i.val * Fintype.card β +
        ((Fintype.orderIsoFinOfCardEq β rfl).symm b).val := by
  rw [inverse_enum_eq_card_below]
  let e := (Fintype.orderIsoFinOfCardEq β rfl).symm
  let f : Fin r ×ₗ β → Fin r ×ₗ Fin (Fintype.card β) :=
    fun p => toLex ((ofLex p).1, e (ofLex p).2)
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply ofLex.injective
      have hp := congrArg ofLex h
      simp only [f, ofLex_toLex, Prod.mk.injEq] at hp
      exact Prod.ext hp.1 (e.injective hp.2)
    · intro y
      let p := ofLex y
      refine ⟨toLex (p.1,e.symm p.2), ?_⟩
      simp [f, p]
  have hlt : ∀ x : Fin r ×ₗ β,
      x < toLex (i,b) ↔ f x < f (toLex (i,b)) := by
    intro x
    simp only [Prod.Lex.lt_iff, f, ofLex_toLex]
    constructor
    · rintro (h | ⟨h,h'⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h,e.strictMono h'⟩
    · rintro (h | ⟨h,h'⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h,e.lt_iff_lt.mp h'⟩
  have hc := Finset.card_bijective (s := Finset.univ.filter
      (fun x : Fin r ×ₗ β => x < toLex (i,b)))
    (t := Finset.univ.filter (fun y : Fin r ×ₗ Fin (Fintype.card β) =>
      y < toLex (i,e b))) f hf (by
      intro x
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hlt x)
  calc
    (Finset.univ.filter (fun x : Fin r ×ₗ β => x < toLex (i,b))).card =
        (Finset.univ.filter (fun y : Fin r ×ₗ Fin (Fintype.card β) =>
          y < toLex (i,e b))).card := hc
    _ = ((Fintype.orderIsoFinOfCardEq (Fin r ×ₗ Fin (Fintype.card β)) rfl).symm
          (toLex (i,e b))).val := (inverse_enum_eq_card_below _).symm
    _ = _ := lex_fin_product_rank i (e b)

theorem copied_vertex_label {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : EthInapproximability.ParameterizedNP.GuardedSourceGraph.EndpointGraph V E)
    (r : ℕ) (hr : 0 < r) (i : Fin r) (v : V) :
    (letI := (G.copies r hr).orderV;
      ((Fintype.orderIsoFinOfCardEq (Fin r × V) rfl).symm (i,v)).val) =
      i.val * Fintype.card V +
        (letI := G.orderV;
          ((Fintype.orderIsoFinOfCardEq V rfl).symm v).val) := by
  classical
  letI : LinearOrder V := G.orderV
  letI : LinearOrder (Fin r × V) := (G.copies r hr).orderV
  letI : LT (Fin r × V) := (G.copies r hr).orderV.toLT
  rw [inverse_enum_eq_card_below]
  have heq : (Finset.univ.filter (fun x : Fin r × V => x < (i,v))).card =
      (Finset.univ.filter (fun x : Fin r ×ₗ V => x < toLex (i,v))).card := by
    apply Finset.card_bijective (s := Finset.univ.filter
      (fun x : Fin r × V => x < (i,v)))
      (t := Finset.univ.filter (fun x : Fin r ×ₗ V => x < toLex (i,v)))
      toLex toLex.bijective
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rw [heq]
  exact (inverse_enum_eq_card_below (toLex (i,v))).symm.trans
    (lex_product_rank i v)

theorem padded_vertex_label_old {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : SourceNormalization.RawGraph V E) (v : G.Support) :
    (letI := G.padded.orderV;
      ((Fintype.orderIsoFinOfCardEq G.PaddedVertex rfl).symm (Sum.inl v)).val) =
      (letI := G.orderV;
        ((Fintype.orderIsoFinOfCardEq G.Support rfl).symm v).val) := by
  classical
  letI : LinearOrder V := G.orderV
  letI : LinearOrder G.PaddedVertex := G.padded.orderV
  letI : LT G.PaddedVertex := G.padded.orderV.toLT
  rw [inverse_enum_eq_card_below]
  have heq : (Finset.univ.filter (fun x : G.PaddedVertex => x < Sum.inl v)).card =
      (Finset.univ.filter (fun x : G.Support ⊕ₗ Fin 2 =>
        x < toLex (Sum.inl v))).card := by
    apply Finset.card_bijective (s := Finset.univ.filter
      (fun x : G.PaddedVertex => x < Sum.inl v))
      (t := Finset.univ.filter (fun x : G.Support ⊕ₗ Fin 2 =>
        x < toLex (Sum.inl v))) toLex toLex.bijective
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rw [heq]
  exact (inverse_enum_eq_card_below (toLex (Sum.inl v))).symm.trans
    (rank_sum_inl v)

theorem padded_vertex_label_new {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : SourceNormalization.RawGraph V E) (b : Fin 2) :
    (letI := G.padded.orderV;
      ((Fintype.orderIsoFinOfCardEq G.PaddedVertex rfl).symm (Sum.inr b)).val) =
      Fintype.card G.Support + b.val := by
  classical
  letI : LinearOrder V := G.orderV
  letI : LinearOrder G.PaddedVertex := G.padded.orderV
  letI : LT G.PaddedVertex := G.padded.orderV.toLT
  rw [inverse_enum_eq_card_below]
  have heq : (Finset.univ.filter (fun x : G.PaddedVertex => x < Sum.inr b)).card =
      (Finset.univ.filter (fun x : G.Support ⊕ₗ Fin 2 =>
        x < toLex (Sum.inr b))).card := by
    apply Finset.card_bijective (s := Finset.univ.filter
      (fun x : G.PaddedVertex => x < Sum.inr b))
      (t := Finset.univ.filter (fun x : G.Support ⊕ₗ Fin 2 =>
        x < toLex (Sum.inr b))) toLex toLex.bijective
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rw [heq]
  fin_cases b
  · exact (inverse_enum_eq_card_below (toLex (Sum.inr (0 : Fin 2)))).symm.trans
      rank_sum_inr_zero
  · simpa using
      (inverse_enum_eq_card_below (toLex (Sum.inr (1 : Fin 2)))).symm.trans
        rank_sum_inr_one

theorem rank_sum_inr_unit :
    ((Fintype.orderIsoFinOfCardEq (α ⊕ₗ Unit) rfl).symm
      (toLex (Sum.inr ()))).val = Fintype.card α := by
  rw [inverse_enum_eq_card_below]
  have h := Finset.card_bij (s := (Finset.univ : Finset α))
    (t := Finset.univ.filter
      (fun y : α ⊕ₗ Unit => y < toLex (Sum.inr ())))
    (fun x _ => toLex (Sum.inl x))
    (by intro x _; simp)
    (by intro x _ y _ he; exact Sum.inl_injective (congrArg ofLex he))
    (by
      intro y hy
      cases he : ofLex y with
      | inl x =>
          refine ⟨x, Finset.mem_univ _, ?_⟩
          calc toLex (Sum.inl x) = toLex (ofLex y) := congrArg toLex he.symm
               _ = y := toLex_ofLex y
      | inr x =>
          have hyEq : y = toLex (Sum.inr x) := by
            calc y = toLex (ofLex y) := (toLex_ofLex y).symm
                 _ = toLex (Sum.inr x) := congrArg toLex he
          rw [hyEq] at hy
          have hx : x < () :=
            Sum.Lex.inr_lt_inr_iff.mp (Finset.mem_filter.mp hy).2
          exact (lt_irrefl () hx).elim)
  simpa using h.symm

theorem padded_edge_label_old {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : SourceNormalization.RawGraph V E) (e : E) :
    (letI := G.padded.orderE;
      ((Fintype.orderIsoFinOfCardEq G.PaddedEdge rfl).symm (Sum.inl e)).val) =
      (letI := G.orderE;
        ((Fintype.orderIsoFinOfCardEq E rfl).symm e).val) := by
  classical
  letI : LinearOrder E := G.orderE
  letI : LinearOrder G.PaddedEdge := G.padded.orderE
  letI : LT G.PaddedEdge := G.padded.orderE.toLT
  rw [inverse_enum_eq_card_below]
  have heq : (Finset.univ.filter (fun x : G.PaddedEdge => x < Sum.inl e)).card =
      (Finset.univ.filter (fun x : E ⊕ₗ Unit => x < toLex (Sum.inl e))).card := by
    apply Finset.card_bijective (s := Finset.univ.filter
      (fun x : G.PaddedEdge => x < Sum.inl e))
      (t := Finset.univ.filter (fun x : E ⊕ₗ Unit => x < toLex (Sum.inl e)))
      toLex toLex.bijective
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rw [heq]
  exact (inverse_enum_eq_card_below (toLex (Sum.inl e))).symm.trans
    (rank_sum_inl e)

theorem padded_edge_label_new {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : SourceNormalization.RawGraph V E) :
    (letI := G.padded.orderE;
      ((Fintype.orderIsoFinOfCardEq G.PaddedEdge rfl).symm (Sum.inr ())).val) =
      Fintype.card E := by
  classical
  letI : LinearOrder E := G.orderE
  letI : LinearOrder G.PaddedEdge := G.padded.orderE
  letI : LT G.PaddedEdge := G.padded.orderE.toLT
  rw [inverse_enum_eq_card_below]
  have heq : (Finset.univ.filter (fun x : G.PaddedEdge => x < Sum.inr ())).card =
      (Finset.univ.filter (fun x : E ⊕ₗ Unit => x < toLex (Sum.inr ()))).card := by
    apply Finset.card_bijective (s := Finset.univ.filter
      (fun x : G.PaddedEdge => x < Sum.inr ()))
      (t := Finset.univ.filter (fun x : E ⊕ₗ Unit => x < toLex (Sum.inr ())))
      toLex toLex.bijective
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rw [heq]
  exact (inverse_enum_eq_card_below (toLex (Sum.inr ()))).symm.trans
    rank_sum_inr_unit

theorem copied_edge_label {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : EthInapproximability.ParameterizedNP.GuardedSourceGraph.EndpointGraph V E)
    (r : ℕ) (hr : 0 < r) (i : Fin r) (e : E) :
    (letI := (G.copies r hr).orderE;
      ((Fintype.orderIsoFinOfCardEq (Fin r × E) rfl).symm (i,e)).val) =
      i.val * Fintype.card E +
        (letI := G.orderE;
          ((Fintype.orderIsoFinOfCardEq E rfl).symm e).val) := by
  classical
  letI : LinearOrder E := G.orderE
  letI : LinearOrder (Fin r × E) := (G.copies r hr).orderE
  letI : LT (Fin r × E) := (G.copies r hr).orderE.toLT
  rw [inverse_enum_eq_card_below]
  have heq : (Finset.univ.filter (fun x : Fin r × E => x < (i,e))).card =
      (Finset.univ.filter (fun x : Fin r ×ₗ E => x < toLex (i,e))).card := by
    apply Finset.card_bijective (s := Finset.univ.filter
      (fun x : Fin r × E => x < (i,e)))
      (t := Finset.univ.filter (fun x : Fin r ×ₗ E => x < toLex (i,e)))
      toLex toLex.bijective
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rw [heq]
  exact (inverse_enum_eq_card_below (toLex (i,e))).symm.trans
    (lex_product_rank i e)

theorem copied_edge_enumeration {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : EthInapproximability.ParameterizedNP.GuardedSourceGraph.EndpointGraph V E)
    (r : ℕ) (hr : 0 < r) (i : Fin r) (j : Fin (Fintype.card E)) :
    SourceNormalization.edgeEnumeration (G.copies r hr)
      ⟨i.val * Fintype.card E + j.val, by
        simp only [Fintype.card_prod, Fintype.card_fin]
        have h₁ : i.val * Fintype.card E + j.val <
            (i.val + 1) * Fintype.card E := by
          nlinarith [j.isLt]
        have h₂ : (i.val + 1) * Fintype.card E ≤
            r * Fintype.card E :=
          Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr i.isLt)
        omega⟩ = (i, SourceNormalization.edgeEnumeration G j) := by
  classical
  let e := SourceNormalization.edgeEnumeration G j
  apply (SourceNormalization.edgeEnumeration (G.copies r hr)).symm.injective
  apply Fin.ext
  simpa [SourceNormalization.edgeEnumeration, e] using
    (copied_edge_label G r hr i e).symm

theorem padded_edge_enumeration_old {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : SourceNormalization.RawGraph V E) (j : Fin (Fintype.card E)) :
    SourceNormalization.edgeEnumeration G.padded
      ⟨j.val, by
        simp only [SourceNormalization.RawGraph.padded_edge_count]
        omega⟩ =
      Sum.inl (letI := G.orderE;
        (Fintype.orderIsoFinOfCardEq E rfl).toEquiv j) := by
  classical
  apply (SourceNormalization.edgeEnumeration G.padded).symm.injective
  apply Fin.ext
  simpa [SourceNormalization.edgeEnumeration] using
    (padded_edge_label_old G
      (letI := G.orderE; (Fintype.orderIsoFinOfCardEq E rfl).toEquiv j)).symm

theorem padded_edge_enumeration_new {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : SourceNormalization.RawGraph V E) :
    SourceNormalization.edgeEnumeration G.padded
      ⟨Fintype.card E, by
        simp only [SourceNormalization.RawGraph.padded_edge_count]
        omega⟩ = Sum.inr () := by
  classical
  apply (SourceNormalization.edgeEnumeration G.padded).symm.injective
  apply Fin.ext
  simpa [SourceNormalization.edgeEnumeration] using
    (padded_edge_label_new G).symm

theorem padded_endpoint_zero_label {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : SourceNormalization.RawGraph V E) (e : E) :
    (letI := G.padded.orderV;
      ((Fintype.orderIsoFinOfCardEq G.PaddedVertex rfl).symm
        (G.padded.bd₀ (Sum.inl e))).val) =
    (letI := G.orderV;
      ((Fintype.orderIsoFinOfCardEq G.Support rfl).symm
        (G.endpoint₀ e)).val) := by
  exact padded_vertex_label_old G (G.endpoint₀ e)

theorem padded_endpoint_one_label {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : SourceNormalization.RawGraph V E) (e : E) :
    (letI := G.padded.orderV;
      ((Fintype.orderIsoFinOfCardEq G.PaddedVertex rfl).symm
        (G.padded.bd₁ (Sum.inl e))).val) =
    (letI := G.orderV;
      ((Fintype.orderIsoFinOfCardEq G.Support rfl).symm
        (G.endpoint₁ e)).val) := by
  exact padded_vertex_label_old G (G.endpoint₁ e)



end EthInapproximability.CurrentPaper.SourceNormalizationOrderRank
