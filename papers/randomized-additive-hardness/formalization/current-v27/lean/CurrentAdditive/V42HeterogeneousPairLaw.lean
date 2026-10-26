import CurrentAdditive.IndependentStreams

/-! Concatenating two exact bounded-wise sources with potentially different
carriers and laws. Independence is only the original complete product law;
no claim about a retained pair event is made. -/

namespace CurrentAdditive.V42HeterogeneousPairLaw

open Paper2
open scoped BigOperators

variable {I J O Seed : Type*}
  [Fintype I] [DecidableEq I] [Fintype J]
  [Fintype O] [DecidableEq O] [Fintype Seed]

private def slice (s : Finset (O × I)) (o : O) : Finset I :=
  (s.filter (fun a => a.1 = o)).image Prod.snd

omit [Fintype I] [Fintype O] in
private theorem mem_slice_iff (s : Finset (O × I)) (o : O) (i : I) :
    i ∈ slice s o ↔ (o, i) ∈ s := by
  classical
  simp only [slice, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨a, ⟨ha, hfst⟩, hsnd⟩
    have : a = (o, i) := Prod.ext hfst hsnd
    simpa [this] using ha
  · intro h
    exact ⟨(o, i), ⟨h, rfl⟩, rfl⟩

omit [Fintype I] [Fintype O] in
private theorem slice_card_le (s : Finset (O × I)) (o : O) :
    (slice s o).card ≤ s.card :=
  (Finset.card_image_le).trans (Finset.card_filter_le _ _)

/-- A probability fibre of a partial decoded inner word equals the product
of its requested coordinate weights. -/
private theorem inner_fibre (D : ℕ) (σ : FiniteLaw Seed)
    (μ : FiniteLaw J) (decode : Seed → I → J)
    (hinner : IsDWise D σ decode μ)
    (s : Finset (O × I)) (o : O) (hs : s.card ≤ D)
    (y : s → J) :
    σ.prob (fun a => ∀ i : slice s o,
      decode a i = y ⟨(o, i), (mem_slice_iff s o i).mp i.property⟩) =
      ∏ i : slice s o,
        μ.weight (y ⟨(o, i), (mem_slice_iff s o i).mp i.property⟩) := by
  let u := slice s o
  let v : u → J := fun i => y ⟨(o, i), (mem_slice_iff s o i).mp i.property⟩
  have h := hinner u ((slice_card_le s o).trans hs) (fun z => z = v)
  rw [FiniteLaw.prob_singleton] at h
  simpa only [FiniteLaw.pi, v, u, funext_iff] using h

omit [Fintype I] [Fintype O] in
private theorem slice_product (s : Finset (O × I)) (o : O)
    (μ : FiniteLaw J) (y : s → J) :
    (∏ i : slice s o,
        μ.weight (y ⟨(o, i), (mem_slice_iff s o i).mp i.property⟩)) =
      ∏ a ∈ s.filter (fun a => a.1 = o),
        μ.weight (if h : a ∈ s then y ⟨a, h⟩ else Classical.choice μ.nonempty) := by
  classical
  let f : I → ℝ := fun i =>
    μ.weight (if h : (o, i) ∈ s then y ⟨(o, i), h⟩ else Classical.choice μ.nonempty)
  have hinj : ∀ a ∈ s.filter (fun a => a.1 = o),
      ∀ b ∈ s.filter (fun a => a.1 = o), a.2 = b.2 → a = b := by
    intro a ha b hb h
    have h₁ : a.1 = o := (Finset.mem_filter.mp ha).2
    have h₂ : b.1 = o := (Finset.mem_filter.mp hb).2
    exact Prod.ext (h₁.trans h₂.symm) h
  have himage := Finset.prod_image (f := f) hinj
  change (∏ i ∈ slice s o, f i) =
    ∏ a ∈ s.filter (fun a => a.1 = o), f a.2 at himage
  calc
    _ = ∏ i : slice s o, f i := by
      apply Finset.prod_congr rfl
      intro i _
      simp only [f, dif_pos ((mem_slice_iff s o i).mp i.property)]
    _ = ∏ i ∈ slice s o, f i := by
      exact (Finset.prod_subtype (slice s o) (by simp) f).symm
    _ = ∏ a ∈ s.filter (fun a => a.1 = o), f a.2 := himage
    _ = _ := by
      apply Finset.prod_congr rfl
      intro a ha
      have hfst : a.1 = o := (Finset.mem_filter.mp ha).2
      cases a with
      | mk a i => simp only at hfst; subst a; rfl


def concat {So Sf : Type*} {q : ℕ}
    (decode_o : So → Fin q → J) (decode_f : Sf → Fin q → J) :
    (So × Sf) → (Bool × Fin q) → J :=
  fun z p => if p.1 then decode_f z.2 p.2 else decode_o z.1 p.2

private theorem prod_prob_and {So Sf : Type*} [Fintype So] [Fintype Sf]
    (σo : FiniteLaw So) (σf : FiniteLaw Sf) (Po : So → Prop) (Pf : Sf → Prop) :
    (σo.prod σf).prob (fun z => Po z.1 ∧ Pf z.2) = σo.prob Po * σf.prob Pf := by
  classical
  rw [FiniteLaw.prod_prob σo σf (fun a b => Po a ∧ Pf b)]
  have hprob (a : So) : σf.prob (fun b => Po a ∧ Pf b) =
      if Po a then σf.prob Pf else 0 := by
    by_cases h : Po a <;> simp [h]
  simp_rw [hprob]
  simp only [FiniteLaw.prob]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : Po a <;> simp [h]

/-- The two laws and the two source carriers are entirely independent inputs.
Every requested set of at most D distinct tagged coordinates has the exact
base product marginal, including equal inner indices on opposite tags. -/
theorem concat_dwise {So Sf : Type*} [Fintype So] [Fintype Sf] {q : ℕ}
    (D : ℕ) (σo : FiniteLaw So) (σf : FiniteLaw Sf) (μ : FiniteLaw J)
    (decode_o : So → Fin q → J) (decode_f : Sf → Fin q → J)
    (ho : IsDWise D σo decode_o μ) (hf : IsDWise D σf decode_f μ) :
    IsDWise D (σo.prod σf) (concat decode_o decode_f) μ := by
  classical
  intro s hs E
  apply FiniteLaw.prob_preimage_eq_of_fibres
    (σo.prod σf) (FiniteLaw.pi (fun _ : s => μ))
    (fun z p => concat decode_o decode_f z p.val) ?_ E
  intro y
  let Po : So → Prop := fun z => ∀ i : slice s false,
    decode_o z i = y ⟨(false,i),(mem_slice_iff s false i).mp i.property⟩
  let Pf : Sf → Prop := fun z => ∀ i : slice s true,
    decode_f z i = y ⟨(true,i),(mem_slice_iff s true i).mp i.property⟩
  have hevent : (fun z : So × Sf =>
      (fun p : s => concat decode_o decode_f z p.val)=y) =
      (fun z => Po z.1 ∧ Pf z.2) := by
    funext z
    apply propext
    constructor
    · intro h
      constructor
      · intro i
        exact congrFun h ⟨(false,i),(mem_slice_iff s false i).mp i.property⟩
      · intro i
        exact congrFun h ⟨(true,i),(mem_slice_iff s true i).mp i.property⟩
    · rintro ⟨hzo,hzf⟩
      funext p
      rcases p with ⟨⟨b,i⟩,hp⟩
      cases b with
      | false => exact hzo ⟨i,(mem_slice_iff s false i).mpr hp⟩
      | true => exact hzf ⟨i,(mem_slice_iff s true i).mpr hp⟩
  rw [hevent,prod_prob_and]
  rw [show σo.prob Po = ∏ i : slice s false,
      μ.weight (y ⟨(false,i),(mem_slice_iff s false i).mp i.property⟩) from
    inner_fibre D σo μ decode_o ho s false hs y]
  rw [show σf.prob Pf = ∏ i : slice s true,
      μ.weight (y ⟨(true,i),(mem_slice_iff s true i).mp i.property⟩) from
    inner_fibre D σf μ decode_f hf s true hs y]
  let f : Bool × Fin q → ℝ := fun a =>
    μ.weight (if h : a ∈ s then y ⟨a,h⟩ else Classical.choice μ.nonempty)
  change _ = ∏ p : s, μ.weight (y p)
  calc
    _ = ∏ b : Bool, ∏ i : slice s b,
        μ.weight (y ⟨(b,i),(mem_slice_iff s b i).mp i.property⟩) := by
      simp only [Fintype.prod_bool]
      ring
    _ = ∏ b : Bool, ∏ a ∈ s.filter (fun a => a.1=b), f a := by
      apply Finset.prod_congr rfl
      intro b _
      exact slice_product s b μ y
    _ = ∏ a ∈ s, f a :=
      Finset.prod_fiberwise_of_maps_to (s := s) (t := Finset.univ) (g := Prod.fst)
        (by intro a ha; exact Finset.mem_univ _) f
    _ = ∏ p : s, f p := Finset.prod_subtype s (by intro a; rfl) f
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p _
      simp [f,p.property]

end CurrentAdditive.V42HeterogeneousPairLaw

#print axioms CurrentAdditive.V42HeterogeneousPairLaw.concat_dwise

