import CurrentAdditive.V39GeneratedConstruction
import Paper2.ProtectedIncomingTemplateLaw

namespace CurrentAdditive.V39GeneratedConstruction
open Paper2 Paper2.SourceMatrix
open scoped BigOperators

theorem product_toFiniteLaw {A B : Type} [Fintype A] [Fintype B]
    (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw B) :
    (product μ ν).toFiniteLaw = μ.toFiniteLaw.prod ν.toFiniteLaw := by
  have hh : (product μ ν).toFiniteLaw.weight =
      (μ.toFiniteLaw.prod ν.toFiniteLaw).weight := by
    funext a
    simp [product, PositiveRationalLaw.toFiniteLaw, FiniteLaw.prod]
  cases h₁ : (product μ ν).toFiniteLaw
  cases h₂ : μ.toFiniteLaw.prod ν.toFiniteLaw
  simp only [h₁, h₂] at hh
  cases hh
  rfl
private theorem joint_prod_map_pushes
    {A B X Y : Type*}
    [Fintype A] [Fintype B] [Fintype X] [Fintype Y]
    (ρ : FiniteLaw A) (σ : FiniteLaw B)
    (μ : FiniteLaw X) (ν : FiniteLaw Y)
    (f : A → X) (g : B → Y)
    (hf : ρ.PushesTo μ f) (hg : σ.PushesTo ν g) :
    (ρ.prod σ).PushesTo (μ.prod ν)
      (fun z => (f z.1, g z.2)) := by
  classical
  intro E
  apply FiniteLaw.prob_preimage_eq_of_fibres
  intro ⟨x,y⟩
  have h1 : (ρ.prod σ).prob
      (fun z => (f z.1, g z.2) = (x,y)) =
      ρ.prob (fun a => f a = x) * σ.prob (fun b => g b = y) := by
    rw [show (ρ.prod σ).prob (fun z => (f z.1, g z.2) = (x,y)) =
      ∑ a, ρ.weight a * σ.prob (fun b => (f a, g b) = (x,y)) from
        FiniteLaw.prod_prob ρ σ (fun a b => (f a, g b) = (x,y))]
    simp only [Prod.mk.injEq]
    have hinner (a : A) :
        σ.prob (fun b => f a = x ∧ g b = y) =
        if f a = x then σ.prob (fun b => g b = y) else 0 := by
      by_cases ha : f a = x <;> simp [ha]
    simp_rw [hinner]
    unfold FiniteLaw.prob
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : f a = x <;> simp [ha]
  rw [h1, hf (fun a => a = x), hg (fun b => b = y)]
  simp only [FiniteLaw.prob_singleton, FiniteLaw.prod]

private theorem pi_map_pushes
    {ι A B : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype A] [Fintype B]
    (μ : FiniteLaw A) (ν : FiniteLaw B) (f : A → B)
    (hf : μ.PushesTo ν f) :
    (FiniteLaw.pi (fun _ : ι => μ)).PushesTo
      (FiniteLaw.pi (fun _ : ι => ν))
      (fun v i => f (v i)) := by
  classical
  intro E
  apply FiniteLaw.prob_preimage_eq_of_fibres
  intro y
  have heq : (fun v : ι → A => (fun i => f (v i)) = y) =
      (fun v => ∀ i, f (v i) = y i) := by
    funext v
    apply propext
    exact funext_iff
  rw [heq]
  change (FiniteLaw.pi (fun _ : ι => μ)).prob
      (fun v => ∀ i, (fun a => f a = y i) (v i)) =
    (FiniteLaw.pi (fun _ : ι => ν)).weight y
  rw [show (FiniteLaw.pi (fun _ : ι => μ)).prob
      (fun v => ∀ i, (fun a => f a = y i) (v i)) =
      ∏ i, μ.prob (fun a => f a = y i) from
        FiniteLaw.pi_prob_coordinatewise (fun _ : ι => μ)
          (fun i a => f a = y i)]
  have hweight (i : ι) : μ.prob (fun a => f a = y i) = ν.weight (y i) := by
    rw [hf (fun a => a = y i), FiniteLaw.prob_singleton]
  simp_rw [hweight]
  simp [FiniteLaw.pi]

namespace SourceData
variable {D q₁ q₂ s nx ny ni : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
  {μX : PositiveRationalLaw (Fin nx)} {μY : PositiveRationalLaw (Fin ny)}
  {μI : PositiveRationalLaw (Fin ni)}
  (src : SourceData (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
private def rowOfTriple
    (z : (Fin s ⊕ (Fin ni)) × (Fin nx × Fin src.inner.size)) :
    src.Row (ni := ni) :=
  match z.1 with
  | .inl p => .inl (p, z.2.2)
  | .inr item => .inr (item, z.2.1)

/-- The advertised indexed row law is exactly the pushforward of one
independent metadata/base/selector coordinate triple. -/
theorem row_triple_pushes :
    (((mixture (uniform s) μI).toFiniteLaw).prod
      (μX.toFiniteLaw.prod src.inner.law.toFiniteLaw)).PushesTo
      (src.rowLaw (μI := μI)).toFiniteLaw (rowOfTriple src) := by
  classical
  let md := (mixture (uniform s) μI).toFiniteLaw
  let base := μX.toFiniteLaw
  let sel := src.inner.law.toFiniteLaw
  intro E
  apply FiniteLaw.prob_preimage_eq_of_fibres
  intro k
  cases k with
  | inl pz =>
      rcases pz with ⟨p,z⟩
      have hevent : (fun a : (Fin s ⊕ (Fin ni)) ×
          (Fin nx × Fin src.inner.size) => rowOfTriple src a = .inl (p,z)) =
          (fun a => a.1 = .inl p ∧ a.2.2 = z) := by
        funext a
        rcases a with ⟨m, x, z'⟩
        cases m <;> simp [rowOfTriple, Prod.mk.injEq]
      rw [hevent]
      rw [FiniteLaw.prod_prob_fixed_fst md (base.prod sel) (.inl p)
        (fun bs => bs.2 = z)]
      rw [FiniteLaw.prod_prob_snd base sel (fun zz => zz = z)]
      simp [md, sel, mixture, rowLaw, product, uniform,
        PositiveRationalLaw.toFiniteLaw, PositiveRationalLaw.prod,
        PositiveRationalLaw.uniform, Fintype.card_fin]
      ring
  | inr itemx =>
      rcases itemx with ⟨item,x⟩
      have hevent : (fun a : (Fin s ⊕ (Fin ni)) ×
          (Fin nx × Fin src.inner.size) => rowOfTriple src a = .inr (item,x)) =
          (fun a => a.1 = .inr item ∧ a.2.1 = x) := by
        funext a
        rcases a with ⟨m, x', z⟩
        cases m <;> simp [rowOfTriple, Prod.mk.injEq]
      rw [hevent]
      rw [FiniteLaw.prod_prob_fixed_fst md (base.prod sel) (.inr item)
        (fun bs => bs.1 = x)]
      have hbase : (base.prod sel).prob (fun bs => bs.1 = x) = base.weight x := by
        have h := FiniteLaw.prod_prob_fixed_fst base sel x (fun _ => True)
        simpa using h
      rw [hbase]
      simp [md, base, mixture, rowLaw, product,
        PositiveRationalLaw.toFiniteLaw, PositiveRationalLaw.prod]
      ring

/-- Every at-most-D joint projection of the actual independent complete
metadata/base/selector indices has the product of the original row law.
The retained tuple event is introduced only after this ambient equality. -/
theorem combined_dwise
    {w : ℕ} (streams : src.Streams (μI := μI) (w := w)) :
    IsDWise D (Streams.law src streams).toFiniteLaw
      (Streams.decode src streams)
      (src.rowLaw (μI := μI)).toFiniteLaw := by
  classical
  intro S hS E
  let ρ := streams.metadata.law.toFiniteLaw
  let σ := streams.base.law.toFiniteLaw
  let τ := streams.selector.law.toFiniteLaw
  let md := (mixture (uniform s) μI).toFiniteLaw
  let base := μX.toFiniteLaw
  let sel := src.inner.law.toFiniteLaw
  let raw := md.prod (base.prod sel)
  let rows := (src.rowLaw (μI := μI)).toFiniteLaw
  let fm : Fin streams.metadata.size → (S → Fin s ⊕ (Fin ni)) :=
    fun t j => streams.metadata.decode t j.val
  let fb : Fin streams.base.size → (S → Fin nx) :=
    fun t j => streams.base.decode t j.val
  let fs : Fin streams.selector.size → (S → Fin src.inner.size) :=
    fun t j => streams.selector.decode t j.val
  have hm : ρ.PushesTo (FiniteLaw.pi (fun _ : S => md)) fm :=
    streams.metadata.exactLaw S hS
  have hb : σ.PushesTo (FiniteLaw.pi (fun _ : S => base)) fb :=
    streams.base.exactLaw S hS
  have hsel : τ.PushesTo (FiniteLaw.pi (fun _ : S => sel)) fs :=
    streams.selector.exactLaw S hS
  have hbs := joint_prod_map_pushes σ τ
    (FiniteLaw.pi (fun _ : S => base))
    (FiniteLaw.pi (fun _ : S => sel)) fb fs hb hsel
  have hmbs := joint_prod_map_pushes ρ (σ.prod τ)
    (FiniteLaw.pi (fun _ : S => md))
    ((FiniteLaw.pi (fun _ : S => base)).prod
      (FiniteLaw.pi (fun _ : S => sel)))
    fm (fun t => (fb t.1, fs t.2)) hm hbs
  have hpiInner := Paper2.ProtectedIncomingTemplateLaw.pi_prod_pushes
    (I := S) base sel
  have hid : (FiniteLaw.pi (fun _ : S => md)).PushesTo
      (FiniteLaw.pi (fun _ : S => md)) id := by
    intro E'; rfl
  have hcombineInner := joint_prod_map_pushes
    (FiniteLaw.pi (fun _ : S => md))
    ((FiniteLaw.pi (fun _ : S => base)).prod
      (FiniteLaw.pi (fun _ : S => sel)))
    (FiniteLaw.pi (fun _ : S => md))
    (FiniteLaw.pi (fun _ : S => base.prod sel))
    id (fun v j => (v.1 j, v.2 j)) hid hpiInner
  have hpiOuter := Paper2.ProtectedIncomingTemplateLaw.pi_prod_pushes
    (I := S) md (base.prod sel)
  have hcombine :
      ((FiniteLaw.pi (fun _ : S => md)).prod
        ((FiniteLaw.pi (fun _ : S => base)).prod
          (FiniteLaw.pi (fun _ : S => sel)))).PushesTo
      (FiniteLaw.pi (fun _ : S => raw))
      (fun v j => (v.1 j, (v.2.1 j, v.2.2 j))) := by
    intro E'
    calc
      _ = ((FiniteLaw.pi (fun _ : S => md)).prod
          (FiniteLaw.pi (fun _ : S => base.prod sel))).prob
            (fun v => E' (fun j => (v.1 j, v.2 j))) :=
          hcombineInner (fun v => E' (fun j => (v.1 j, v.2 j)))
      _ = (FiniteLaw.pi (fun _ : S => raw)).prob E' := hpiOuter E'
  have hraw : (ρ.prod (σ.prod τ)).PushesTo
      (FiniteLaw.pi (fun _ : S => raw))
      (fun t j => (fm t.1 j, (fb t.2.1 j, fs t.2.2 j))) := by
    intro E'
    calc
      _ = ((FiniteLaw.pi (fun _ : S => md)).prod
        ((FiniteLaw.pi (fun _ : S => base)).prod
          (FiniteLaw.pi (fun _ : S => sel)))).prob
          (fun v => E' (fun j => (v.1 j, (v.2.1 j, v.2.2 j)))) :=
          hmbs (fun v => E' (fun j => (v.1 j, (v.2.1 j, v.2.2 j))))
      _ = _ := hcombine E'
  have htriple : raw.PushesTo rows (rowOfTriple src) :=
    row_triple_pushes src (μI := μI)
  have hrow := pi_map_pushes raw rows (rowOfTriple src)
    htriple (ι := S)
  have hlaw : (Streams.law src streams).toFiniteLaw = ρ.prod (σ.prod τ) := by
    simp [ρ, σ, τ, Streams.law,
      product_toFiniteLaw]
  rw [hlaw]
  calc
    (ρ.prod (σ.prod τ)).prob
        (fun t => E (fun j : S => Streams.decode src streams t j.val)) =
      (ρ.prod (σ.prod τ)).prob
        (fun t => E (fun j : S => rowOfTriple src
          (fm t.1 j, (fb t.2.1 j, fs t.2.2 j)))) := rfl
    _ = (FiniteLaw.pi (fun _ : S => raw)).prob
          (fun v => E (fun j => rowOfTriple src (v j))) :=
          hraw (fun v => E (fun j => rowOfTriple src (v j)))
    _ = (FiniteLaw.pi (fun _ : S => rows)).prob E := hrow E


end SourceData
end CurrentAdditive.V39GeneratedConstruction
