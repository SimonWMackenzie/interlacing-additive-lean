import CurrentAdditive.GeneratedOwnerRowMarginal
import Paper2.ProtectedIncomingTemplateLaw

/-! Exact bounded joint law of the actual triple-stream indexed row source. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix

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

variable {G V Aux X Y : Type*}
  [Fintype G] [Fintype V] [Fintype Aux]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [DecidableEq G] [DecidableEq V] [DecidableEq Aux]
  {D q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  (μI : PositiveRationalLaw (G × (V ⊕ Aux)))

private def rowOfTripleJoint
    (z : (Fin s ⊕ (G × (V ⊕ Aux))) × (X × src.inner.Label)) :
    Row (I := G × (V ⊕ Aux)) src :=
  match z.1 with
  | .inl p => .inl (p, z.2.2)
  | .inr item => .inr (item, z.2.1)

/-- Every at-most-D joint projection of the actual independent complete
metadata/base/selector indices has the product of the original row law.
The retained tuple event is introduced only after this ambient equality. -/
theorem internal_streams_row_dwise
    {w : ℕ} (streams : InternalStreams src μI w) :
    IsDWise D streams.law.toFiniteLaw
      (InternalStreams.decode src streams)
      (rowLaw src μI).toFiniteLaw := by
  classical
  intro S hS E
  let ρ := streams.metadataStream.law.toFiniteLaw
  let σ := streams.baseStream.law.toFiniteLaw
  let τ := streams.selectorStream.law.toFiniteLaw
  let md := (metadataLaw (s := s) μI).toFiniteLaw
  let base := μX.toFiniteLaw
  let sel := src.inner.law.toFiniteLaw
  let raw := md.prod (base.prod sel)
  let rows := (rowLaw src μI).toFiniteLaw
  let fm : streams.metadataStream.Label → (S → Fin s ⊕ (G × (V ⊕ Aux))) :=
    fun t j => streams.metadataStream.decode t j.val
  let fb : streams.baseStream.Label → (S → X) :=
    fun t j => streams.baseStream.decode t j.val
  let fs : streams.selectorStream.Label → (S → src.inner.Label) :=
    fun t j => streams.selectorStream.decode t j.val
  have hm : ρ.PushesTo (FiniteLaw.pi (fun _ : S => md)) fm :=
    streams.metadataStream.exactLaw S hS
  have hb : σ.PushesTo (FiniteLaw.pi (fun _ : S => base)) fb :=
    streams.baseStream.exactLaw S hS
  have hsel : τ.PushesTo (FiniteLaw.pi (fun _ : S => sel)) fs :=
    streams.selectorStream.exactLaw S hS
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
  have htriple : raw.PushesTo rows (rowOfTripleJoint src) :=
    row_triple_pushes src μI
  have hrow := pi_map_pushes raw rows (rowOfTripleJoint src)
    htriple (ι := S)
  have hlaw : streams.law.toFiniteLaw = ρ.prod (σ.prod τ) := by
    simp [ρ, σ, τ, InternalStreams.law,
      PositiveRationalLaw.toFiniteLaw_prod]
  rw [hlaw]
  calc
    (ρ.prod (σ.prod τ)).prob
        (fun t => E (fun j : S => InternalStreams.decode src streams t j.val)) =
      (ρ.prod (σ.prod τ)).prob
        (fun t => E (fun j : S => rowOfTripleJoint src
          (fm t.1 j, (fb t.2.1 j, fs t.2.2 j)))) := by
        congr 1
        funext t
        congr 1
        funext j
        cases h : streams.metadataStream.decode t.1 j.val <;>
          simp [InternalStreams.decode, rowOfTripleJoint, fm, fb, fs, h]
    _ = (FiniteLaw.pi (fun _ : S => raw)).prob
          (fun v => E (fun j => rowOfTripleJoint src (v j))) :=
          hraw (fun v => E (fun j => rowOfTripleJoint src (v j)))
    _ = (FiniteLaw.pi (fun _ : S => rows)).prob E := hrow E

#print axioms internal_streams_row_dwise

end CurrentAdditive.DeterministicIndexedMatrix.Sources
