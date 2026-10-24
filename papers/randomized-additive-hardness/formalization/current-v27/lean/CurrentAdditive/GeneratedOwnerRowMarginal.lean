import CurrentAdditive.GeneratedOwnerOtherBins
import CurrentAdditive.DeterministicIndexedCoordinates

/-! Exact single-coordinate row law of the three independent complete
indexed streams, prior to retention. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix

private theorem prod_map_pushes
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

variable {G V Aux X Y : Type*}
  [Fintype G] [Fintype V] [Fintype Aux]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [DecidableEq G] [DecidableEq V] [DecidableEq Aux]
  {D q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  (μI : PositiveRationalLaw (G × (V ⊕ Aux)))

private def rowOfTriple
    (z : (Fin s ⊕ (G × (V ⊕ Aux))) × (X × src.inner.Label)) :
    Row (I := G × (V ⊕ Aux)) src :=
  match z.1 with
  | .inl p => .inl (p, z.2.2)
  | .inr item => .inr (item, z.2.1)

/-- The advertised indexed row law is exactly the pushforward of one
independent metadata/base/selector coordinate triple. -/
theorem row_triple_pushes :
    (((metadataLaw (s := s) μI).toFiniteLaw).prod
      (μX.toFiniteLaw.prod src.inner.law.toFiniteLaw)).PushesTo
      (rowLaw src μI).toFiniteLaw (rowOfTriple src) := by
  classical
  let md := (metadataLaw (s := s) μI).toFiniteLaw
  let base := μX.toFiniteLaw
  let sel := src.inner.law.toFiniteLaw
  intro E
  apply FiniteLaw.prob_preimage_eq_of_fibres
  intro k
  cases k with
  | inl pz =>
      rcases pz with ⟨p,z⟩
      have hevent : (fun a : (Fin s ⊕ (G × (V ⊕ Aux))) ×
          (X × src.inner.Label) => rowOfTriple src a = .inl (p,z)) =
          (fun a => a.1 = .inl p ∧ a.2.2 = z) := by
        funext a
        rcases a with ⟨m, x, z'⟩
        cases m <;> simp [rowOfTriple, Prod.mk.injEq]
      rw [hevent]
      rw [FiniteLaw.prod_prob_fixed_fst md (base.prod sel) (.inl p)
        (fun bs => bs.2 = z)]
      rw [FiniteLaw.prod_prob_snd base sel (fun zz => zz = z)]
      simp [md, sel, metadataLaw, rowLaw, templateRowLaw,
        PositiveRationalLaw.toFiniteLaw, PositiveRationalLaw.prod,
        PositiveRationalLaw.uniform, Fintype.card_fin]
      ring
  | inr itemx =>
      rcases itemx with ⟨item,x⟩
      have hevent : (fun a : (Fin s ⊕ (G × (V ⊕ Aux))) ×
          (X × src.inner.Label) => rowOfTriple src a = .inr (item,x)) =
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
      simp [md, base, metadataLaw, rowLaw, sourceRowLaw,
        PositiveRationalLaw.toFiniteLaw, PositiveRationalLaw.prod]
      ring

/-- A single decoded coordinate of the actual indexed triple-stream
source has exactly the advertised original row law. -/
theorem internal_coordinate_pushes
    {w : ℕ} (streams : InternalStreams src μI w)
    (hD : 1 ≤ D) (i : Fin w) :
    streams.law.toFiniteLaw.PushesTo (rowLaw src μI).toFiniteLaw
      (fun t => InternalStreams.decode src streams t i) := by
  let ρ := streams.metadataStream.law.toFiniteLaw
  let σ := streams.baseStream.law.toFiniteLaw
  let τ := streams.selectorStream.law.toFiniteLaw
  let md := (metadataLaw (s := s) μI).toFiniteLaw
  let base := μX.toFiniteLaw
  let sel := src.inner.law.toFiniteLaw
  have hm : ρ.PushesTo md (fun t => streams.metadataStream.decode t i) :=
    codeSource_coordinate_pushes _ streams.metadataStream hD i
  have hb : σ.PushesTo base (fun t => streams.baseStream.decode t i) :=
    codeSource_coordinate_pushes _ streams.baseStream hD i
  have hs : τ.PushesTo sel (fun t => streams.selectorStream.decode t i) :=
    codeSource_coordinate_pushes _ streams.selectorStream hD i
  have hinner := prod_map_pushes σ τ base sel
    (fun t => streams.baseStream.decode t i)
    (fun t => streams.selectorStream.decode t i) hb hs
  have houter := prod_map_pushes ρ (σ.prod τ) md (base.prod sel)
    (fun t => streams.metadataStream.decode t i)
    (fun t => (streams.baseStream.decode t.1 i,
      streams.selectorStream.decode t.2 i)) hm hinner
  have hlaw : streams.law.toFiniteLaw = ρ.prod (σ.prod τ) := by
    simp [ρ, σ, τ, InternalStreams.law,
      PositiveRationalLaw.toFiniteLaw_prod]
  intro E
  rw [hlaw]
  have heq (t : InternalLabel src streams) :
      InternalStreams.decode src streams t i =
        rowOfTriple src
          (streams.metadataStream.decode t.1 i,
           (streams.baseStream.decode t.2.1 i,
            streams.selectorStream.decode t.2.2 i)) := by
    cases h : streams.metadataStream.decode t.1 i <;>
      simp [InternalStreams.decode, rowOfTriple, h]
  calc
    (ρ.prod (σ.prod τ)).prob
        (fun t => E (InternalStreams.decode src streams t i)) =
      (ρ.prod (σ.prod τ)).prob
        (fun t => E (rowOfTriple src
          (streams.metadataStream.decode t.1 i,
           (streams.baseStream.decode t.2.1 i,
            streams.selectorStream.decode t.2.2 i)))) := by
        congr 1; funext t; rw [heq]
    _ = (md.prod (base.prod sel)).prob
          (fun z => E (rowOfTriple src z)) :=
          houter (fun z => E (rowOfTriple src z))
    _ = (rowLaw src μI).toFiniteLaw.prob E :=
      row_triple_pushes src μI E

#print axioms row_triple_pushes
#print axioms internal_coordinate_pushes

/-- High original-index retention forces low loss in every one-coordinate
decoded image, without identifying duplicate source indices. -/
theorem singleton_loss_of_retained_index_mass
    {w : ℕ} (streams : InternalStreams src μI w)
    (hD : 1 ≤ D) (U : Set (InternalLabel src streams))
    (i : Fin w) (η : ℝ)
    (hU : 1 - η/2 ≤ streams.law.toFiniteLaw.prob (· ∈ U)) :
    (rowLaw src μI).toFiniteLaw.prob
      (fun k => k ∉ (InternalStreams.decode src streams · i) '' U) ≤ η/2 := by
  let ν := streams.law.toFiniteLaw
  let μ := (rowLaw src μI).toFiniteLaw
  let f : InternalLabel src streams → Row (I := G × (V ⊕ Aux)) src :=
    fun t => InternalStreams.decode src streams t i
  have himage : ν.prob (· ∈ U) ≤ μ.prob (· ∈ f '' U) :=
    FiniteLaw.prob_le_image ν μ f
      (internal_coordinate_pushes src μI streams hD i) U
  have hcomp : μ.prob (fun k => k ∉ f '' U) =
      1 - μ.prob (· ∈ f '' U) := by
    simpa using Paper2.SourceProjectionRetention.probability_complement
      μ (· ∈ f '' U)
  rw [hcomp]
  linarith

/-- The actual high-retention source law supplies all non-distinguished
selector-bin masses once the numerical loss budget is met. -/
theorem owner_other_bins_from_retained_index_mass
    {w : ℕ} (streams : InternalStreams src μI w)
    (hD : 1 ≤ D) (U : Set (InternalLabel src streams))
    (i : Fin w) (η x : ℝ)
    (hU : 1 - η/2 ≤ streams.law.toFiniteLaw.prob (· ∈ U))
    (hfloor : 2*s*x ≤ 1 - η * (s : ℝ) / (2 * (255/256 : ℝ))) :
    ∀ p b : Fin s, b ≠ p →
      2*s*x ≤ src.inner.law.toFiniteLaw.prob
        (fun z => ∃ t ∈ U,
          streams.metadataStream.decode t.1 i = .inl b ∧
          streams.selectorStream.decode t.2.2 i = z) := by
  exact owner_other_bins_from_singleton_loss src μI streams U i η x
    (singleton_loss_of_retained_index_mass src μI streams hD U i η hU)
    hfloor

#print axioms singleton_loss_of_retained_index_mass
#print axioms owner_other_bins_from_retained_index_mass

end CurrentAdditive.DeterministicIndexedMatrix.Sources
