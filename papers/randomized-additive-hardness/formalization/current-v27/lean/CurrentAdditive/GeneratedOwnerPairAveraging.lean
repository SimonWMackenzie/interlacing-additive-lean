import CurrentAdditive.GeneratedOwnerTwoStreamProfiles

/-! The fixed-bin averaging step of Appendix I for the literal indexed row law. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix

variable {G V Aux X Y : Type*}
  [Fintype G] [Fintype V] [Fintype Aux]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [DecidableEq G] [DecidableEq V] [DecidableEq Aux]
  {D q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  (μI : PositiveRationalLaw (G × (V ⊕ Aux)))

private theorem template_atom_weight (p : Fin s) (z : src.inner.Label) :
    (rowLaw src μI).toFiniteLaw.weight (.inl (p,z)) =
      (255 / 256 : ℝ) * (s : ℝ)⁻¹ * src.inner.law.toFiniteLaw.weight z := by
  simp [rowLaw, templateRowLaw, PositiveRationalLaw.toFiniteLaw,
    PositiveRationalLaw.prod, PositiveRationalLaw.uniform, Fintype.card_fin]
  ring

private theorem template_pair_prob
    (B : Set (Row (I := G × (V ⊕ Aux)) src ×
      Row (I := G × (V ⊕ Aux)) src)) :
    let χ := (rowLaw src μI).toFiniteLaw
    let σ := src.inner.law.toFiniteLaw
    (χ.prod χ).prob (fun k =>
      match k with
      | (.inl _, .inl _) => k ∈ B
      | _ => False) =
      ((255 / 256 : ℝ) * (s : ℝ)⁻¹) ^ 2 *
        ∑ p : Fin s, ∑ r : Fin s,
          (σ.prod σ).prob (fun z =>
            ((.inl (p,z.1), .inl (r,z.2)) :
              Row (I := G × (V ⊕ Aux)) src ×
                Row (I := G × (V ⊕ Aux)) src) ∈ B) := by
  classical
  dsimp
  simp only [FiniteLaw.prob, FiniteLaw.prod, Fintype.sum_prod_type,
    Fintype.sum_sum_type]
  simp only [template_atom_weight src μI]
  simp [Finset.mul_sum, pow_two]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro z' _
  split_ifs <;> ring

private theorem template_mass :
    (rowLaw src μI).toFiniteLaw.prob
      (fun k => ∃ p z, k = .inl (p,z)) = (255 / 256 : ℝ) := by
  classical
  have htotal : (∑ p : Fin s, ∑ z : src.inner.Label,
      ((templateRowLaw src).weight (p,z) : ℝ)) = 1 := by
    simpa [FiniteLaw.prob, PositiveRationalLaw.toFiniteLaw,
      Fintype.sum_prod_type] using
      (templateRowLaw src).toFiniteLaw.prob_true
  simp [FiniteLaw.prob, rowLaw, PositiveRationalLaw.toFiniteLaw,
    Fintype.sum_sum_type, Fintype.sum_prod_type,
    ← Finset.mul_sum, htotal]

private theorem prod_prob_both {A : Type*} [Fintype A]
    (κ : FiniteLaw A) (T : A → Prop) :
    (κ.prod κ).prob (fun x => T x.1 ∧ T x.2) = (κ.prob T)^2 := by
  classical
  have hprod := FiniteLaw.prod_prob κ κ (fun a b => T a ∧ T b)
  have h (a : A) : κ.prob (fun b => T a ∧ T b) =
      if T a then κ.prob T else 0 := by
    by_cases ha : T a <;> simp [ha]
  calc
    _ = ∑ a, κ.weight a * κ.prob (fun b => T a ∧ T b) := hprod
    _ = ∑ a, κ.weight a * (if T a then κ.prob T else 0) := by simp_rw [h]
    _ = (κ.prob T) * (κ.prob T) := by
      calc
        _ = ∑ a, (if T a then κ.weight a else 0) * κ.prob T := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases ha : T a <;> simp [ha]
        _ = (∑ a, if T a then κ.weight a else 0) * κ.prob T := by
          rw [Finset.sum_mul]
        _ = _ := rfl
    _ = _ := by ring

private theorem both_template_prob :
    let χ := (rowLaw src μI).toFiniteLaw
    (χ.prod χ).prob (fun k =>
      (∃ p z, k.1 = .inl (p,z)) ∧
      (∃ r z, k.2 = .inl (r,z))) = (255 / 256 : ℝ)^2 := by
  let χ := (rowLaw src μI).toFiniteLaw
  let T : Row (I := G × (V ⊕ Aux)) src → Prop :=
    fun k => ∃ p z, k = .inl (p,z)
  change (χ.prod χ).prob (fun k => T k.1 ∧ T k.2) = _
  rw [prod_prob_both, template_mass src μI]

private theorem prob_inter_lower {A : Type*} [Fintype A]
    (κ : FiniteLaw A) (E T : A → Prop) :
    κ.prob E + κ.prob T - 1 ≤ κ.prob (fun a => E a ∧ T a) := by
  classical
  have h : κ.prob E ≤ κ.prob (fun a => E a ∧ T a) +
      κ.prob (fun a => ¬ T a) := by
    unfold FiniteLaw.prob
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a _
    by_cases he : E a <;> by_cases ht : T a <;> simp [he, ht, κ.nonneg a]
  have hc : κ.prob (fun a => ¬ T a) = 1 - κ.prob T := by
    simpa using Paper2.SourceProjectionRetention.probability_complement κ T
  linarith

/-- A good two-coordinate image under the actual indexed row law has one
fixed pair of template bins with the source's selector-pair density. -/
theorem exists_dense_owner_pair_bins
    (B : Set (Row (I := G × (V ⊕ Aux)) src ×
      Row (I := G × (V ⊕ Aux)) src))
    (hgood : (99 / 100 : ℝ) ≤
      ((rowLaw src μI).toFiniteLaw.prod
        (rowLaw src μI).toFiniteLaw).prob (· ∈ B)) :
    ∃ p r : Fin s,
      ((99 / 100 : ℝ) + (255 / 256 : ℝ)^2 - 1) /
          (255 / 256 : ℝ)^2 ≤
        (src.inner.law.toFiniteLaw.prod
          src.inner.law.toFiniteLaw).prob (fun z =>
            ((.inl (p,z.1), .inl (r,z.2)) :
              Row (I := G × (V ⊕ Aux)) src ×
                Row (I := G × (V ⊕ Aux)) src) ∈ B) := by
  classical
  let χ := (rowLaw src μI).toFiniteLaw
  let σ := src.inner.law.toFiniteLaw
  let a : ℝ := ((99 / 100 : ℝ) + (255 / 256 : ℝ)^2 - 1) /
    (255 / 256 : ℝ)^2
  let f (p r : Fin s) : ℝ := (σ.prod σ).prob
    (fun z => ((.inl (p,z.1), .inl (r,z.2)) :
      Row (I := G × (V ⊕ Aux)) src ×
        Row (I := G × (V ⊕ Aux)) src) ∈ B)
  have htemplate := both_template_prob src μI
  have hinter := prob_inter_lower (χ.prod χ) (· ∈ B)
    (fun k => (∃ p z, k.1 = .inl (p,z)) ∧
      (∃ r z, k.2 = .inl (r,z)))
  have hdecomp := template_pair_prob src μI B
  have hsum : (99 / 100 : ℝ) + (255 / 256 : ℝ)^2 - 1 ≤
      ((255 / 256 : ℝ) * (s : ℝ)⁻¹)^2 *
        ∑ p : Fin s, ∑ r : Fin s, f p r := by
    have hh : (χ.prod χ).prob (fun k => k ∈ B ∧
        ((∃ p z, k.1 = .inl (p,z)) ∧
          (∃ r z, k.2 = .inl (r,z)))) =
        (χ.prod χ).prob (fun k =>
          match k with
          | (.inl _, .inl _) => k ∈ B
          | _ => False) := by
      congr 1
      funext k
      rcases k with ⟨u,v⟩
      cases u with
      | inl u =>
          cases v with
          | inl v =>
              rcases u with ⟨p,z⟩
              rcases v with ⟨r,t⟩
              simp
          | inr v => simp
      | inr u => cases v <;> simp
    dsimp [χ] at hgood htemplate hinter hdecomp
    rw [hh] at hinter
    simpa only [f] using le_trans (by linarith [hgood, htemplate])
      (le_of_eq hdecomp)
  by_contra hn
  have hall (p r : Fin s) : f p r < a := by
    exact lt_of_not_ge (fun hp => hn ⟨p,r,hp⟩)
  let p0 : Fin s := ⟨0, NeZero.pos s⟩
  have hinner (p : Fin s) : (∑ r : Fin s, f p r) < ∑ _r : Fin s, a := by
    apply Finset.sum_lt_sum
    · intro r _; exact (hall p r).le
    · exact ⟨p0, Finset.mem_univ _, hall p p0⟩
  have houter : (∑ p : Fin s, ∑ r : Fin s, f p r) <
      ∑ _p : Fin s, ∑ _r : Fin s, a := by
    apply Finset.sum_lt_sum
    · intro p _; exact (hinner p).le
    · exact ⟨p0, Finset.mem_univ _, hinner p0⟩
  have hconst : (∑ _p : Fin s, ∑ _r : Fin s, a) =
      (s : ℝ) * ((s : ℝ) * a) := by
    simp [Fintype.card_fin, nsmul_eq_mul]
  rw [hconst] at houter
  have hspos : (0 : ℝ) < s := by exact_mod_cast (NeZero.pos s)
  have hcpos : (0 : ℝ) < ((255 / 256 : ℝ) * (s : ℝ)⁻¹)^2 := by positivity
  have heq : ((255 / 256 : ℝ) * (s : ℝ)⁻¹)^2 *
      ((s : ℝ) * ((s : ℝ) * a)) = (255 / 256 : ℝ)^2 * a := by
    field_simp
  have houter' := mul_lt_mul_of_pos_left houter hcpos
  rw [heq] at houter'
  have ha : (255 / 256 : ℝ)^2 * a =
      (99 / 100 : ℝ) + (255 / 256 : ℝ)^2 - 1 := by
    dsimp [a]
    field_simp
  nlinarith [hsum, houter', ha]

#print axioms exists_dense_owner_pair_bins

/-- The pair-density conclusion is about the image of surviving *original*
indexed tuples, not a newly sampled product of surviving singleton images. -/
theorem owner_pair_image_mass_of_good_projection
    {w : ℕ} (streams : InternalStreams src μI w)
    (U : Set (InternalLabel src streams)) (i j : Fin w)
    (hgood : (99 / 100 : ℝ) ≤
      ((rowLaw src μI).toFiniteLaw.prod
        (rowLaw src μI).toFiniteLaw).prob
          (· ∈ (fun t =>
            (InternalStreams.decode src streams t i,
             InternalStreams.decode src streams t j)) '' U)) :
    ∃ p r : Fin s,
      ((99 / 100 : ℝ) + (255 / 256 : ℝ)^2 - 1) /
          (255 / 256 : ℝ)^2 ≤
        (src.inner.law.toFiniteLaw.prod
          src.inner.law.toFiniteLaw).prob
            (· ∈ ownerPairImage src streams U i j p r) := by
  classical
  obtain ⟨p, r, hmass⟩ := exists_dense_owner_pair_bins src μI _ hgood
  refine ⟨p, r, le_trans hmass ?_⟩
  apply (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).prob_mono
  intro z hz
  rcases hz with ⟨t, ht, hpair⟩
  have hi : InternalStreams.decode src streams t i = .inl (p, z.1) :=
    congrArg Prod.fst hpair
  have hj : InternalStreams.decode src streams t j = .inl (r, z.2) :=
    congrArg Prod.snd hpair
  unfold InternalStreams.decode at hi hj
  cases hmi : streams.metadataStream.decode t.1 i with
  | inl b =>
      simp only [hmi] at hi
      have hb : b = p := (Prod.mk.inj (Sum.inl.inj hi)).1
      have hz1 : streams.selectorStream.decode t.2.2 i = z.1 :=
        (Prod.mk.inj (Sum.inl.inj hi)).2
      cases hmj : streams.metadataStream.decode t.1 j with
      | inl c =>
          simp only [hmj] at hj
          have hc : c = r := (Prod.mk.inj (Sum.inl.inj hj)).1
          have hz2 : streams.selectorStream.decode t.2.2 j = z.2 :=
            (Prod.mk.inj (Sum.inl.inj hj)).2
          exact ⟨t, ht, hb ▸ hmi, hc ▸ hmj, hz1, hz2⟩
      | inr v => simp only [hmj] at hj; cases hj
  | inr v => simp only [hmi] at hi; cases hi

#print axioms owner_pair_image_mass_of_good_projection

/-- The source's good two-copy projection supplies the distinguished bins
for the literal W obstruction. The other-bin and retained-row estimates
are separate facts about the node's actual support. -/
theorem owner_to_owner_W_lower_good_projection
    {w : ℕ} (streams : InternalStreams src μI w)
    (R₀ : X → Y → Bool)
    (activity : (G × (V ⊕ Aux)) → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y)
    (i j : Fin w)
    (U : Set (InternalLabel src streams))
    (Vrows : Set (Fin w × Column src))
    (H ell a : ℕ) (hH : 2 ≤ H)
    (hq : q₂ = 2^ell) (hs : s = 2^a)
    (x : ℝ) (hx : 0 < x) (hD : 8 ≤ D)
    (hA : RestrictionProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (H : ℤ))
    (hT : RestrictionProfile (T src R₀)
      src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw
      x ((H+ell : ℕ) : ℤ))
    (hgood : (99 / 100 : ℝ) ≤
      ((rowLaw src μI).toFiniteLaw.prod
        (rowLaw src μI).toFiniteLaw).prob
          (· ∈ (fun t =>
            (InternalStreams.decode src streams t i,
             InternalStreams.decode src streams t j)) '' U))
    (hmargin : 49/64 + 2*s*x <
      ((99 / 100 : ℝ) + (255 / 256 : ℝ)^2 - 1) /
        (255 / 256 : ℝ)^2)
    (hOther : ∀ p b : Fin s, b ≠ p →
      2*s*x ≤ src.inner.law.toFiniteLaw.prob
        (fun z => ∃ t ∈ U,
          streams.metadataStream.decode t.1 i = .inl b ∧
          streams.selectorStream.decode t.2.2 i = z))
    (ε δ : ℝ)
    (hO : 1-ε ≤ (ordinaryLaw src).toFiniteLaw.prob
      (fun o => (i, .ordinary o) ∈ Vrows))
    (hF : δ ≤
      (Paper2.PairedSelectorPopulation.columnLaw src.gamma.law).toFiniteLaw.prob
        (fun f => (j, .diagonal f) ∈ Vrows))
    (hδ : δ ≤ 1)
    (hslack : 2*q₂*x+5*ε+2/q₂ ≤ δ)
    (hsmall : 2*s*x ≤ 1/8) (hpairsmall : 2*q₂*x ≤ 1/8) :
    H+ell+a+1 ≤ Compression.restrictionD
      (W src streams R₀ activity ξ₀) U Vrows := by
  obtain ⟨p, r, hPair⟩ :=
    owner_pair_image_mass_of_good_projection src μI streams U i j hgood
  exact owner_to_owner_W_lower_fixed_bins src streams R₀ activity ξ₀
    i j p r U Vrows H ell a hH hq hs x hx hD hA hT
    (((99 / 100 : ℝ) + (255 / 256 : ℝ)^2 - 1) /
      (255 / 256 : ℝ)^2) ε δ hPair hmargin
    (fun b hb => hOther p b hb) hO hF hδ hslack hsmall hpairsmall

#print axioms owner_to_owner_W_lower_good_projection

end CurrentAdditive.DeterministicIndexedMatrix.Sources
