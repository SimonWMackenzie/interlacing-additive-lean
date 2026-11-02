import Paper2.ProtectedDensityGroups
import Paper2.ReferenceColumnStep
import Paper2.ReferenceProjectionMass
import Paper2.RestorationCoverParameters
import Paper2.TemplateProjection
import Paper2.RationalTupleTransport
import Paper2.SourceLawBinding

/-!
# Incoming protected column selection

Frozen v12 `res:incoming`, lines 322--386. The full retained tuple event may
correlate all coordinates. Cover selection and first-Bob restriction act on
its actual coordinate projection, never on an independent replacement event.
-/

namespace Paper2.ProtectedIncomingColumns

open Paper2.ProductProjections Paper2.ReferenceCapacity

/-- A dense original coordinate group avoids the cover of all poor `u`-sets.
The selected coordinates retain their original labels. -/
theorem good_projection_in_dense_group {K : Type*} [Fintype K]
    {w : ℕ} (κ : FiniteLaw K) (Y' : Set (Fin w → K))
    (V : Finset (Fin w)) (u B : ℕ) (Q : ℕ)
    (hQ : 0 < Q) (hB : B = RestorationCoverParameters.B2 Q)
    (hlarge : u * B < V.card)
    (hmass : RestorationCoverParameters.theta Q ≤ (κ.iid w).prob (· ∈ Y')) :
    ∃ S : Finset (Fin w), S ⊆ V ∧ S.card = u ∧
      (99 / 100 : ℝ) ≤ projectionMass (fun _ => κ) (· ∈ Y') S := by
  classical
  have hBpos : 1 ≤ B := by simp [hB, RestorationCoverParameters.B2]; omega
  have hgap : (99 / 100 : ℝ) ^ B < RestorationCoverParameters.theta Q := by
    simpa [hB] using RestorationCoverParameters.B2_gap hQ
  obtain ⟨C, hC, hcover⟩ := projection_cover (fun _ : Fin w => κ)
    (· ∈ Y') u B hBpos (RestorationCoverParameters.theta Q) (99 / 100)
    (by simpa [RestorationCovers.pi_const_prob] using hmass) hgap
  have hroom : u ≤ (V \ C).card := by
    have hcovercard : V.card ≤ (V \ C).card + C.card := by
      calc
        V.card = (V \ C).card + (V ∩ C).card := by
          simpa [Nat.add_comm] using (Finset.card_sdiff_add_card_inter V C).symm
        _ ≤ (V \ C).card + C.card :=
          Nat.add_le_add_left (Finset.card_le_card Finset.inter_subset_right) _
    have hidentity : u * B = u * (B - 1) + u := by
      calc
        u * B = u * ((B - 1) + 1) := by congr 1; omega
        _ = u * (B - 1) + u := by ring
    omega
  obtain ⟨S, hsub, hcard⟩ := Finset.exists_subset_card_eq hroom
  refine ⟨S, hsub.trans Finset.sdiff_subset, hcard, ?_⟩
  have hdis : Disjoint S C := Finset.disjoint_left.mpr (by
    intro i hi hCi
    exact (Finset.mem_sdiff.mp (hsub hi)).2 hCi)
  by_contra hbad
  exact (hcover S hcard (lt_of_not_ge hbad)) hdis

/-- The actual first Bob query has a child retaining half the selected
projected mass, even if the two child projections overlap. -/
theorem good_projected_child {K : Type*} [Fintype K]
    {w u : ℕ} (κ : FiniteLaw K) (Y' : Set (Fin w → K))
    (e : Fin u → Fin w) (he : Function.Injective e)
    (query : (Fin w → K) → Bool)
    (hgood : (99 / 100 : ℝ) ≤
      projectionMass (fun _ => κ) (· ∈ Y') (Finset.univ.image e)) :
    ∃ b : Bool, (99 / 200 : ℝ) ≤
      (κ.iid u).prob (· ∈ selectedColumns e
        (ReferenceColumnStep.columnChild Y' query b)) := by
  have hmass : (99 / 100 : ℝ) ≤
      (κ.iid u).prob (· ∈ selectedColumns e Y') := by
    rwa [ReferenceProjectionMass.projectionMass_eq_selectedColumns_of_injective
      κ Y' (Finset.univ.image e) e he rfl] at hgood
  obtain ⟨b, hb⟩ := ReferenceColumnStep.exists_dense_projected_child
    (κ.iid u) (fun y : Fin w → K => fun t => y (e t)) Y' query
    (99 / 100) hmass
  refine ⟨b, ?_⟩
  simpa only [show (99 / 100 : ℝ) / 2 = 99 / 200 by norm_num,
    selectedColumns] using hb

/-- The exact selector-tuple image after fixing one original template bin
at each selected original coordinate. -/
def selectorImage {V X : Type*} {q₁ q₂ s w k : ℕ}
    (U : Set (Fin w → SourceMatrix.RawRow q₁ q₂ s X
      (SourceConstruction.Items s V)))
    (e : Fin k → Fin w) (p : Fin k → Fin s) :
    Set (Fin k → SourceMatrix.Template q₁ q₂ X) :=
  fun z => ∃ y ∈ U, ∀ t, y (e t) = .inl (p t, z t)

/-- Every selector label is represented by a single surviving whole original
tuple, not by independently chosen coordinate completions. -/
noncomputable def selectorRepresentative {V X : Type*} {q₁ q₂ s w k : ℕ}
    (U : Set (Fin w → SourceMatrix.RawRow q₁ q₂ s X
      (SourceConstruction.Items s V)))
    (e : Fin k → Fin w) (p : Fin k → Fin s)
    (z : selectorImage U e p) :
    Fin w → SourceMatrix.RawRow q₁ q₂ s X (SourceConstruction.Items s V) :=
  Classical.choose z.property

theorem selectorRepresentative_survives {V X : Type*} {q₁ q₂ s w k : ℕ}
    (U : Set (Fin w → SourceMatrix.RawRow q₁ q₂ s X
      (SourceConstruction.Items s V)))
    (e : Fin k → Fin w) (p : Fin k → Fin s)
    (z : selectorImage U e p) :
    selectorRepresentative U e p z ∈ U :=
  (Classical.choose_spec z.property).1

theorem selectorRepresentative_coordinates {V X : Type*} {q₁ q₂ s w k : ℕ}
    (U : Set (Fin w → SourceMatrix.RawRow q₁ q₂ s X
      (SourceConstruction.Items s V)))
    (e : Fin k → Fin w) (p : Fin k → Fin s)
    (z : selectorImage U e p) (t : Fin k) :
    selectorRepresentative U e p z (e t) = .inl (p t, z.val t) :=
  (Classical.choose_spec z.property).2 t

theorem selectorRepresentative_injective {V X : Type*} {q₁ q₂ s w k : ℕ}
    (U : Set (Fin w → SourceMatrix.RawRow q₁ q₂ s X
      (SourceConstruction.Items s V)))
    (e : Fin k → Fin w) (p : Fin k → Fin s) :
    Function.Injective (selectorRepresentative U e p) := by
  intro z z' h
  apply Subtype.ext
  funext t
  have hz := selectorRepresentative_coordinates U e p z t
  have hz' := selectorRepresentative_coordinates U e p z' t
  rw [h] at hz
  have hh : (p t, z.val t) = (p t, z'.val t) := Sum.inl.inj (hz.symm.trans hz')
  exact congrArg Prod.snd hh

/-- The selected original completion exposes the actual template entry at
every selected coordinate and fixed bin, for every unrestricted source row. -/
theorem selectorRepresentative_unrestricted_entry
    {V X Y : Type*} {q₁ q₂ s w k : ℕ} [NeZero s]
    (base : X → Y → Bool)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ₀ : SourceMatrix.Tail s Y)
    (U : Set (Fin w → SourceMatrix.RawRow q₁ q₂ s X
      (SourceConstruction.Items s V)))
    (e : Fin k → Fin w) (p : Fin k → Fin s)
    (z : selectorImage U e p) (t : Fin k)
    (Z : SourceMatrix.RawColumn q₁ q₂ s Y) :
    SourceMatrix.N base activity ξ₀ (.unrestricted Z)
      (selectorRepresentative U e p z (e t)) =
      SourceMatrix.T base (z.val t) (Z.2 (p t)) := by
  rw [selectorRepresentative_coordinates U e p z t]
  rfl

noncomputable def copyRetained {K : Type*} [Fintype K]
    (χ : PositiveRationalLaw K) (n : ℕ) (U : Set (Fin n → K)) :
    Finset (Fin n → χ.Copies) := by
  classical
  exact Finset.univ.filter (fun z => χ.forgetTuple n z ∈ U)

noncomputable def copyFamily {K : Type*} [Fintype K]
    (χ : PositiveRationalLaw K) (E : K → Prop) : Finset χ.Copies := by
  classical
  exact Finset.univ.filter (fun z => E (χ.forget z))

noncomputable def copyProjectionDensity {K : Type*} [Fintype K]
    (χ : PositiveRationalLaw K) (k : ℕ)
    (U : Set (Fin (2 * k) → K)) (E : K → Prop)
    (J : Finset (Fin (2 * k))) : ℝ := by
  classical
  exact TemplateProjection.projectionDensity
    (copyRetained χ (2 * k) U) (copyFamily χ E) J

/-- T41 applied faithfully to the uniform duplicate labels of an arbitrary
positive rational alphabet law. The original retained event is pulled back
as a *whole tuple* event, so its coordinate correlations are unchanged. -/
theorem uniform_copy_template_projection {K : Type*} [Fintype K]
    (χ : PositiveRationalLaw K) (k : ℕ) (hk : 1 ≤ k)
    (U : Set (Fin (2 * k) → K)) (E : K → Prop)
    (hE : ∃ a, E a)
    (hmass : (99 / 200 : ℝ) ≤ (χ.toFiniteLaw.iid (2 * k)).prob (· ∈ U))
    (hfamily : χ.toFiniteLaw.prob E = 255 / 256) :
    ∃ J : Finset (Fin (2 * k)), J.card = k ∧
      (12 / 25 : ℝ) < copyProjectionDensity χ k U E J := by
  classical
  let P := copyRetained χ (2 * k) U
  let T := copyFamily χ E
  have hT : T.Nonempty := by
    obtain ⟨a, ha⟩ := hE
    obtain ⟨z, rfl⟩ := χ.forget_surjective a
    exact ⟨z, by simp [T, copyFamily, ha]⟩
  have hcopy : χ.uniformCopies = FiniteLaw.uniform χ.Copies := by
    apply FiniteLaw.eq_of_weight_eq
    funext z
    simp only [PositiveRationalLaw.uniformCopies, FiniteLaw.uniform, χ.card_copies]
  have hP : TemplateProjection.retainedDensity P =
      (χ.toFiniteLaw.iid (2 * k)).prob (· ∈ U) := by
    change (P.card : ℝ) / (Fintype.card χ.Copies : ℝ) ^ (2 * k) = _
    rw [← TemplateProjection.wordLaw_prob_finset,
      TemplateProjection.wordLaw, ← hcopy]
    simpa [P, copyRetained] using
      χ.uniformCopies_iid_prob_preimage (2 * k) (· ∈ U)
  have hlambda : TemplateProjection.lambda T = 255 / 256 := by
    rw [show TemplateProjection.lambda T =
      (FiniteLaw.uniform χ.Copies).prob (· ∈ T) from
      (FiniteLaw.uniform_prob_finset T).symm]
    rw [← hcopy, show (fun z : χ.Copies => z ∈ T) =
      (fun z => E (χ.forget z)) from by funext z; simp [T, copyFamily]]
    exact (χ.uniformCopies_prob_preimage E).trans hfamily
  obtain ⟨J, hJ, hsharp, hcoarse⟩ :=
    TemplateProjection.dense_alphabet_projection k hk P T hT
  refine ⟨J, hJ, ?_⟩
  have hbound : (12 / 25 : ℝ) <
      TemplateProjection.retainedDensity P -
        2 * (1 - TemplateProjection.lambda T) := by
    rw [hP, hlambda]
    linarith
  exact hbound.trans_le (hcoarse.trans hsharp)

/-- The raw source's template family has exactly the public `255/256`
mass, so the copy-alphabet projection step applies to the actual source law. -/
theorem source_copy_template_projection
    {V X : Type*} [Fintype V] [Nonempty V] [Fintype X]
    {q₁ q₂ s : ℕ} [NeZero q₁]
    (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (k : ℕ) (hk : 1 ≤ k)
    (U : Set (Fin (2 * k) → SourceMatrix.RawRow q₁ q₂ s X
      (SourceConstruction.Items s V)))
    (hmass : (99 / 200 : ℝ) ≤
      (((SourceLawBinding.matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw).iid
        (2 * k)).prob (· ∈ U)) :
    ∃ J : Finset (Fin (2 * k)), J.card = k ∧
      (12 / 25 : ℝ) < copyProjectionDensity
        (SourceLawBinding.matrixColumnLaw (V := V) μ q₁ q₂ s hs)
        k U (fun a => SourceLawBinding.columnFamilyIndex a = 0) J := by
  let χ := SourceLawBinding.matrixColumnLaw (V := V) μ q₁ q₂ s hs
  have hfamily : χ.toFiniteLaw.prob
      (fun a => SourceLawBinding.columnFamilyIndex a = 0) = 255 / 256 :=
    (SourceLawBinding.column_family_masses (V := V) μ hs).1
  have hE : ∃ a : SourceMatrix.RawRow q₁ q₂ s X
      (SourceConstruction.Items s V),
      SourceLawBinding.columnFamilyIndex a = 0 := by
    letI : Nonempty X := μ.nonempty
    letI : Nonempty (Fin q₁) := ⟨⟨0, NeZero.pos q₁⟩⟩
    letI : Nonempty (Fin s) := ⟨⟨0, by omega⟩⟩
    exact ⟨.inl (Classical.choice inferInstance,
      fun _ => (Classical.choice inferInstance, Classical.choice inferInstance)), rfl⟩
  exact uniform_copy_template_projection χ k hk U _ hE hmass hfamily

noncomputable def restrictedCopyLaw {I Z : Type*} [Fintype I] [DecidableEq I]
    [Fintype Z] [DecidableEq Z]
    (T : Finset Z) (hT : T.Nonempty) (J : Finset I) :
    FiniteLaw (J → T) := by
  letI : Nonempty T := ⟨⟨hT.choose, hT.choose_spec⟩⟩
  exact FiniteLaw.uniform (J → T)

/-- The T41 counting density is literally uniform mass on the complete
restricted copy alphabet. An exact pushforward therefore transfers it to
the image of actual retained patterns, without replacing that image by a
product of singleton images. -/
theorem copy_projection_mass_le_image
    {I Z B : Type*} [Fintype I] [DecidableEq I]
    [Fintype Z] [DecidableEq Z] [Fintype B]
    (P : Finset (I → Z)) (T : Finset Z) (hT : T.Nonempty)
    (J : Finset I) (f : T → B) (ν : FiniteLaw (J → B))
    (hpush : (restrictedCopyLaw T hT J).PushesTo ν
      (fun y j => f (y j))) :
    TemplateProjection.projectionDensity P T J ≤
      ν.prob (· ∈ (fun y : J → T => fun j => f (y j)) ''
        (TemplateProjection.projectionSet P T J : Set (J → T))) := by
  classical
  let Q := TemplateProjection.projectionSet P T J
  letI : Nonempty T := ⟨⟨hT.choose, hT.choose_spec⟩⟩
  have hcard : Fintype.card (J → T) = T.card ^ J.card := by simp
  have hmass : TemplateProjection.projectionDensity P T J =
      (restrictedCopyLaw T hT J).prob (· ∈ (Q : Set (J → T))) := by
    change _ = (FiniteLaw.uniform (J → T)).prob (fun y => y ∈ Q)
    rw [FiniteLaw.uniform_prob_finset]
    simp only [TemplateProjection.projectionDensity, hcard, Q, Nat.cast_pow]
  rw [hmass, ← hpush]
  apply (restrictedCopyLaw T hT J).prob_mono
  intro y hy
  exact ⟨y, hy, rfl⟩

end Paper2.ProtectedIncomingColumns

#print axioms Paper2.ProtectedIncomingColumns.good_projection_in_dense_group
#print axioms Paper2.ProtectedIncomingColumns.good_projected_child
#print axioms Paper2.ProtectedIncomingColumns.selectorRepresentative_injective
#print axioms Paper2.ProtectedIncomingColumns.selectorRepresentative_unrestricted_entry
#print axioms Paper2.ProtectedIncomingColumns.uniform_copy_template_projection
#print axioms Paper2.ProtectedIncomingColumns.source_copy_template_projection
#print axioms Paper2.ProtectedIncomingColumns.copy_projection_mass_le_image
