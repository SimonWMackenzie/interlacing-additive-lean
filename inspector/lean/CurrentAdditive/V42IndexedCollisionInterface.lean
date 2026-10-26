import CurrentAdditive.V39IndexedUsable

/-! The collision hypothesis stated in v42 src:profiles, on the original
indexed Gamma labels.  It concerns an interlace of R, not hardness of the
whole source matrix.  Any three distinct tail positions are allowed. -/

namespace CurrentAdditive.V42IndexedCollisionInterface

open Paper2 Paper2.SourceMatrix Paper2.SourceProjectionDiagonal Paper2.SourceProjection
open Paper2.SourceSupportFrontier
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open CurrentAdditive.V38IndexedTwoTag CurrentAdditive.V38IndexedUsable
open Workspace.Types.Protocol Workspace.Types.CommComplexity

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- The first q₁ positions, followed by any three distinct tail positions. -/
def threeTailWord (positions : Fin 3 ↪ Fin (s+1)) (γ : src.gamma.Label)
    (i : Fin (q₁+3)) : Y :=
  match finSumFinEquiv.symm i with
  | .inl r => head (src.gamma.decode γ) r
  | .inr j => tail (src.gamma.decode γ) (positions j)

/-- Original-law collision bound from src:profiles.  The retained event
is a set of complete Gamma labels; duplicate decoded lists stay distinct. -/
def ThreeTailBound (R : X → Y → Bool) (H : ℕ) (xcap : ℝ) : Prop :=
  ∀ (positions : Fin 3 ↪ Fin (s+1))
    (Rows : Set (Fin (q₁+3) × X)) (Words : Set src.gamma.Label),
    (∀ i, xcap ≤ μX.toFiniteLaw.prob (fun u => (i,u) ∈ Rows)) →
    (1/2 : ℝ) < src.gamma.law.toFiniteLaw.prob (· ∈ Words) →
    H+1 ≤ Compression.restrictionD
      (fun row γ => R row.2 (threeTailWord src positions γ row.1)) Rows Words

omit [NeZero s] in
theorem selected_cost (R : X → Y → Bool) (H : ℕ) (xcap : ℝ)
    (threeTail : ThreeTailBound src R H xcap)
    (p p' : Fin s) (hpp : p ≠ p')
    (Rows : Set (Fin (q₁+3) × X)) (Words : Set src.gamma.Label)
    (hrows : ∀ i, xcap ≤ μX.toFiniteLaw.prob (fun u => (i,u) ∈ Rows))
    (hwords : (1/2 : ℝ) < src.gamma.law.toFiniteLaw.prob (· ∈ Words)) :
    H+1 ≤ Compression.restrictionD
      (fun row γ => R row.2 (selectedGamma src p p' γ row.1)) Rows Words := by
  let e : Fin 3 ↪ Fin (s+1) :=
    ⟨collisionTailPosition p p',collisionTailPosition_injective p p' hpp⟩
  have he : threeTailWord src e = selectedGamma src p p' := by
    funext γ i
    unfold threeTailWord selectedGamma selectedCoordinateFin
    simp only [Function.comp_apply]
    cases h : finSumFinEquiv.symm i with
    | inl r => rfl
    | inr j => rfl
  simpa only [he] using threeTail e Rows Words hrows hwords

theorem marked_protocol_cost
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (H : ℕ) (xcap : ℝ) (threeTail : ThreeTailBound src R H xcap)
    (bin : Fin s) (α : Fin q₂) (K : Set src.inner.Label)
    (Base : Fin 3 → Set X) (S : Finset src.gamma.Label)
    (i₁ i₂ i₀ : I) (p p' : Fin s) (hpp : p ≠ p')
    (h₁ : activity i₁ α = some p) (h₂ : activity i₂ α = some p')
    (h₀ : activity i₀ α = none)
    (U : Set (V38IndexedTwoTag.Column src)) (V : Set (Row (I := I) src))
    (hK : ∀ z ∈ K, Sum.inl (bin,z) ∈ V)
    (hBase : ∀ t u, u ∈ Base t → Sum.inr (collisionItem i₁ i₂ i₀ t,u) ∈ V)
    (hS : ∀ γ ∈ S, Sum.inr (α,γ) ∈ U)
    (hhead : ∀ i : Fin q₁, xcap ≤ μX.toFiniteLaw.prob
      (fun u => (i,u) ∈ (fun z => src.inner.decode z α) '' K))
    (hbase : ∀ t : Fin 3, xcap ≤ μX.toFiniteLaw.prob (· ∈ Base t))
    (hSmass : (1/2 : ℝ) < SourceSupportStep.mass src.gamma.law.toFiniteLaw S)
    (P : Protocol V U Bool)
    (hP : P.Computes (fun v u => matrix src R activity ξ₀ u.val v.val)) :
    H+1 ≤ P.cost := by
  classical
  have hrows (i : Fin (q₁+3)) : xcap ≤ μX.toFiniteLaw.prob
      (fun u => (i,u) ∈ indexedWitnessRows src α K Base) := by
    change xcap ≤ μX.toFiniteLaw.prob (fun u =>
      match finSumFinEquiv.symm i with
      | .inl r => (r,u) ∈ (fun z => src.inner.decode z α) '' K
      | .inr t => u ∈ Base t)
    cases h : finSumFinEquiv.symm i with
    | inl r => simpa only [h] using hhead r
    | inr t => simpa only [h] using hbase t
  change (1/2 : ℝ) < src.gamma.law.toFiniteLaw.prob (· ∈ (S : Set _)) at hSmass
  have hl := selected_cost src R H xcap threeTail p p' hpp
    (indexedWitnessRows src α K Base) (S : Set _) hrows hSmass
  have hm := witness_source_cost_le src R activity ξ₀ bin α K Base i₁ i₂ i₀
    p p' h₁ h₂ h₀ (S : Set _) U V hK hBase hS
  have hu : Workspace.Types.CommComplexity.D (fun (v : V) (u : U) => matrix src R activity ξ₀ u.val v.val) ≤ P.cost :=
    Nat.sInf_le ⟨P,rfl,hP⟩
  have he := restrictionD_transpose (matrix src R activity ξ₀) U V
  exact hl.trans (hm.trans (he ▸ hu))

theorem no_short_remaining_protocol
    (hD : 8 ≤ D) (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (H ell b : ℕ) (hH : 2 ≤ H) (hq₂ : q₂=2^ell) (hq2 : 2 ≤ q₂) (hb : b < q₂)
    (x xcap : ℝ) (hx : 0 < x) (hsmall : 2*(q₂ : ℝ)*x ≤ 1/8)
    (hprofileA : V38RestrictionProfiles.TwoThresholdProfile (Sources.A src R)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw x (H : ℤ))
    (threeTail : ThreeTailBound src R H xcap)
    (bin : Fin s) (K : Set src.inner.Label) (V : Set (Row (I := I) src))
    (hK : ∀ z ∈ K, Sum.inl (bin,z) ∈ V)
    (hKmass : (998/1000 : ℝ) < src.inner.law.toFiniteLaw.prob (· ∈ K))
    (initial : State V (V38IndexedTwoTag.Column src) (Fin q₂) src.gamma.Label)
    (hcost : initial.protocol.cost ≤ H+ell)
    (hcorrect : ∀ v c, c ∈ initial.columns → initial.protocol.eval v c = matrix src R activity ξ₀ c v.val)
    (hcount : initial.coordinates.card+b=q₂) (hexcess : b < initial.attachments.card)
    (hmarked : initial.attachments ⊆ initial.coordinates)
    (hmass : ∀ α ∈ initial.coordinates, (3/4 : ℝ) ≤
      SourceSupportStep.mass src.gamma.law.toFiniteLaw (initial.support α))
    (hreaches : ∀ α ∈ initial.coordinates, ∀ γ ∈ initial.support α, Sum.inr (α,γ) ∈ initial.columns)
    (hhead : ∀ α ∈ initial.attachments, ∀ i : Fin q₁, xcap ≤ μX.toFiniteLaw.prob
      (fun u => (i,u) ∈ (fun z => src.inner.decode z α) '' K))
    (hcollision : ∀ α ∈ initial.attachments, ∃ (i₁ i₂ i₀ : I) (p p' : Fin s), p ≠ p' ∧
      activity i₁ α = some p ∧ activity i₂ α = some p' ∧ activity i₀ α = none ∧
      ∀ t : Fin 3, xcap ≤ μX.toFiniteLaw.prob
        (fun u => Sum.inr (collisionItem i₁ i₂ i₀ t,u) ∈ V)) : False := by
  classical
  let F := fun (v : Row (I := I) src) (c : V38IndexedTwoTag.Column src) => matrix src R activity ξ₀ c v
  let B := Sources.A src R
  let row := fun z : src.inner.Label => (Sum.inl (bin,z) : Row (I := I) src)
  let input := fun (α : Fin q₂) (γ : src.gamma.Label) => (Sum.inr (α,γ) : V38IndexedTwoTag.Column src)
  have hentry : ∀ z γ α, F (row z) (input α γ) = B γ (src.inner.decode z α) := by intros; rfl
  have hwise : IsDWise 8 src.inner.law.toFiniteLaw src.inner.decode
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw := by
    intro Q hQ E; exact src.inner.exactLaw Q (hQ.trans hD) E
  apply V38Collision.no_short_actual_protocol src.gamma.law.toFiniteLaw input
    (fun (v : V) c => F v.val c) q₂ b ell H hq₂ hq2 hb initial
    (by omega) hcount hexcess x hx hsmall hcost hcorrect hmarked hmass hreaches
  · intro U P hP α S hS hSmass
    exact V38LocalDiagram.before_alice_cost src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      src.inner.law.toFiniteLaw F B row input src.inner.decode hentry
      (codeSource_coordinate_pushes _ src.inner (by omega))
      H x hprofileA K V hK (by linarith) U P hP α S hS hSmass
  · intro U query
    exact V38LocalDiagram.after_alice_cost src.gamma.law
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX) src.inner.law.toFiniteLaw
      F B row input src.inner.decode hentry hwise H x hH hx hprofileA K V hK hKmass U query
  · intro U P hP α hα S _hsub hS hSmass
    obtain ⟨i₁,i₂,i₀,p,p',hpp,h₁,h₂,h₀,hbase⟩ := hcollision α hα
    let Base : Fin 3 → Set X := fun t => {u | Sum.inr (collisionItem i₁ i₂ i₀ t,u) ∈ V}
    exact marked_protocol_cost src R activity ξ₀ H xcap threeTail bin α K Base S
      i₁ i₂ i₀ p p' hpp h₁ h₂ h₀ U V hK (fun _ _ h => h) hS
      (hhead α hα) hbase hSmass P hP

theorem no_short_with_usable_collision_coordinates
    (hD : 8 ≤ D) (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (H ell : ℕ) (hH : 2 ≤ H) (hq₂ : q₂=2^ell) (hq2 : 2 ≤ q₂)
    (x xcap : ℝ) (hx : 0 < x) (hsmall : 2*(q₂ : ℝ)*x ≤ 1/8)
    (hprofileA : V38RestrictionProfiles.TwoThresholdProfile (Sources.A src R)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw x (H : ℤ))
    (threeTail : ThreeTailBound src R H xcap)
    (bin : Fin s) (K : Set src.inner.Label) (A : Set (Row (I := I) src))
    (U : Set (V38IndexedTwoTag.Column src)) (hK : ∀ z ∈ K, Sum.inl (bin,z) ∈ A)
    (hKmass : (998/1000 : ℝ) < src.inner.law.toFiniteLaw.prob (· ∈ K))
    (Marks : Finset (Fin q₂)) (hMarks : Marks ⊆ Finset.univ \ bad src K U xcap)
    (hexcess : (bad src K U xcap).card < Marks.card)
    (hcollision : ∀ α ∈ Marks, ∃ (i₁ i₂ i₀ : I) (p p' : Fin s), p ≠ p' ∧
      activity i₁ α = some p ∧ activity i₂ α = some p' ∧ activity i₀ α = none ∧
      ∀ t : Fin 3, xcap ≤ μX.toFiniteLaw.prob (fun u => Sum.inr (collisionItem i₁ i₂ i₀ t,u) ∈ A))
    (P : Protocol A (V38IndexedTwoTag.Column src) Bool) (hcost : P.cost ≤ H+ell)
    (hcorrect : ∀ a c, c ∈ U → P.eval a c = matrix src R activity ξ₀ c a.val) : False := by
  classical
  let Bad := bad src K U xcap
  let initial := initialState src P U Bad Marks
  obtain ⟨hcount,hmass,hreaches,hhead⟩ := initial_facts src P K U xcap Marks
  change initial.coordinates.card+Bad.card=q₂ at hcount
  change Bad.card < Marks.card at hexcess
  have hm : Marks.card ≤ initial.coordinates.card := Finset.card_le_card hMarks
  have hb : Bad.card < q₂ := by omega
  apply no_short_remaining_protocol src hD R activity ξ₀ H ell Bad.card hH hq₂ hq2 hb
    x xcap hx hsmall hprofileA threeTail bin K A hK hKmass initial hcost hcorrect hcount hexcess
    hMarks hmass hreaches
  · intro α hα i; exact hhead α (hMarks hα) i
  · exact hcollision

#print axioms selected_cost
#print axioms marked_protocol_cost
#print axioms no_short_remaining_protocol
#print axioms no_short_with_usable_collision_coordinates

end CurrentAdditive.V42IndexedCollisionInterface

