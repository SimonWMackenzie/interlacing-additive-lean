import Paper2.SourceLaws
import Paper2.SourceProjection
import Paper2.PairedSelectorMatrixProjection

/-!
# Actual-input adapters for the two-stream matrix

Frozen v12 Section 5, `res:two-stream`, lines 134--201. These lemmas
transport joint laws and exhibit restrictions on surviving original labels.
They supply neither a protocol frontier nor a communication lower bound.
-/

namespace Paper2.TwoStreamMatrix

open Workspace.Types.CommComplexity
open SourceMatrix SourceProjection

variable {J S Rw Ω F E : Type*} [Fintype J] [Fintype S]
  [Fintype Rw] [Fintype Ω] [Fintype F] [Fintype E] {s n : ℕ}

/-- Selecting distinct coordinates of the whole ordinary tuple preserves
their joint iid law. The premise is a law on the whole tuple, not marginal
laws for its separate coordinates. -/
theorem selected_joint_pushes (ν : FiniteLaw J) (κ : FiniteLaw Ω)
    (Φ : Ω → Fin s → J)
    (hΦ : κ.PushesTo (ν.iid s) Φ)
    (e : Fin n → Fin s) (he : Function.Injective e) :
    κ.PushesTo (ν.iid n) (fun c j => Φ c (e j)) := by
  intro U
  calc
    κ.prob (fun c => U (fun j => Φ c (e j))) =
        (ν.iid s).prob (fun z => U (fun j => z (e j))) :=
      hΦ (fun z => U (fun j => z (e j)))
    _ = (ν.iid n).prob U := iid_restrict_pushes ν e he U

theorem selected_joint_mass (ν : FiniteLaw J) (κ : FiniteLaw Ω)
    (Φ : Ω → Fin s → J)
    (hΦ : κ.PushesTo (ν.iid s) Φ)
    (e : Fin n → Fin s) (he : Function.Injective e) (O : Set Ω) :
    κ.prob (· ∈ O) ≤
      (ν.iid n).prob (· ∈ (fun c j => Φ c (e j)) '' O) :=
  FiniteLaw.prob_le_image _ _ _ (selected_joint_pushes ν κ Φ hΦ e he) O

/-- The literal source's unrestricted ordinary carrier has the entire
product law on its second component. -/
theorem raw_joint_pushes {Y : Type*} [Fintype Y]
    (ν : PositiveRationalLaw Y) (q₁ q₂ s : ℕ) [NeZero q₂] :
    (SourceLaws.rawLaw ν q₁ q₂ s).toFiniteLaw.PushesTo
      ((SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw.iid s)
      (fun Z : RawColumn q₁ q₂ s Y => Z.2) := by
  change ((ν.iid (s + 1)).prod ((SourceLaws.outerLaw ν q₁ q₂ s).iid s)).toFiniteLaw.PushesTo
    ((SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw.iid s) Prod.snd
  rw [PositiveRationalLaw.toFiniteLaw_prod, PositiveRationalLaw.toFiniteLaw_iid]
  rw [PositiveRationalLaw.toFiniteLaw_iid (SourceLaws.outerLaw ν q₁ q₂ s) s]
  exact FiniteLaw.prod_snd_pushesTo
    (ν.toFiniteLaw.iid (s + 1))
    ((SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw.iid s)

/-- The frozen raw law therefore supplies the joint selected-coordinate
event used by the outer-bin row ladder. -/
theorem raw_selected_joint_mass {Y : Type*} [Fintype Y]
    (ν : PositiveRationalLaw Y) (q₁ q₂ s : ℕ) [NeZero q₂]
    (e : Fin n → Fin s) (he : Function.Injective e)
    (O : Set (RawColumn q₁ q₂ s Y)) :
    (SourceLaws.rawLaw ν q₁ q₂ s).toFiniteLaw.prob (· ∈ O) ≤
      ((SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw.iid n).prob
        (· ∈ (fun Z j => Z.2 (e j)) '' O) :=
  selected_joint_mass _ _ _ (raw_joint_pushes ν q₁ q₂ s) e he O

/-- First projection of an ambient joint paired law has the original
selector law, even when the retained event is correlated. -/
theorem paired_first_pushes (μ : FiniteLaw S) (κ : FiniteLaw E)
    (ζ : E → S × S) (hζ : κ.PushesTo (μ.prod μ) ζ) :
    κ.PushesTo μ (fun a => (ζ a).1) := by
  intro U
  calc
    κ.prob (fun a => U (ζ a).1) =
        (μ.prod μ).prob (fun z => U z.1) := hζ (fun z => U z.1)
    _ = μ.prob U := by
      rw [FiniteLaw.prod_prob μ μ (fun x _ => U x)]
      simp only [FiniteLaw.prob]
      simp [μ.total]

/-- An ambient paired subset is no heavier than its first-selector image. -/
theorem paired_mass_le_first_image (μ : FiniteLaw S) (κ : FiniteLaw E)
    (ζ : E → S × S) (hζ : κ.PushesTo (μ.prod μ) ζ) (P : Set E) :
    κ.prob (· ∈ P) ≤ μ.prob (· ∈ (fun a => (ζ a).1) '' P) :=
  FiniteLaw.prob_le_image _ _ _ (paired_first_pushes μ κ ζ hζ) P

/-- The foreign family is measured in its own ambient law; tagging does
not change the lower bound on its projected coordinate image. -/
theorem foreign_image_mass (ν : FiniteLaw J) (κ : FiniteLaw F)
    (ψ : F → J) (hψ : κ.PushesTo ν ψ) (G : Set F) :
    κ.prob (· ∈ G) ≤ ν.prob (· ∈ ψ '' G) :=
  FiniteLaw.prob_le_image _ _ _ hψ G

/-- A retained actual bin exposes `T` on the image of its original rows
and ordinary columns. Representatives are chosen once for each image label. -/
theorem one_bin_D_le (T : S → J → Bool) (M : Rw → (Ω ⊕ F) → Bool)
    (bin : Rw → Fin s) (selector : Rw → S) (Φ : Ω → Fin s → J)
    (hordinary : ∀ r c, M r (.inl c) = T (selector r) (Φ c (bin r)))
    (i : Fin s) (R : Set Rw) (O : Set Ω)
    (hbin : ∀ r ∈ R, bin r = i) :
    Compression.restrictionD T (selector '' R) ((fun c => Φ c i) '' O) ≤
      Compression.restrictionD M R (Sum.inl '' O) := by
  classical
  let row : (selector '' R) → R := representative selector R
  let col : ((fun c => Φ c i) '' O) → (Sum.inl '' O : Set (Ω ⊕ F)) :=
    fun b => ⟨Sum.inl (representative (fun c => Φ c i) O b).val,
      ⟨_, (representative (fun c => Φ c i) O b).property, rfl⟩⟩
  have heq : (fun (a : selector '' R) (b : (fun c => Φ c i) '' O) => T a.val b.val) =
      (fun a b => M (row a).val (col b).val) := by
    funext a b
    change T a.val b.val = M (row a).val
      (.inl (representative (fun c => Φ c i) O b).val)
    rw [hordinary, hbin _ (row a).property,
      representative_maps selector R a,
      representative_maps (fun c => Φ c i) O b]
  change Workspace.Types.CommComplexity.D
    (fun (a : selector '' R) (b : (fun c => Φ c i) '' O) => T a.val b.val) ≤ _
  rw [heq]
  exact Workspace.ProofLemmas.SublemmaPrecompNoIncrease
    (fun (a : R) (b : (Sum.inl '' O : Set (Ω ⊕ F))) => M a.val b.val) row col

/-- Distinct actual outer bins expose a full interlace of `T`. The
selected ordinary-column image is one joint event, not a product of its
coordinate images. `lift` chooses original rows independently of columns. -/
theorem many_bin_D_le (T : S → J → Bool) (M : Rw → (Ω ⊕ F) → Bool)
    (bin : Rw → Fin s) (selector : Rw → S) (Φ : Ω → Fin s → J)
    (hordinary : ∀ r c, M r (.inl c) = T (selector r) (Φ c (bin r)))
    (e : Fin n → Fin s) (R : Set Rw) (O : Set Ω)
    (A : Set (Fin n × S)) (lift : Fin n × S → Rw)
    (hlift : ∀ a ∈ A, lift a ∈ R ∧ bin (lift a) = e a.1 ∧ selector (lift a) = a.2) :
    Compression.restrictionD (fullInterlace T n) A
        ((fun c j => Φ c (e j)) '' O) ≤
      Compression.restrictionD M R (Sum.inl '' O) := by
  have h := restrictionD_projected_le
    (fun r c => M r (.inl c)) (fullInterlace T n) lift
    (fun c j => Φ c (e j)) R O A
    (fun a ha => (hlift a ha).1)
    (by
      intro a ha c hc
      rcases hlift a ha with ⟨_, hb, hs⟩
      simp only [fullInterlace_apply, hordinary, hb, hs])
  have hmap := restrictionD_map_le M id (Sum.inl : Ω → Ω ⊕ F)
    R (Sum.inl '' O) R O
    (by intro r hr; exact hr)
    (by intro c hc; exact ⟨c, hc, rfl⟩)
  exact h.trans hmap

/-- The two tags remain distinct even if they carry the same projected
`J`-label. This is the paired-selector matrix in abstract `T` notation. -/
def pairedMatrix (T : S → J → Bool) : (S × S) → (Bool × J) → Bool :=
  fun z c => T (if c.1 then z.2 else z.1) c.2

/-- The ordinary and foreign carriers are disjoint tags after projection. -/
def tagProjection (Φ : Ω → Fin s → J) (ψ : F → J) (star : Fin s) :
    (Ω ⊕ F) → Bool × J
  | .inl c => (false, Φ c star)
  | .inr f => (true, ψ f)

/-- A paired restriction uses one original row for each retained whole
selector pair and one original tagged column for each projected label.
The premise `hentry` is solely a pointwise entry identity on actual labels. -/
theorem paired_D_le (T : S → J → Bool) (M : Rw → (Ω ⊕ F) → Bool)
    (ι : E → Rw) (ζ : E → S × S)
    (π : (Ω ⊕ F) → Bool × J)
    (P : Set E) (R : Set Rw) (C : Set (Ω ⊕ F))
    (hι : ∀ a ∈ P, ι a ∈ R)
    (hentry : ∀ a ∈ P, ∀ c ∈ C, M (ι a) c = pairedMatrix T (ζ a) (π c)) :
    Compression.restrictionD (pairedMatrix T) (ζ '' P) (π '' C) ≤
      Compression.restrictionD M R C := by
  classical
  let row : (ζ '' P) → R := fun a =>
    ⟨ι (representative ζ P a).val, hι _ (representative ζ P a).property⟩
  let col : (π '' C) → C := representative π C
  have heq : (fun (a : ζ '' P) (b : π '' C) => pairedMatrix T a.val b.val) =
      (fun a b => M (row a).val (col b).val) := by
    funext a b
    change pairedMatrix T a.val b.val =
      M (ι (representative ζ P a).val) (col b).val
    rw [hentry _ (representative ζ P a).property _ (col b).property,
      representative_maps ζ P a, representative_maps π C b]
  change Workspace.Types.CommComplexity.D
    (fun (a : ζ '' P) (b : π '' C) => pairedMatrix T a.val b.val) ≤ _
  rw [heq]
  exact Workspace.ProofLemmas.SublemmaPrecompNoIncrease
    (fun (a : R) (b : C) => M a.val b.val) row col

/-- The paired adapter with precisely the two actual entry rules from
the frozen source. Other-bin foreign entries are wholly unconstrained. -/
theorem paired_tagged_D_le (T : S → J → Bool) (M : Rw → (Ω ⊕ F) → Bool)
    (bin : Rw → Fin s) (selector : Rw → S)
    (Φ : Ω → Fin s → J) (ψ : F → J) (star : Fin s)
    (ι : E → Rw) (ζ : E → S × S)
    (hordinary : ∀ r c, M r (.inl c) = T (selector r) (Φ c (bin r)))
    (hstar : ∀ a, bin (ι a) = star ∧ selector (ι a) = (ζ a).1)
    (hforeign : ∀ a f, M (ι a) (.inr f) = T (ζ a).2 (ψ f))
    (P : Set E) (R : Set Rw) (C : Set (Ω ⊕ F))
    (hι : ∀ a ∈ P, ι a ∈ R) :
    Compression.restrictionD (pairedMatrix T) (ζ '' P)
        ((tagProjection Φ ψ star) '' C) ≤
      Compression.restrictionD M R C := by
  apply paired_D_le T M ι ζ (tagProjection Φ ψ star) P R C hι
  intro a ha c hc
  cases c with
  | inl c =>
      simp only [tagProjection, pairedMatrix, Bool.false_eq_true, ↓reduceIte]
      rw [hordinary, (hstar a).1, (hstar a).2]
  | inr f =>
      simp only [tagProjection, pairedMatrix, ↓reduceIte]
      exact hforeign a f

end Paper2.TwoStreamMatrix

#print axioms Paper2.TwoStreamMatrix.raw_joint_pushes
#print axioms Paper2.TwoStreamMatrix.raw_selected_joint_mass
#print axioms Paper2.TwoStreamMatrix.paired_first_pushes
#print axioms Paper2.TwoStreamMatrix.one_bin_D_le
#print axioms Paper2.TwoStreamMatrix.many_bin_D_le
#print axioms Paper2.TwoStreamMatrix.paired_tagged_D_le
