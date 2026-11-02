import CurrentAdditive.V38RestrictionProfiles
import CurrentAdditive.IndependentStreams
import CurrentAdditive.ArbitraryPrefix
import CurrentAdditive.RestrictionBridge
import CurrentAdditive.V38CollisionConservation
import Paper2.SourceSupportCapacity

/-!
Source: selected v39 = v38, sections/robustness.tex, src:near-full,
lines 245--278. These lemmas concern actual retained labels and actual
protocols. The source's two thresholds are used without a Fin 3 upgrade.
The diagram is general enough for full words and indexed source labels.
-/

namespace CurrentAdditive.V38LocalDiagram

open Paper2 Paper2.SourceProjection Paper2.SourceSupportCapacity
open Workspace.Types.Protocol Workspace.Types.CommComplexity
open CurrentAdditive.ArbitraryPrefix

variable {A C T W J : Type*}
  [Fintype A] [Fintype C] [Fintype T] [Fintype W] [Fintype J]
  {q : ℕ}

/-- The original selector labels that send one actual Alice bit. -/
def selectorFibre (row : T → A) (K : Set T) (V : Set A)
    (query : V → Bool) (bit : Bool) : Set T :=
  {t | t ∈ K ∧ rawQuery V query (row t) = bit}

/-- Alice's chosen child is fixed before the support family or dyadic
capacity is chosen. Mass is measured in the original selector law. -/
theorem dense_selector_child (σ : FiniteLaw T) (row : T → A)
    (K : Set T) (V : Set A) (query : V → Bool)
    (hK : (998 / 1000 : ℝ) < σ.prob (· ∈ K)) :
    ∃ bit : Bool, (499 / 1000 : ℝ) <
      σ.prob (· ∈ selectorFibre row K V query bit) := by
  classical
  let f := fun t => rawQuery V query (row t)
  let bit := SourceSupportStep.heavyBit σ K.toFinset f
  have hp := SourceSupportStep.mass_partition_heavy σ K.toFinset f
  have hg := SourceSupportStep.heavy_ge_other σ K.toFinset f
  have he (b : Bool) : SourceSupportStep.mass σ
      (SourceSupportStep.fibre K.toFinset f b) =
      σ.prob (· ∈ selectorFibre row K V query b) := by
    simp only [SourceSupportStep.mass, SourceSupportStep.mem_fibre,
      Set.mem_toFinset]
    rfl
  have hm : SourceSupportStep.mass σ K.toFinset = σ.prob (· ∈ K) := by
    simp [SourceSupportStep.mass]
  rw [he, he, hm] at hp
  rw [he, he] at hg
  exact ⟨bit, by linarith⟩

/-- One genuine source fibre against retained selectors contains the
profile restriction on the actual image of the coordinate projection.
Each representative works for every word in that fibre. -/
theorem coordinate_restriction_le
    (F : A → C → Bool) (B : W → J → Bool)
    (row : T → A) (input : Fin q → W → C)
    (decode : T → Fin q → J)
    (hentry : ∀ t w i, F (row t) (input i w) = B w (decode t i))
    (i : Fin q) (K : Set T) (S : Set W) (V : Set A) (U : Set C)
    (hrow : ∀ t ∈ K, row t ∈ V)
    (hinput : ∀ w ∈ S, input i w ∈ U) :
    Compression.restrictionD B S ((fun t => decode t i) '' K) ≤
      Compression.restrictionD F V U := by
  have hp := restrictionD_projected_le
    (fun w t => F (row t) (input i w)) B id (fun t => decode t i)
    S K S (fun _ h => h) (fun w _ t _ => hentry t w i)
  have hm := restrictionD_map_le (fun c a => F a c)
    (input i) row U V S K hinput hrow
  rw [restrictionD_transpose F V U] at hm
  exact hp.trans hm

/-- Local bound (i) with precisely the source's first (3/5) threshold.
No claim about the selector distribution conditioned on K is used. -/
theorem before_alice_cost
    (μ : FiniteLaw W) (ν : FiniteLaw J) (σ : FiniteLaw T)
    (F : A → C → Bool) (B : W → J → Bool)
    (row : T → A) (input : Fin q → W → C)
    (decode : T → Fin q → J)
    (hentry : ∀ t w i, F (row t) (input i w) = B w (decode t i))
    (hmarginal : ∀ i, σ.PushesTo ν (fun t => decode t i))
    (H : ℕ) (x : ℝ)
    (hprofile : Paper2.V38RestrictionProfiles.TwoThresholdProfile B μ ν x (H : ℤ))
    (K : Set T) (V : Set A)
    (hrow : ∀ t ∈ K, row t ∈ V)
    (hK : (3 / 5 : ℝ) ≤ σ.prob (· ∈ K))
    (U : Set C) (P : Protocol V U Bool)
    (hP : P.Computes (fun a c => F a.val c.val))
    (i : Fin q) (S : Finset W)
    (hinput : ∀ w ∈ S, input i w ∈ U)
    (hS : x ≤ SourceSupportStep.mass μ S) : H ≤ P.cost := by
  classical
  have hcol := hK.trans (σ.prob_le_image ν (fun t => decode t i)
    (hmarginal i) K)
  have hfirst := (Paper2.V38RestrictionProfiles.twoThresholdProfile_iff
    B μ ν x (H : ℤ)).mp hprofile |>.1
  have hl := hfirst (S : Set W) ((fun t => decode t i) '' K) hS hcol
  have hlNat : H ≤ Compression.restrictionD B (S : Set W)
      ((fun t => decode t i) '' K) := by exact_mod_cast hl
  have hm := coordinate_restriction_le F B row input decode hentry i K
    (S : Set W) V U hrow hinput
  have hu : Compression.restrictionD F V U ≤ P.cost :=
    Nat.sInf_le ⟨P, rfl, hP⟩
  exact hlNat.trans (hm.trans hu)

/-- The interlace on the selected supports is computed by the same
actual child below Alice's query. The child-row representatives are
chosen from its retained selectors, once for all word inputs. -/
theorem after_alice_interlace_le
    (F : A → C → Bool) (B : W → J → Bool)
    (row : T → A) (input : Fin q → W → C)
    (decode : T → Fin q → J)
    (hentry : ∀ t w i, F (row t) (input i w) = B w (decode t i))
    (K : Set T) (V : Set A) (query : V → Bool) (bit : Bool)
    (hrow : ∀ t ∈ K, row t ∈ V)
    (Good : Finset (Fin q)) (Rows : Fin q → Set W) (U : Set C)
    (hinput : ∀ i ∈ Good, ∀ w ∈ Rows i, input i w ∈ U)
    (child : Protocol {a : V // query a = bit} U Bool)
    (hchild : child.Computes (fun a c => F a.val.val c.val)) :
    Compression.restrictionD (fun (a : Fin q × W) t => B a.2 (decode t a.1))
      (rowRectangle Good Rows) (selectorFibre row K V query bit) ≤ child.cost := by
  classical
  let childRow : selectorFibre row K V query bit →
      {a : V // query a = bit} := fun t =>
    ⟨⟨row t.val, hrow t.val t.property.1⟩, by
      rw [← rawQuery_of_mem V query (row t.val) (hrow t.val t.property.1)]
      exact t.property.2⟩
  let childCol : rowRectangle Good Rows → U := fun a =>
    ⟨input a.val.1 a.val.2, hinput a.val.1 a.property.1 a.val.2 a.property.2⟩
  have heq : (fun (a : rowRectangle Good Rows)
      (t : selectorFibre row K V query bit) => B a.val.2 (decode t.val a.val.1)) =
      fun a t => F (childRow t).val.val (childCol a).val := by
    funext a t
    exact (hentry t.val a.val.2 a.val.1).symm
  change D (fun (a : rowRectangle Good Rows)
      (t : selectorFibre row K V query bit) => B a.val.2 (decode t.val a.val.1)) ≤ _
  rw [heq]
  have hm := Workspace.ProofLemmas.SublemmaPrecompNoIncrease
    (fun (c : U) (a : {a : V // query a = bit}) => F a.val.val c.val)
    childCol childRow
  have hu : D (fun (a : {a : V // query a = bit}) (c : U) =>
      F a.val.val c.val) ≤ child.cost := Nat.sInf_le ⟨child, rfl, hchild⟩
  exact hm.trans ((transpose_D
    (fun (a : {a : V // query a = bit}) (c : U) =>
      F a.val.val c.val)).le.trans hu)

end CurrentAdditive.V38LocalDiagram

#print axioms CurrentAdditive.V38LocalDiagram.dense_selector_child
#print axioms CurrentAdditive.V38LocalDiagram.coordinate_restriction_le
#print axioms CurrentAdditive.V38LocalDiagram.before_alice_cost
#print axioms CurrentAdditive.V38LocalDiagram.after_alice_interlace_le
