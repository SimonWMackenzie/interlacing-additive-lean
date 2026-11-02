import Paper2.TwoStreamMatrix
import Paper2.ProjectedSupportMass

/-!
# A surviving bin lower-bounds the actual transposed protocol

Frozen v12, Section 5, `res:two-stream`, live-stop exclusion. The protocol
still takes original input labels. Its value on retained ordinary columns
and raw row supports exposes the scalar restriction profile of `T`.
No protocol or row representatives are selected as a function of the other
party's input.
-/

namespace Paper2.TwoStreamScalarCost

open Workspace.Types.Protocol

variable {S J W Ω A C : Type*} [Fintype S] [Fintype J]
  [Fintype W] [Fintype Ω]

/-- A coordinate of the joint ordinary map has its prescribed law. -/
theorem coordinate_pushes (ν : FiniteLaw J) (κ : FiniteLaw Ω) (s : ℕ)
    (Φ : Ω → Fin s → J) (hΦ : κ.PushesTo (ν.iid s) Φ) (i : Fin s) :
    κ.PushesTo ν (fun c => Φ c i) := by
  intro E
  exact (hΦ (fun z => E (z i))).trans (FiniteLaw.iid_prob_coordinate ν s i E)

/-- The profile is applied to the actual selector and coordinate images.
The resulting lower bound concerns the given protocol, not an abstract
matrix with merely comparable input densities. -/
theorem one_bin_cost (μ : FiniteLaw S) (ν : FiniteLaw J) (κ : FiniteLaw Ω)
    (T : S → J → Bool) (H : ℕ) (x : ℝ)
    (hprofile : RestrictionProfile T μ ν x (H : ℤ))
    (σ : W → S) (φ : Ω → J) (hφ : κ.PushesTo ν φ)
    (F : Finset W) (O : Set Ω)
    (hF : x ≤ ProjectedSupportStep.mass μ σ F)
    (hO : (3 / 5 : ℝ) ≤ κ.prob (· ∈ O))
    (input : W → C) (col : Ω → A) (P : Protocol A C Bool)
    (hP : ∀ w ∈ F, ∀ c ∈ O, P.eval (col c) (input w) = T (σ w) (φ c)) :
    H ≤ P.cost := by
  classical
  let Q := Workspace.UpperBound.Protocol.comap
    (fun w : (F : Set W) => input w.val) (fun c : O => col c.val)
    (Workspace.UpperBound.Protocol.transpose P)
  have hQ : Q.Computes (fun (w : (F : Set W)) (c : O) => T (σ w.val) (φ c.val)) := by
    intro w c
    rw [Workspace.UpperBound.Protocol.comap_eval,
      Workspace.UpperBound.Protocol.transpose_eval]
    exact hP w.val w.property c.val c.property
  have hupper : Compression.restrictionD (fun w c => T (σ w) (φ c))
      (F : Set W) O ≤ P.cost := by
    have hle : Compression.restrictionD (fun w c => T (σ w) (φ c))
        (F : Set W) O ≤ Q.cost := Nat.sInf_le ⟨Q, rfl, hQ⟩
    simpa only [Q, Workspace.UpperBound.Protocol.comap_cost,
      Workspace.UpperBound.Protocol.transpose_cost] using hle
  rw [restrictionD_pullback_image T σ φ (F : Set W) O] at hupper
  have hcol : (3 / 5 : ℝ) ≤ ν.prob (· ∈ φ '' O) :=
    hO.trans (FiniteLaw.prob_le_image κ ν φ hφ O)
  have hrow : x ≤ μ.prob (· ∈ σ '' (F : Set W)) := hF
  have hl := hprofile ⟨0, by omega⟩ (σ '' (F : Set W)) (φ '' O) hrow
    (by simpa using hcol)
  simp only [Fin.val_zero, Nat.cast_zero, sub_zero] at hl
  have hnat : H ≤ Compression.restrictionD T (σ '' (F : Set W)) (φ '' O) := by
    exact_mod_cast hl
  exact hnat.trans hupper

end Paper2.TwoStreamScalarCost

#print axioms Paper2.TwoStreamScalarCost.one_bin_cost
