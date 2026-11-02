import CurrentAdditive.GeneratedFrontierEndpoint

/-!
Exact joint law on any injectively selected tuple of coordinates of a
complete indexed source. This generalizes the frozen eight-coordinate
suffix adapter to the larger selected word needed by a collision witness.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2

theorem selected_dwise_pushes
    {S Z : Type*} [Fintype S] [Fintype Z] {D q n : ℕ}
    (source : FiniteLaw S) (ν : FiniteLaw Z)
    (decode : S → Fin q → Z)
    (hwise : IsDWise D source decode ν)
    (hn : n ≤ D) (e : Fin n → Fin q) (he : Function.Injective e) :
    source.PushesTo (ν.iid n) (fun s j => decode s (e j)) := by
  classical
  intro P
  let J : Finset (Fin q) := Finset.univ.image e
  have hJcard : J.card ≤ D := by
    exact (Finset.card_image_le).trans (by simpa [J] using hn)
  have hmem (j : Fin n) : e j ∈ J :=
    Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  let E : (J → Z) → Prop := fun z => P (fun j => z ⟨e j, hmem j⟩)
  have hsource := hwise J hJcard E
  have hrestrict := FiniteLaw.pi_prob_restrict
    (fun _ : Fin q => ν) (fun j : J => j.val)
    Subtype.val_injective E
  have hsource' : source.prob (fun s => P (fun j => decode s (e j))) =
      (ν.iid q).prob (fun c => P (fun j => c (e j))) := by
    calc
      _ = source.prob (fun s => E (fun j : J => decode s j.val)) := rfl
      _ = (FiniteLaw.pi (fun _ : J => ν)).prob E := hsource
      _ = (ν.iid q).prob (fun c => P (fun j => c (e j))) := by
        simpa only [FiniteLaw.iid, E] using hrestrict.symm
  have hproduct := FiniteLaw.pi_prob_restrict
    (fun _ : Fin q => ν) e he P
  calc
    _ = (ν.iid q).prob (fun c => P (fun j => c (e j))) := hsource'
    _ = (ν.iid n).prob P := by simpa only [FiniteLaw.iid] using hproduct

end CurrentAdditive.DeterministicIndexedMatrix

#print axioms CurrentAdditive.DeterministicIndexedMatrix.selected_dwise_pushes
