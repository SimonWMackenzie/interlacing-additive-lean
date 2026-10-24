import CurrentAdditive.ExactSuffixLongEight

/-! A bounded-wise source has the exact joint law on any injectively
selected ordered tuple of at most eight original coordinates. -/

namespace CurrentAdditive.ArbitraryPrefix

open Paper2

theorem exact_selected_of_eight
    {S Z : Type*} [Fintype S] [Fintype Z] {q n : ℕ}
    (source : FiniteLaw S) (ν : FiniteLaw Z)
    (decode : S → Fin q → Z)
    (hwise : IsDWise 8 source decode ν)
    (hn : n ≤ 8) (e : Fin n → Fin q) (he : Function.Injective e)
    (P : (Fin n → Z) → Prop) :
    source.prob (fun s => P (fun j => decode s (e j))) =
      (ν.iid n).prob P := by
  classical
  let J : Finset (Fin q) := Finset.univ.image e
  have hJcard : J.card ≤ 8 := by
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

#print axioms CurrentAdditive.ArbitraryPrefix.exact_selected_of_eight

end CurrentAdditive.ArbitraryPrefix
