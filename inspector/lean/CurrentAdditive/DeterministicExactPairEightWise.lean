import CurrentAdditive.DeterministicPairProductLaw

/-! Appendix H exact-source bridge at the manuscript's actual eight-wise
independence order: four selected disjoint pairs read at most eight
original coordinates. -/

namespace CurrentAdditive.SuffixLong

open Paper2

variable {Z S : Type*} [Fintype Z] [Fintype S]

/-- The Boolean tests of any four selected disjoint pairs have exactly
their ambient heterogeneous Bernoulli product law under an eight-wise
indexed source. This is the `hjoint` input to the exact pair-tail bound. -/
theorem pairHit_source_four_wise_of_eight
    (source : FiniteLaw S) (ν : FiniteLaw Z)
    {m q : ℕ} (decode : S → Fin q → Z)
    (hwise : IsDWise 8 source decode ν)
    (e : Fin (2*m) → Fin q) (he : Function.Injective e)
    (K : Set S) (s : Finset (Fin m)) (hs : s.card ≤ 4)
    (E : (s → Bool) → Prop) :
    source.prob (fun ω => E (fun j : s =>
      pairHit decode e K j.val (decode ω))) =
      (FiniteLaw.pi (fun j : s =>
        boolImageLaw (ν.iid q) (pairHit decode e K j.val))).prob E := by
  classical
  let U : Finset (Fin q) := s.biUnion (pairBlock e)
  have hsize (i : Fin m) : (pairBlock e i).card ≤ 2 := by
    calc
      (pairBlock e i).card ≤ (Finset.univ : Finset (Fin 2)).card :=
        Finset.card_image_le
      _ = 2 := by simp
  have hU : U.card ≤ 8 := by
    have hu := Finset.card_biUnion_le_card_mul s (pairBlock e) 2
      (fun i _ => hsize i)
    calc
      U.card ≤ s.card * 2 := hu
      _ ≤ 4 * 2 := Nat.mul_le_mul_right 2 hs
      _ = 8 := by norm_num
  have hmem (j : s) (k : pairBlock e j.val) : k.val ∈ U :=
    Finset.mem_biUnion.mpr ⟨j.val, j.property, k.property⟩
  let testU : (U → Z) → (s → Bool) := fun z j =>
    localPairHit decode e K j.val (fun k => z ⟨k.val, hmem j k⟩)
  have htest (c : Fin q → Z) (j : s) :
      testU (fun k : U => c k.val) j =
        pairHit decode e K j.val c := by
    rfl
  have hsource := hwise U hU (fun z => E (testU z))
  have hfull := FiniteLaw.pi_prob_restrict (fun _ : Fin q => ν)
    (fun j : U => j.val) Subtype.val_injective
    (fun z => E (testU z))
  have hsourceAmbient :
      source.prob (fun ω => E (fun j : s =>
        pairHit decode e K j.val (decode ω))) =
      (ν.iid q).prob (fun c => E (fun j : s =>
        pairHit decode e K j.val c)) := by
    calc
      _ = (FiniteLaw.pi (fun _ : U => ν)).prob (fun z => E (testU z)) := by
        simpa only [htest] using hsource
      _ = _ := by
        simpa only [FiniteLaw.iid, htest] using hfull.symm
  let μ : Fin m → FiniteLaw Bool := fun i =>
    boolImageLaw (ν.iid q) (pairHit decode e K i)
  have hvector := pairHit_vector_product_law ν decode e he K
    (fun v : Fin m → Bool => E (fun j : s => v j.val))
  have hrestrict := FiniteLaw.pi_prob_restrict μ
    (fun j : s => j.val) Subtype.val_injective E
  calc
    _ = (ν.iid q).prob (fun c => E (fun j : s =>
          pairHit decode e K j.val c)) := hsourceAmbient
    _ = (FiniteLaw.pi μ).prob
          (fun v => E (fun j : s => v j.val)) := hvector
    _ = (FiniteLaw.pi (fun j : s => μ j.val)).prob E := hrestrict

#print axioms pairHit_source_four_wise_of_eight

end CurrentAdditive.SuffixLong
