import CurrentAdditive.CandidateBitsLocal

/-!
The first missing pivot column admits a simpler back-substitution formula:
the earlier columns have their own row as pivot row, while coefficients after
the free column vanish.  This is a semantic target for the physical vector
writer.  The Gauss-specific prefix and zero facts are supplied separately.
-/

namespace CurrentAdditive.GaussFirstFreeCandidate

open CurrentAdditive.SequentialTotality
open CurrentAdditive.RationalBitBounds

def directCandidate {m k : Nat} (B : Fin m → Fin k → ℚ)
    (f : Fin k) (hf : f.val ≤ m) (j : Fin k) : ℚ :=
  if h : j.val < f.val then
    -B ⟨j.val, by omega⟩ f
  else if j = f then 1 else 0

theorem directCandidate_eq {m k : Nat}
    (B : Fin m → Fin k → ℚ) (ps : List (Fin m × Fin k))
    (f : Fin k) (hf : f.val ≤ m)
    (hfree : f ∉ ps.map Prod.snd)
    (hcol : Function.Injective (fun p : PivotIndex ps => p.val.2))
    (hleft : ∀ j : Fin k, j.val < f.val →
      ∃ i : Fin m, i.val = j.val ∧ (i, j) ∈ ps)
    (hzero : ∀ p ∈ ps, f.val < p.2.val → B p.1 f = 0)
    (j : Fin k) :
    directCandidate B f hf j = typedCandidate B ps f j := by
  by_cases hj : j.val < f.val
  · obtain ⟨i, hi, hip⟩ := hleft j hj
    let p : PivotIndex ps := ⟨(i,j), List.mem_toFinset.mpr hip⟩
    have hif : i = (⟨j.val, by omega⟩ : Fin m) := by
      apply Fin.ext
      exact hi
    simpa [directCandidate, hj, p, hif] using
      (typedCandidate_at_pivot B ps f hfree hcol p).symm
  · by_cases hEq : j = f
    · subst j
      simpa [directCandidate, hj] using
        (typedCandidate_at_free B ps f hfree).symm
    · have hfj : f.val < j.val := by omega
      by_cases hp : j ∈ ps.map Prod.snd
      · obtain ⟨p0, hp0, hpj⟩ := List.mem_map.mp hp
        let p : PivotIndex ps := ⟨p0, List.mem_toFinset.mpr hp0⟩
        have hz : B p0.1 f = 0 := hzero p0 hp0 (by simpa [hpj] using hfj)
        simpa [directCandidate, hj, hEq, p, hpj, hz] using
          (typedCandidate_at_pivot B ps f hfree hcol p).symm
      · simpa [directCandidate, hj, hEq] using
          (typedCandidate_off_pivots B ps f j hEq hp).symm

#print axioms directCandidate_eq

end CurrentAdditive.GaussFirstFreeCandidate
