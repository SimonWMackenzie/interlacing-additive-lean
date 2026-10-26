import CurrentAdditive.PivotGramBridge
import CurrentAdditive.ClearDenominatorsTotal

namespace CurrentAdditive.RationalBitBounds

open CurrentAdditive.SequentialTotality

theorem typedCandidate_pivotSum {m k : Nat}
    (B : Fin m → Fin k → ℚ) (ps : List (Fin m × Fin k))
    (f j : Fin k) :
    typedCandidate B ps f j =
      (if j = f then 1 else 0) -
        ∑ p : PivotIndex ps,
          if j = p.val.2 then B p.val.1 f else 0 := by
  simp only [typedCandidate]
  congr 1
  exact Finset.sum_subtype ps.toFinset (fun p => Iff.rfl)
    (fun p => if j = p.2 then B p.1 f else 0)

theorem typedCandidate_at_free {m k : Nat}
    (B : Fin m → Fin k → ℚ) (ps : List (Fin m × Fin k))
    (f : Fin k) (hfree : f ∉ ps.map Prod.snd) :
    typedCandidate B ps f f = 1 := by
  rw [typedCandidate_pivotSum]
  have hne : ∀ p : PivotIndex ps, f ≠ p.val.2 := by
    intro p h
    apply hfree
    exact List.mem_map.mpr ⟨p.val,
      List.mem_toFinset.mp p.property, h.symm⟩
  simp [hne]

theorem typedCandidate_at_pivot {m k : Nat}
    (B : Fin m → Fin k → ℚ) (ps : List (Fin m × Fin k))
    (f : Fin k) (hfree : f ∉ ps.map Prod.snd)
    (hcol : Function.Injective (fun p : PivotIndex ps => p.val.2))
    (p0 : PivotIndex ps) :
    typedCandidate B ps f p0.val.2 = -B p0.val.1 f := by
  rw [typedCandidate_pivotSum]
  have hf : p0.val.2 ≠ f := by
    intro h
    apply hfree
    exact List.mem_map.mpr ⟨p0.val,
      List.mem_toFinset.mp p0.property, h⟩
  have hsum :
      (∑ p ∈ ps.toFinset.attach,
        if p0.val.2 = p.val.2 then B p.val.1 f else 0) =
      B p0.val.1 f := by
    rw [Finset.attach_eq_univ]
    simp [hcol.eq_iff]
  simp [hf, hsum]

theorem typedCandidate_off_pivots {m k : Nat}
    (B : Fin m → Fin k → ℚ) (ps : List (Fin m × Fin k))
    (f j : Fin k) (hjf : j ≠ f)
    (hjp : j ∉ ps.map Prod.snd) :
    typedCandidate B ps f j = 0 := by
  rw [typedCandidate_pivotSum]
  have hne : ∀ p : PivotIndex ps, j ≠ p.val.2 := by
    intro p h
    apply hjp
    exact List.mem_map.mpr ⟨p.val,
      List.mem_toFinset.mp p.property, h.symm⟩
  simp [hjf, hne]

end CurrentAdditive.RationalBitBounds
