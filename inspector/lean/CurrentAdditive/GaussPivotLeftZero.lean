import CurrentAdditive.SequentialTotality

/-! Every final pivot row is zero in columns before its pivot. This follows
from the below-active-row invariant at the pivot step and the preservation of
already scanned columns by all later steps. -/

namespace CurrentAdditive.GaussPivotLeftZero

open CurrentAdditive.SequentialTotality

theorem echelonTyped_pivot_left_zero {m k : Nat}
    (A : Fin m → Fin k → ℚ) (r c fuel : Nat)
    (hbound : c + fuel ≤ k) (hbelow : BelowZero A r c) :
    let out := echelonTyped A r c fuel
    ∀ p ∈ out.2, ∀ j : Fin k, j.val < p.2.val → out.1 p.1 j = 0 := by
  induction fuel generalizing A r c with
  | zero => simp [echelonTyped]
  | succ fuel ih =>
      have hc : c < k := by omega
      by_cases hr : r < m
      · cases hp : pivotTyped A r ⟨c, hc⟩ with
        | none =>
            have hb := belowZero_advance_no_pivot A r c hc hbelow hp
            have hrec := ih A r (c + 1) (by omega) hb
            simpa [echelonTyped, hr, hc, hp] using hrec
        | some s =>
            have hs := (pivotTyped_spec A r ⟨c, hc⟩ s hp).1
            let B := swapTyped A ⟨r, hr⟩ s
            let C := clearTyped B ⟨r, hr⟩ ⟨c, hc⟩
            have hbs : BelowZero B r c := belowZero_swap A r c hr s hs hbelow
            have hpnz : B ⟨r, hr⟩ ⟨c, hc⟩ ≠ 0 := by
              simpa [B, swapTyped] using
                (pivotTyped_spec A r ⟨c, hc⟩ s hp).2
            have hbc : BelowZero C (r + 1) (c + 1) :=
              belowZero_clear B r c hr hc hbs hpnz
            have hrec := ih C (r + 1) (c + 1) (by omega) hbc
            have hleft := (echelonTyped_staircase C (r + 1) (c + 1) fuel
              (by omega) hbc).2
            dsimp only
            intro p hmem j hj
            have hmem' : p = (⟨r, hr⟩, ⟨c, hc⟩) ∨
                p ∈ (echelonTyped C (r + 1) (c + 1) fuel).2 := by
              simpa [echelonTyped, hr, hc, hp, B, C] using hmem
            rcases hmem' with hfirst | hlater
            · subst p
              have hjc : j.val < c := by simpa using hj
              have hfinal := hleft ⟨r, hr⟩ j (by omega)
              have hstep := pivotStep_left A r c hr hc s hs hbelow
                ⟨r, hr⟩ j hjc
              have hinitial : A ⟨r, hr⟩ j = 0 :=
                hbelow ⟨r, hr⟩ j (by simp) hjc
              simpa [echelonTyped, hr, hc, hp, B, C] using
                hfinal.trans (hstep.trans hinitial)
            · simpa [echelonTyped, hr, hc, hp, B, C] using
                hrec p hlater j hj
      · simp [echelonTyped, hr]

theorem full_pivot_left_zero {m k : Nat}
    (A : Fin m → Fin k → ℚ) :
    let out := echelonTyped A 0 0 k
    ∀ p ∈ out.2, ∀ j : Fin k, j.val < p.2.val → out.1 p.1 j = 0 := by
  apply echelonTyped_pivot_left_zero A 0 0 k (by simp)
  intro i j _ hj
  omega

#print axioms full_pivot_left_zero

end CurrentAdditive.GaussPivotLeftZero
