import CurrentAdditive.GaussControlTrace

/-! Ordered pivot-list invariants for the materialized Gauss control trace. -/

namespace CurrentAdditive.GaussTraceInvariants

open CurrentAdditive.GaussControlTrace
open CurrentAdditive.SequentialTotality

theorem step_rows {m k : Nat} (s : State m k)
    (h : s.pivots.map (fun p => p.1.val) = List.range s.r) :
    (step s).pivots.map (fun p => p.1.val) = List.range (step s).r := by
  by_cases hr : s.r < m
  · by_cases hc : s.c < k
    · cases hp : pivotTyped s.B s.r ⟨s.c, hc⟩ with
      | none => simpa [step, hr, hc, hp] using h
      | some i =>
          simp [step, hr, hc, hp, List.map_append, List.range_succ, h]
    · simpa [step, hr, hc] using h
  · simpa [step, hr] using h

theorem after_rows {m k : Nat} (A : Fin m → Fin k → ℚ) (t : Nat) :
    (after A t).pivots.map (fun p => p.1.val) = List.range (after A t).r := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [after, Function.iterate_succ_apply'] at ih ⊢
      exact step_rows _ ih

theorem step_columns_below {m k : Nat} (s : State m k)
    (h : ∀ p ∈ s.pivots, p.2.val < s.c) :
    ∀ p ∈ (step s).pivots, p.2.val < (step s).c := by
  by_cases hr : s.r < m
  · by_cases hc : s.c < k
    · cases hp : pivotTyped s.B s.r ⟨s.c, hc⟩ with
      | none =>
          simpa [step, hr, hc, hp] using
            (fun p hp' => Nat.lt_succ_of_lt (h p hp'))
      | some i =>
          intro p hp'
          have hmem : p ∈ s.pivots ++ [(⟨s.r, hr⟩, ⟨s.c, hc⟩)] := by
            simpa [step, hr, hc, hp] using hp'
          have hout : p.2.val < s.c + 1 := by
            rcases List.mem_append.mp hmem with hp' | hp'
            · exact Nat.lt_succ_of_lt (h p hp')
            · simp only [List.mem_singleton] at hp'
              subst p
              simp
          simpa [step, hr, hc, hp] using hout
    · simpa [step, hr, hc] using h
  · simpa [step, hr] using h

theorem after_columns_below {m k : Nat} (A : Fin m → Fin k → ℚ) (t : Nat) :
    ∀ p ∈ (after A t).pivots, p.2.val < (after A t).c := by
  induction t with
  | zero => simp [after, initial]
  | succ t ih =>
      simp only [after, Function.iterate_succ_apply'] at ih ⊢
      exact step_columns_below _ ih

theorem step_columns_pairwise {m k : Nat} (s : State m k)
    (hbelow : ∀ p ∈ s.pivots, p.2.val < s.c)
    (hpw : (s.pivots.map (fun p => p.2.val)).Pairwise (· < ·)) :
    ((step s).pivots.map (fun p => p.2.val)).Pairwise (· < ·) := by
  by_cases hr : s.r < m
  · by_cases hc : s.c < k
    · cases hp : pivotTyped s.B s.r ⟨s.c, hc⟩ with
      | none => simpa [step, hr, hc, hp] using hpw
      | some i =>
          simpa [step, hr, hc, hp, List.map_append,
            List.pairwise_append] using
            (show (s.pivots.map (fun p => p.2.val) ++ [s.c]).Pairwise (· < ·) from by
              apply List.pairwise_append.mpr
              constructor
              · exact hpw
              constructor
              · simp
              · intro a ha b hb
                simp only [List.mem_singleton] at hb
                subst b
                obtain ⟨p,hp,hval⟩ := List.mem_map.mp ha
                subst a
                exact hbelow p hp)
    · simpa [step, hr, hc] using hpw
  · simpa [step, hr] using hpw

theorem after_columns_pairwise {m k : Nat} (A : Fin m → Fin k → ℚ) (t : Nat) :
    ((after A t).pivots.map (fun p => p.2.val)).Pairwise (· < ·) := by
  induction t with
  | zero => simp [after, initial]
  | succ t ih =>
      simp only [after, Function.iterate_succ_apply'] at ih ⊢
      exact step_columns_pairwise _ (after_columns_below A t) ih

#print axioms after_rows
#print axioms after_columns_below
#print axioms after_columns_pairwise

end CurrentAdditive.GaussTraceInvariants
