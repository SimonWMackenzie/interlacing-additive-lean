import CurrentAdditive.GaussFirstFreeArithmetic

/-! The true prefix of row=column flags contains the diagonal pivot pairs. -/

namespace CurrentAdditive.GaussPivotPrefixRows

open CurrentAdditive.GaussPivotPrefixPhysical

theorem diagonal_pairs_in_prefix (n : Nat) (ps : List (Nat × Nat))
    (hrows : ps.map Prod.fst = List.range' n ps.length) :
    ∀ j, n ≤ j → j < n + prefixCount ps → (j,j) ∈ ps := by
  induction ps generalizing n with
  | nil => simp [prefixCount, pivotFlags]
  | cons p ps ih =>
      rcases p with ⟨r,c⟩
      have hr : r = n := by
        have h := congrArg List.head? hrows
        simpa [List.range'_succ] using h
      have htail : ps.map Prod.fst = List.range' (n+1) ps.length := by
        have h := congrArg List.tail hrows
        simpa [List.range'_succ] using h
      subst r
      by_cases hc : c = n
      · subst c
        have hprefix : prefixCount ((n,n) :: ps) =
            1 + prefixCount ps := by
          simp [prefixCount, pivotFlags]
          omega
        intro j hnj hj
        rw [hprefix] at hj
        by_cases heq : j = n
        · subst j; simp
        · have hmem := ih (n+1) htail j (by omega) (by omega)
          simp [hmem]
      · have hprefix : prefixCount ((n,c) :: ps) = 0 := by
          have hnc : n ≠ c := Ne.symm hc
          simp [prefixCount, pivotFlags, hnc]
        intro j hnj hj
        rw [hprefix] at hj
        omega

#print axioms diagonal_pairs_in_prefix

end CurrentAdditive.GaussPivotPrefixRows
