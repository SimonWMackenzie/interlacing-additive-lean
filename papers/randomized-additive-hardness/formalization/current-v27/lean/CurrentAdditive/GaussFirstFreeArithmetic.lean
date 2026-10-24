import CurrentAdditive.GaussPivotPrefixPhysical

/-! Arithmetic justification for reading the first missing pivot column from
the initial run of diagonal (row,column) pivot pairs. -/

namespace CurrentAdditive.GaussFirstFreeArithmetic

open CurrentAdditive.GaussPivotPrefixPhysical

def diagonalFlags : Nat → List Nat → List Bool
  | _, [] => []
  | n, c :: cs => decide (n = c) :: diagonalFlags (n + 1) cs

def diagonalPrefix (n : Nat) (cs : List Nat) : Nat :=
  ((diagonalFlags n cs).takeWhile id).length

theorem diagonalPrefix_le (n : Nat) (cs : List Nat) :
    diagonalPrefix n cs ≤ cs.length := by
  have hlen : (diagonalFlags n cs).length = cs.length := by
    induction cs generalizing n with
    | nil => rfl
    | cons c cs ih => simp [diagonalFlags, ih]
  unfold diagonalPrefix
  exact (List.takeWhile_sublist id).length_le.trans_eq hlen

theorem diagonal_facts (n : Nat) (cs : List Nat)
    (hinc : cs.Pairwise (· < ·))
    (hlower : ∀ c ∈ cs, n ≤ c) :
    (∀ x, n ≤ x → x < n + diagonalPrefix n cs → x ∈ cs) ∧
      n + diagonalPrefix n cs ∉ cs := by
  induction cs generalizing n with
  | nil => simp [diagonalPrefix, diagonalFlags]
  | cons c cs ih =>
      have htail : cs.Pairwise (· < ·) := (List.pairwise_cons.mp hinc).2
      have hhead : ∀ d ∈ cs, c < d := (List.pairwise_cons.mp hinc).1
      have hc : n ≤ c := hlower c (by simp)
      by_cases heq : c = n
      · subst c
        have hlow : ∀ d ∈ cs, n + 1 ≤ d := by
          intro d hd
          have := hhead d hd
          omega
        obtain ⟨hmem, hnot⟩ := ih (n + 1) htail hlow
        have hp : diagonalPrefix n (n :: cs) =
            1 + diagonalPrefix (n + 1) cs := by
          simp [diagonalPrefix, diagonalFlags]
          omega
        constructor
        · intro x hx hxf
          rw [hp] at hxf
          by_cases hxn : x = n
          · subst x; simp
          · have : x ∈ cs := hmem x (by omega) (by omega)
            simp [this]
        · rw [hp]
          intro hm
          have hne : n + (1 + diagonalPrefix (n + 1) cs) ≠ n := by omega
          have htailmem : n + (1 + diagonalPrefix (n + 1) cs) ∈ cs := by
            simpa [hne] using hm
          exact hnot (by simpa [Nat.add_assoc] using htailmem)
      · have hp : diagonalPrefix n (c :: cs) = 0 := by
          simp [diagonalPrefix, diagonalFlags, heq, eq_comm]
        constructor
        · intro x hx hxf
          rw [hp] at hxf
          omega
        · rw [hp]
          intro hm
          have hn : n ≠ c := by omega
          have hcs : n ∈ cs := by simpa [hn] using hm
          have hd := hhead n hcs
          omega

theorem firstFree_eq_prefix (k : Nat) (cs : List Nat)
    (hinc : cs.Pairwise (· < ·))
    (hlen : cs.length < k) :
    (List.range k).find? (fun c => decide (c ∉ cs)) =
      some (diagonalPrefix 0 cs) := by
  have hfacts := diagonal_facts 0 cs hinc (by simp)
  have hf : diagonalPrefix 0 cs < k := by
    have := diagonalPrefix_le 0 cs
    omega
  apply List.find?_eq_some_iff_getElem.mpr
  refine ⟨?_, diagonalPrefix 0 cs, (by simpa using hf), ?_, ?_⟩
  · simpa using hfacts.2
  · simp
  · intro j hj
    have hm : j ∈ cs := hfacts.1 j (by omega) (by omega)
    simp [hm]

theorem flags_eq_diagonalFrom (n : Nat) (ps : List (Nat × Nat))
    (hrows : ps.map Prod.fst = List.range' n ps.length) :
    GaussPivotPrefixPhysical.pivotFlags ps =
      diagonalFlags n (ps.map Prod.snd) := by
  induction ps generalizing n with
  | nil => rfl
  | cons p ps ih =>
      rcases p with ⟨r,c⟩
      have hfirst : r = n := by
        have h := congrArg List.head? hrows
        simpa [List.range'_succ] using h
      have htail : ps.map Prod.fst = List.range' (n+1) ps.length := by
        have h := congrArg List.tail hrows
        simpa [List.range'_succ] using h
      subst r
      simp only [GaussPivotPrefixPhysical.pivotFlags,
        diagonalFlags, List.map_cons]
      exact congrArg (List.cons _) (ih (n+1) htail)

end CurrentAdditive.GaussFirstFreeArithmetic
