import CurrentAdditive.LabelTrace

/-! The actual independent-column constructor, preceded by its literal zero
deletion pass, returns a normalized positive law for every nonnegative
normalized rational input law. Pattern requests may name deleted values. -/

namespace CurrentAdditive.LabelTrace

open SequentialCode SequentialSourceCode IndependentSupport
  SequentialFeatureCoverage SequentialAppendMoments

instance patternMatchesDecidable {Y : Type*} [DecidableEq Y] {q : Nat}
    (p : Fin q → Option Y) (v : Fin q → Y) : Decidable (PatternMatches p v) :=
  inferInstanceAs (Decidable (∀ i, p i = none ∨ p i = some (v i)))

/-- All coordinates of every retained word are actual decoded alphabet
values. This remains true for an empty alphabet and repeated values. -/
theorem sequentialIndependent_coordinate_mem {Y : Type*} [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ)) :
    ∀ q out, sequentialIndependent D alphabet q = some out →
      ∀ entry ∈ out, ∀ i : Fin q,
        entry.1 i ∈ (alphabet.map Prod.fst).toList := by
  intro q
  induction q with
  | zero =>
      intro out h entry he i
      exact Fin.elim0 i
  | succ q ih =>
      intro out h entry he i
      cases hprev : sequentialIndependent D alphabet q with
      | none => simp [sequentialIndependent, hprev] at h
      | some prev =>
          obtain ⟨old, hold, hword⟩ :=
            sequentialIndependent_stage_labels D alphabet q prev out hprev h entry he
          have hold' : old ∈ (appendSource prev alphabet).toList :=
            Array.mem_toList_iff.mpr hold
          rw [appendSource_toList] at hold'
          obtain ⟨x, hx, hy⟩ := List.mem_flatMap.mp hold'
          obtain ⟨y, hy, heq⟩ := List.mem_map.mp hy
          have hword' : entry.1 = appendWord x.1 y.1 := by
            rw [← hword, ← heq]
          rw [hword']
          by_cases hi : i.val < q
          · simpa [appendWord, hi] using
              ih prev hprev x (Array.mem_toList_iff.mp hx) ⟨i.val, hi⟩
          · simp only [appendWord, dif_neg hi]
            rw [Array.toList_map]
            exact List.mem_map.mpr ⟨y, hy, rfl⟩

theorem alphabetPointMass_eq_zero_of_not_mem {Y : Type*} [DecidableEq Y]
    (alphabet : Array (Y × ℚ)) (y : Y)
    (hy : y ∉ (alphabet.map Prod.fst).toList) :
    alphabetPointMass alphabet y = 0 := by
  unfold alphabetPointMass weightedSum
  apply List.sum_eq_zero
  intro a ha
  obtain ⟨entry, he, rfl⟩ := List.mem_map.mp ha
  have hne : entry.1 ≠ y := by
    intro heq
    apply hy
    rw [Array.toList_map]
    exact List.mem_map.mpr ⟨entry, he, heq⟩
  simp [hne]

/-- The missing-value case is proved on the actual output words, rather
than inferred from a rewritten target probability. -/
theorem sequentialIndependent_pattern_moment_arbitrary {Y : Type*}
    [DecidableEq Y] (D : Nat) (alphabet : Array (Y × ℚ))
    (halphabet : sourceMass alphabet = 1)
    (q : Nat) (out : Array ((Fin q → Y) × ℚ))
    (hout : sequentialIndependent D alphabet q = some out)
    (p : Fin q → Option Y) (hsize : patternSize p ≤ D) :
    weightedSum out (fun v => if PatternMatches p v then 1 else 0) =
      patternTarget alphabet p := by
  classical
  by_cases hvalues : ∀ i y, p i = some y →
      y ∈ (alphabet.map Prod.fst).toList
  · exact sequentialIndependent_pattern_moment D alphabet halphabet q out hout
      p hvalues hsize
  · push_neg at hvalues
    obtain ⟨i, y, hiy, hy⟩ := hvalues
    have htarget : patternTarget alphabet p = 0 := by
      unfold patternTarget
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [hiy]
      exact alphabetPointMass_eq_zero_of_not_mem alphabet y hy
    rw [htarget]
    unfold weightedSum
    apply List.sum_eq_zero
    intro a ha
    obtain ⟨entry, he, rfl⟩ := List.mem_map.mp ha
    have hnot : ¬ PatternMatches p entry.1 := by
      intro hm
      have hi := hm i
      rw [hiy] at hi
      have heqy : y = entry.1 i := by simpa using hi
      apply hy
      rw [heqy]
      exact sequentialIndependent_coordinate_mem D alphabet q out hout
        entry (Array.mem_toList_iff.mp he) i
    simp [hnot]

theorem sequentialPreprocessed_pattern_moment {Y : Type*}
    [DecidableEq Y] (D : Nat) (alphabet : Array (Y × ℚ))
    (hnonneg : alphabet.all (fun e => decide (0 ≤ e.2)) = true)
    (hmass : sourceMass alphabet = 1)
    (q : Nat) (out : Array ((Fin q → Y) × ℚ))
    (hout : sequentialPreprocessed D alphabet q = some out)
    (p : Fin q → Option Y) (hsize : patternSize p ≤ D) :
    weightedSum out (fun v => if PatternMatches p v then 1 else 0) =
      patternTarget alphabet p := by
  classical
  have hm : sourceMass (positiveLaw alphabet) = 1 := by
    rw [← (positiveLaw_mass_moments alphabet hnonneg
      (n := 0) (fun _ j => Fin.elim0 j)).1]
    exact hmass
  rw [positiveLaw_patternTarget alphabet hnonneg p]
  exact sequentialIndependent_pattern_moment_arbitrary D
    (positiveLaw alphabet) hm q out hout p hsize

theorem positiveLaw_size_le {Y : Type*} (alphabet : Array (Y × ℚ))
    (hmass : sourceMass alphabet = 1) :
    (positiveLaw alphabet).size ≤ alphabet.size := by
  obtain ⟨trace, _, _⟩ := positiveLaw_trace alphabet hmass
  simpa using Fintype.card_le_of_injective trace trace.injective

theorem sequentialPreprocessed_size_polynomial {Y : Type*}
    [DecidableEq Y] (D : Nat) (alphabet : Array (Y × ℚ))
    (hmass : sourceMass alphabet = 1)
    (q : Nat) (out : Array ((Fin q → Y) × ℚ))
    (hout : sequentialPreprocessed D alphabet q = some out) :
    out.size ≤ (1 + q * alphabet.size) ^ D := by
  cases q with
  | zero =>
      simp [sequentialPreprocessed, sequentialIndependent] at hout
      subst out
      simp
  | succ q =>
      exact (sequentialIndependent_size_polynomial D
        (positiveLaw alphabet) q out hout).trans
        (Nat.pow_le_pow_left (by
          have hs := positiveLaw_size_le alphabet hmass
          exact Nat.add_le_add_left (Nat.mul_le_mul_left (q + 1) hs) 1) D)

/-- One output of the executable constructor carries all the advertised
law properties at once, including all requests involving zero-mass values. -/
theorem sequentialPreprocessed_normalized {Y : Type*} [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ))
    (hnonneg : alphabet.all (fun e => decide (0 ≤ e.2)) = true)
    (hmass : sourceMass alphabet = 1) (q : Nat) :
    ∃ out, sequentialPreprocessed D alphabet q = some out ∧
      SourcePositive out ∧ sourceMass out = 1 ∧ 0 < out.size ∧
      out.size ≤ (1 + q * alphabet.size) ^ D ∧
      ∀ p : Fin q → Option Y, patternSize p ≤ D →
        weightedSum out (fun v => if PatternMatches p v then 1 else 0) =
          patternTarget alphabet p := by
  classical
  obtain ⟨out, hout, hpos⟩ := sequentialPreprocessed_total D alphabet q
  have hm := sequentialPreprocessed_mass D alphabet hnonneg hmass q out hout
  refine ⟨out, hout, hpos, hm, ?_,
    sequentialPreprocessed_size_polynomial D alphabet hmass q out hout, ?_⟩
  · by_contra hn
    have hz : out.size = 0 := by omega
    have he : out = #[] := Array.size_eq_zero_iff.mp hz
    simp [he, sourceMass] at hm
  · intro p hp
    exact sequentialPreprocessed_pattern_moment D alphabet hnonneg hmass
      q out hout p hp

#print axioms sequentialIndependent_coordinate_mem
#print axioms sequentialIndependent_pattern_moment_arbitrary
#print axioms sequentialPreprocessed_pattern_moment
#print axioms sequentialPreprocessed_normalized

end CurrentAdditive.LabelTrace
