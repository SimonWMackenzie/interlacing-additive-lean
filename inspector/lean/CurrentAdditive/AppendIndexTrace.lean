import CurrentAdditive.LabelTrace

namespace CurrentAdditive.LabelTrace

open SequentialCode SequentialSourceCode IndependentSupport

private theorem alphabet_size_pos_of_mass_one {Y : Type*}
    (alphabet : Array (Y × ℚ)) (hmass : sourceMass alphabet = 1) :
    0 < alphabet.size := by
  by_contra hn
  have hz : alphabet.size = 0 := by omega
  have he : alphabet = #[] := Array.size_eq_zero_iff.mp hz
  simp [he, sourceMass] at hmass

/-- Zero deletion retains exactly the original pairs, including their
weights, and its image is exactly the original positive-weight positions. -/
theorem positiveLaw_trace_exact {Y : Type*}
    (alphabet : Array (Y × ℚ)) (hmass : sourceMass alphabet = 1) :
    ∃ trace : Fin (positiveLaw alphabet).size ↪ Fin alphabet.size,
      (∀ j, (positiveLaw alphabet)[j] = alphabet[trace j]) ∧
      (∀ i : Fin alphabet.size,
        (∃ j, trace j = i) ↔ 0 < alphabet[i].2) := by
  have ha := alphabet_size_pos_of_mass_one alphabet hmass
  letI : Inhabited Y := ⟨alphabet[0].1⟩
  obtain ⟨trace, he, hi⟩ :=
    selectedSource_trace alphabet (alphabet.map Prod.snd) (by simp)
  refine ⟨trace, ?_, ?_⟩
  · intro j
    simpa [positiveLaw, SequentialZeroDeletion.retainedSource,
      (trace j).isLt] using he j
  · intro i
    simpa [positiveLaw, i.isLt] using hi i

/-- The literal append positions are exactly the product of the two original
position sets. No distinctness assumption on decoded values is used. -/
def appendIndexEquiv {Y : Type*} {q : Nat}
    (prev : Array ((Fin q → Y) × ℚ)) (alphabet : Array (Y × ℚ)) :
    Fin prev.size × Fin alphabet.size ≃ Fin (appendSource prev alphabet).size :=
  finProdFinEquiv.trans {
    toFun := Fin.cast (SequentialSourceResource.appendSource_size prev alphabet).symm
    invFun := Fin.cast (SequentialSourceResource.appendSource_size prev alphabet)
    left_inv := fun _ => Fin.ext rfl
    right_inv := fun _ => Fin.ext rfl }

theorem appendIndexEquiv_val {Y : Type*} {q : Nat}
    (prev : Array ((Fin q → Y) × ℚ)) (alphabet : Array (Y × ℚ))
    (r : Fin prev.size) (c : Fin alphabet.size) :
    (appendIndexEquiv prev alphabet (r, c)).val =
      r.val * alphabet.size + c.val := by
  simp [appendIndexEquiv, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

theorem appendIndexEquiv_entry {Y : Type*} {q : Nat}
    (prev : Array ((Fin q → Y) × ℚ)) (alphabet : Array (Y × ℚ))
    (r : Fin prev.size) (c : Fin alphabet.size) :
    (appendSource prev alphabet)[appendIndexEquiv prev alphabet (r, c)] =
      (appendWord prev[r].1 alphabet[c].1, prev[r].2 * alphabet[c].2) := by
  change (appendSource prev alphabet)[(appendIndexEquiv prev alphabet (r, c)).val] = _
  simp only [appendIndexEquiv_val]
  exact appendSource_get prev alphabet r c

/-- An injection on alphabet positions induces the literal row-major
injection on appended candidate positions. -/
def appendIndexEmbedding {Y : Type*} {q : Nat}
    (prev : Array ((Fin q → Y) × ℚ)) (small big : Array (Y × ℚ))
    (alphabetTrace : Fin small.size ↪ Fin big.size) :
    Fin (appendSource prev small).size ↪ Fin (appendSource prev big).size where
  toFun j := appendIndexEquiv prev big
    (((appendIndexEquiv prev small).symm j).1,
      alphabetTrace ((appendIndexEquiv prev small).symm j).2)
  inj' := by
    intro a b h
    apply (appendIndexEquiv prev small).symm.injective
    have hp := (appendIndexEquiv prev big).injective h
    apply Prod.ext
    · exact Prod.mk.inj hp |>.1
    · exact alphabetTrace.injective (Prod.mk.inj hp).2

theorem appendIndexEmbedding_decodes {Y : Type*} {q : Nat}
    (prev : Array ((Fin q → Y) × ℚ)) (small big : Array (Y × ℚ))
    (alphabetTrace : Fin small.size ↪ Fin big.size)
    (hdecode : ∀ j, small[j].1 = big[alphabetTrace j].1)
    (j : Fin (appendSource prev small).size) :
    (appendSource prev small)[j].1 =
      (appendSource prev big)[appendIndexEmbedding prev small big alphabetTrace j].1 := by
  let p := (appendIndexEquiv prev small).symm j
  have hj : appendIndexEquiv prev small p = j :=
    (appendIndexEquiv prev small).apply_symm_apply j
  have hs := congrArg (fun e : (Fin (q + 1) → Y) × ℚ => e.1)
    (appendIndexEquiv_entry prev small p.1 p.2)
  have hb := congrArg (fun e : (Fin (q + 1) → Y) × ℚ => e.1)
    (appendIndexEquiv_entry prev big p.1 (alphabetTrace p.2))
  change (appendSource prev small)[j].1 =
    (appendSource prev big)[appendIndexEquiv prev big (p.1, alphabetTrace p.2)].1
  calc
    (appendSource prev small)[j].1 =
        (appendSource prev small)[appendIndexEquiv prev small p].1 :=
      congrArg (fun k : Fin (appendSource prev small).size =>
        (appendSource prev small)[k].1) hj.symm
    _ = appendWord prev[p.1].1 small[p.2].1 := hs
    _ = appendWord prev[p.1].1 big[alphabetTrace p.2].1 := by rw [hdecode]
    _ = _ := hb.symm

theorem sequentialPreprocessed_stage_trace_original {Y : Type*}
    [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ))
    (hmass : sourceMass alphabet = 1)
    (q : Nat) (prev : Array ((Fin q → Y) × ℚ))
    (out : Array ((Fin (q + 1) → Y) × ℚ))
    (hprev : sequentialPreprocessed D alphabet q = some prev)
    (hout : sequentialPreprocessed D alphabet (q + 1) = some out) :
    Retained (appendSource prev alphabet) out := by
  have ha := alphabet_size_pos_of_mass_one alphabet hmass
  letI : Inhabited Y := ⟨alphabet[0].1⟩
  obtain ⟨a, ha, _⟩ := positiveLaw_trace alphabet hmass
  obtain ⟨s, hs⟩ := sequentialIndependent_stage_trace D
    (positiveLaw alphabet) q prev out hprev hout
  refine ⟨s.trans (appendIndexEmbedding prev (positiveLaw alphabet) alphabet a), ?_⟩
  intro j
  exact (hs j).trans
    (appendIndexEmbedding_decodes prev (positiveLaw alphabet) alphabet a ha (s j))

#print axioms appendIndexEquiv_entry
#print axioms positiveLaw_trace_exact
#print axioms appendIndexEmbedding_decodes
#print axioms sequentialPreprocessed_stage_trace_original

end CurrentAdditive.LabelTrace
