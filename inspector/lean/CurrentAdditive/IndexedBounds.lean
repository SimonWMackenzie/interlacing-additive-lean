import CurrentAdditive.IndexedLaw
import CurrentAdditive.LabelTrace

namespace CurrentAdditive.IndexedLaw

open SequentialCode SequentialSourceCode IndependentSupport LabelTrace

def LabelsBounded {q : Nat} (m : Nat)
    (source : Array ((Fin q → Nat) × ℚ)) : Prop :=
  ∀ e ∈ source, ∀ i, e.1 i < m

theorem appendSource_bounded {m q : Nat}
    (prev : Array ((Fin q → Nat) × ℚ)) (alphabet : Array (Nat × ℚ))
    (hprev : LabelsBounded m prev)
    (halphabet : ∀ e ∈ alphabet, e.1 < m) :
    LabelsBounded m (appendSource prev alphabet) := by
  intro e he i
  have he' : e ∈ (appendSource prev alphabet).toList := by simpa using he
  rw [appendSource_toList] at he'
  obtain ⟨old, hold, he'⟩ := List.mem_flatMap.mp he'
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp he'
  by_cases hi : i.val < q
  · simpa [appendWord, hi] using hprev old (by simpa using hold) ⟨i.val, hi⟩
  · simpa [appendWord, hi] using halphabet y (by simpa using hy)

theorem sequentialIndependent_bounded {m : Nat} (D : Nat)
    (alphabet : Array (Nat × ℚ))
    (halphabet : ∀ e ∈ alphabet, e.1 < m) :
    ∀ q out, sequentialIndependent D alphabet q = some out →
      LabelsBounded m out := by
  intro q
  induction q with
  | zero =>
      intro out hout e he i
      exact Fin.elim0 i
  | succ q ih =>
      intro out hout
      cases hprev : sequentialIndependent D alphabet q with
      | none => simp [sequentialIndependent, hprev] at hout
      | some prev =>
          have hret := sequentialIndependent_stage_labels D alphabet q prev out hprev hout
          intro e he i
          obtain ⟨old, hold, hlabel⟩ := hret e he
          rw [← hlabel]
          exact appendSource_bounded prev alphabet (ih prev hprev) halphabet old hold i

theorem indexed_positiveLaw_bounded {m : Nat} (μ : Fin m → ℚ)
    (hmass : ∑ i, μ i = 1) :
    ∀ e ∈ positiveLaw (indexedAlphabet μ), e.1 < m := by
  have hmass' : sourceMass (indexedAlphabet μ) = 1 := by simpa using hmass
  obtain ⟨trace, htrace, _⟩ := positiveLaw_trace (indexedAlphabet μ) hmass'
  intro e he
  obtain ⟨i, hi, hget⟩ := Array.mem_iff_getElem.mp he
  have hlt := indexedAlphabet_label_bound μ
    ((indexedAlphabet μ)[trace ⟨i, hi⟩]) (Array.getElem_mem (trace ⟨i, hi⟩).isLt)
  have hlabel : e.1 = (indexedAlphabet μ)[trace ⟨i, hi⟩].1 := by
    calc
      e.1 = (positiveLaw (indexedAlphabet μ))[i].1 :=
        (congrArg Prod.fst hget).symm
      _ = (indexedAlphabet μ)[trace ⟨i, hi⟩].1 := by
        simpa only [Fin.getElem_fin] using htrace ⟨i, hi⟩
  rw [hlabel]
  exact hlt

theorem sequentialPreprocessed_index_bound {m : Nat} (D : Nat)
    (μ : Fin m → ℚ) (hmass : ∑ i, μ i = 1)
    (q : Nat) (out : Array ((Fin q → Nat) × ℚ))
    (hout : sequentialPreprocessed D (indexedAlphabet μ) q = some out) :
    LabelsBounded m out :=
  sequentialIndependent_bounded D (positiveLaw (indexedAlphabet μ))
    (indexed_positiveLaw_bounded μ hmass) q out hout

end CurrentAdditive.IndexedLaw
