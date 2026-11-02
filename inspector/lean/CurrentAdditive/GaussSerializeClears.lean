import EthInapproximability.CurrentPaper.BitMachineBankSerialize

namespace CurrentAdditive.GaussSerializeClears

open Turing EthInapproximability.CurrentPaper
open BitMachineBankSerialize
open BitMachineEncoding
open EncodedCommunication

theorem emit_words_clear {K : ℕ} (words : List (List Bool)) (start : ℕ)
    (hbound : start + words.length ≤ K) (S : Bank K)
    (source saved output : List Bool)
    (hwords : ∀ j : Fin words.length,
      S ⟨start+j.val, by have := j.isLt; omega⟩ = words[j.val]) :
    ∃ S' : Bank K,
      run (emitTime words)
        (cfg (some (.emit ⟨start, by omega⟩)) none S source saved output) =
        cfg (some (.emit ⟨start+words.length, by omega⟩)) none S' source
          ((encode words).reverse ++ saved) output ∧
      (∀ j : Fin K, start ≤ j.val → j.val < start+words.length → S' j = []) ∧
      (∀ j : Fin K, (j.val < start ∨ start+words.length ≤ j.val) → S' j = S j) := by
  induction words generalizing start S saved with
  | nil =>
      refine ⟨S, ?_, ?_, ?_⟩
      · simp [emitTime, encode, run]
      · intro j h1 h2
        simp only [List.length_nil, Nat.add_zero] at h2
        omega
      · intro j hj; rfl
  | cons word words ih =>
      have hs : start < K := by simp only [List.length_cons] at hbound; omega
      let i : Fin K := ⟨start, hs⟩
      have hfirst : S i = word := by simpa [i] using hwords ⟨0, by simp⟩
      have hb : start+1+words.length ≤ K := by
        simp only [List.length_cons] at hbound; omega
      have hr : ∀ j : Fin words.length,
          (Function.update S i []) ⟨start+1+j.val, by have := j.isLt; omega⟩ =
          words[j.val] := by
        intro j
        have hne : (⟨start+1+j.val, by have := j.isLt; omega⟩ : Fin K) ≠ i := by
          intro h; have he := congrArg Fin.val h; simp only [i] at he; omega
        rw [Function.update_of_ne hne]
        simpa [Nat.add_assoc, Nat.add_comm 1 j.val] using
          hwords ⟨j.val+1, by simpa using j.isLt⟩
      obtain ⟨S', ht, hclear, hframe⟩ := ih (start+1) hb
        (Function.update S i []) ((field word).reverse ++ saved) hr
      refine ⟨S', ?_, ?_, ?_⟩
      · change run (word.length+1+emitTime words) _ = _
        rw [run_add, emit_word i none S word source saved output hfirst]
        change run (emitTime words)
          (cfg (some (.emit ⟨start+1, by omega⟩)) none
            (Function.update S i []) source
            ((field word).reverse ++ saved) output) = _
        rw [ht]
        simp [encode, List.append_assoc, Nat.add_assoc, Nat.add_comm 1 words.length]
      · intro j hjlo hjhi
        by_cases hj : j.val = start
        · have hf := hframe j (Or.inl (by omega))
          rw [hf]
          have he : j = i := Fin.ext hj
          subst j
          simp
        · exact hclear j (by omega) (by
            simp only [List.length_cons] at hjhi
            omega)
      · intro j hj
        have hj' : j.val < start+1 ∨ start+1+words.length ≤ j.val := by
          simp only [List.length_cons] at hj
          rcases hj with h | h <;> omega
        rw [hframe j hj']
        have hne : j ≠ i := by
          intro he; have hv := congrArg Fin.val he
          simp only [List.length_cons] at hj
          rcases hj with h | h <;> simp [i] at hv <;> omega
        rw [Function.update_of_ne hne]

theorem serialize_empty {K : ℕ} (S : Bank K) (source output : List Bool) :
    ∃ t ≤ 2 * (encode (List.ofFn S)).length + 2,
      run t (cfg (some (.emit 0)) none S source [] output) =
        cfg none none (fun _ => []) source []
          (encode (List.ofFn S) ++ output) := by
  let words := List.ofFn S
  have hw : words.length = K := List.length_ofFn
  obtain ⟨S', hs, hc, _⟩ := emit_words_clear words 0 (by omega)
    S source [] output (by intro j; simp [words])
  have hblank : S' = (fun _ => []) := by
    funext j
    exact hc j (by omega) (by simpa only [hw, Nat.zero_add] using j.isLt)
  let t := emitTime words + ((encode words).length + 2)
  refine ⟨t, ?_, ?_⟩
  · have hlen := emitTime_le words
    change emitTime words + ((encode words).length + 2) ≤
      2 * (encode words).length + 2
    omega
  · have hs' : run (emitTime words)
        (cfg (some (.emit (0 : Fin (K+1)))) none S source [] output) =
        cfg (some (.emit ⟨words.length, by omega⟩)) none S' source
          ((encode words).reverse ++ []) output := by
      simpa only [Nat.zero_add] using hs
    rw [show t = emitTime words + ((encode words).length + 1 + 1) by omega]
    rw [run_add, hs']
    simp only [List.append_nil, zero_add, hw]
    rw [run_succ, emit_end]
    have hlen : (encode words).length = ((encode words).reverse).length :=
      List.length_reverse.symm
    rw [hlen, finish_run]
    simp [words, hblank]

#print axioms serialize_empty

end CurrentAdditive.GaussSerializeClears
