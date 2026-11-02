import EthInapproximability.CurrentPaper.BitMachineInline
import EthInapproximability.CurrentPaper.EncodedCommunication

/-!
# Serializing a fixed bank of Boolean stacks

Source: frozen v8 `B-effectivity-details.tex`, literal bit-model writing.
The bank size is a fixed program constant. Each word is written with the
existing field framing, and a final reversal restores natural field order.
Every payload bit, field marker and reversal is an actual TM2 instruction.
-/

namespace EthInapproximability.CurrentPaper.BitMachineBankSerialize

open Turing TM2.Stmt BitMachineEncoding EncodedCommunication

abbrev Stack (K : ℕ) := Fin K ⊕ Fin 3
abbrev Bank (K : ℕ) := Fin K → List Bool

inductive Label (K : ℕ) where
  | emit : Fin (K + 1) → Label K
  | finish
  deriving DecidableEq, Fintype

def contents {K : ℕ} (S : Bank K) (source saved output : List Bool) : Stack K → List Bool :=
  Sum.elim S (fun j => if j = 0 then source else if j = 1 then saved else output)

def cfg {K : ℕ} (l : Option (Label K)) (v : Option Bool)
    (S : Bank K) (source saved output : List Bool) :
    TM2.Cfg (fun _ : Stack K => Bool) (Label K) (Option Bool) :=
  ⟨l, v, contents S source saved output⟩

def program (K : ℕ) : Label K →
    TM2.Stmt (fun _ : Stack K => Bool) (Label K) (Option Bool)
  | .emit i => if h : i.val < K then
      pop (.inl ⟨i.val, h⟩) (fun _ b => b)
        (branch Option.isSome
          (push (.inr 1) (fun _ => true)
            (push (.inr 1) (fun b => b.getD false) (goto (fun _ => .emit i))))
          (push (.inr 1) (fun _ => false)
            (goto (fun _ => .emit ⟨i.val+1, by omega⟩))))
      else load (fun _ => none) (goto (fun _ => .finish))
  | .finish => pop (.inr 1) (fun _ b => b)
      (branch Option.isSome
        (push (.inr 2) (fun b => b.getD false) (goto (fun _ => .finish))) halt)

def run {K : ℕ} (t : ℕ)
    (c : TM2.Cfg (fun _ : Stack K => Bool) (Label K) (Option Bool)) :=
  ((advance (program K))^[t]) c

theorem run_succ {K : ℕ} (t : ℕ)
    (c : TM2.Cfg (fun _ : Stack K => Bool) (Label K) (Option Bool)) :
    run (t+1) c = run t (advance (program K) c) :=
  Function.iterate_succ_apply _ _ _

theorem run_add {K : ℕ} (t u : ℕ)
    (c : TM2.Cfg (fun _ : Stack K => Bool) (Label K) (Option Bool)) :
    run (t+u) c = run u (run t c) := by
  simpa only [run, Nat.add_comm] using Function.iterate_add_apply (advance (program K)) u t c

theorem emit_cons {K : ℕ} (i : Fin K) (v : Option Bool) (S : Bank K)
    (b : Bool) (q source saved output : List Bool) (hS : S i = b :: q) :
    advance (program K) (cfg (some (.emit ⟨i.val, by omega⟩)) v S source saved output) =
      cfg (some (.emit ⟨i.val, by omega⟩)) (some b)
        (Function.update S i q) source (b :: true :: saved) output := by
  simp only [advance, cfg, TM2.step, program, dif_pos i.isLt, TM2.stepAux,
    contents, Sum.elim_inl, hS, List.head?_cons, List.tail_cons,
    Option.isSome_some, cond_true, Option.getD_some]
  congr 1
  funext j
  cases j with
  | inl j => simp only [Function.update_apply, Sum.elim_inl, Sum.inl.injEq,
      Sum.inl_ne_inr, ↓reduceIte]
  | inr j => fin_cases j <;> rfl

theorem emit_nil {K : ℕ} (i : Fin K) (v : Option Bool) (S : Bank K)
    (source saved output : List Bool) (hS : S i = []) :
    advance (program K) (cfg (some (.emit ⟨i.val, by omega⟩)) v S source saved output) =
      cfg (some (.emit ⟨i.val+1, by omega⟩)) none S source (false :: saved) output := by
  simp only [advance, cfg, TM2.step, program, dif_pos i.isLt, TM2.stepAux,
    contents, Sum.elim_inl, hS, List.head?_nil, List.tail_nil,
    Option.isSome_none, cond_false, Option.getD_some]
  congr 1
  funext j
  cases j with
  | inl j =>
      by_cases h : j = i
      · subst j; simp only [Function.update_apply, Sum.elim_inl, hS, ↓reduceIte,
          Sum.inl_ne_inr]
      · simp only [Function.update_apply, Sum.elim_inl, Sum.inl.injEq, h,
          ↓reduceIte, Sum.inl_ne_inr]
  | inr j => fin_cases j <;> rfl

theorem emit_word {K : ℕ} (i : Fin K) (v : Option Bool) (S : Bank K)
    (word source saved output : List Bool) (hS : S i = word) :
    run (word.length+1) (cfg (some (.emit ⟨i.val, by omega⟩)) v S source saved output) =
      cfg (some (.emit ⟨i.val+1, by omega⟩)) none
        (Function.update S i []) source ((field word).reverse ++ saved) output := by
  induction word generalizing v S saved with
  | nil =>
      rw [show ([] : List Bool).length+1 = 0+1 from rfl, run_succ, emit_nil i v S _ _ _ hS]
      have hu : Function.update S i [] = S := by rw [← hS, Function.update_eq_self]
      simp [run, field, hu]
  | cons b q ih =>
      rw [List.length_cons, run_succ, emit_cons i v S b q _ _ _ hS,
        ih _ _ _ (Function.update_self _ _ _)]
      simp [field, Function.update_idem, List.append_assoc]

def encode (words : List (List Bool)) : List Bool := words.flatMap field

def emitTime (words : List (List Bool)) : ℕ :=
  words.foldr (fun word t => word.length+1+t) 0

theorem emitTime_le (words : List (List Bool)) : emitTime words ≤ (encode words).length := by
  induction words with
  | nil => simp [emitTime, encode]
  | cons word words ih =>
      simp only [emitTime, List.foldr_cons, encode, List.flatMap_cons, List.length_append] at *
      have hl := field_length word
      omega

theorem emit_words {K : ℕ} (words : List (List Bool)) (start : ℕ)
    (hbound : start + words.length ≤ K) (S : Bank K) (source saved output : List Bool)
    (hwords : ∀ j : Fin words.length,
      S ⟨start+j.val, by have := j.isLt; omega⟩ = words[j.val]) :
    ∃ S' : Bank K,
      run (emitTime words) (cfg (some (.emit ⟨start, by omega⟩)) none S source saved output) =
        cfg (some (.emit ⟨start+words.length, by omega⟩)) none S' source
          ((encode words).reverse ++ saved) output := by
  induction words generalizing start S saved with
  | nil => exact ⟨S, by simp [emitTime, encode, run]⟩
  | cons word words ih =>
      have hs : start < K := by simp only [List.length_cons] at hbound; omega
      let i : Fin K := ⟨start, hs⟩
      have hfirst : S i = word := by simpa [i] using hwords ⟨0, by simp⟩
      have hb : start+1+words.length ≤ K := by simp only [List.length_cons] at hbound; omega
      have hr : ∀ j : Fin words.length,
          (Function.update S i []) ⟨start+1+j.val, by have := j.isLt; omega⟩ = words[j.val] := by
        intro j
        have hne : (⟨start+1+j.val, by have := j.isLt; omega⟩ : Fin K) ≠ i := by
          intro h; have he := congrArg Fin.val h; simp only [i] at he; omega
        rw [Function.update_of_ne hne]
        simpa [Nat.add_assoc, Nat.add_comm 1 j.val] using hwords ⟨j.val+1, by simpa using j.isLt⟩
      obtain ⟨S', ht⟩ := ih (start+1) hb (Function.update S i [])
        ((field word).reverse ++ saved) hr
      refine ⟨S', ?_⟩
      change run (word.length+1+emitTime words) _ = _
      rw [run_add, emit_word i none S word source saved output hfirst]
      change run (emitTime words)
        (cfg (some (.emit ⟨start+1, by omega⟩)) none (Function.update S i [])
          source ((field word).reverse ++ saved) output) = _
      rw [ht]
      simp [encode, List.append_assoc, Nat.add_assoc, Nat.add_comm 1 words.length]

theorem finish_cons {K : ℕ} (v : Option Bool) (S : Bank K)
    (b : Bool) (source saved output : List Bool) :
    advance (program K) (cfg (some .finish) v S source (b :: saved) output) =
      cfg (some .finish) (some b) S source saved (b :: output) := by
  simp only [advance, cfg, TM2.step, program, TM2.stepAux, contents,
    Sum.elim_inr, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte, List.head?_cons, List.tail_cons,
    Option.isSome_some, cond_true, Option.getD_some]
  congr 1
  funext j
  cases j with
  | inl j => rfl
  | inr j => fin_cases j <;> rfl

theorem finish_nil {K : ℕ} (v : Option Bool) (S : Bank K) (source output : List Bool) :
    advance (program K) (cfg (some .finish) v S source [] output) =
      cfg none none S source [] output := by
  simp only [advance, cfg, TM2.step, program, TM2.stepAux, contents,
    Sum.elim_inr, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte, List.head?_nil, List.tail_nil,
    Option.isSome_none, cond_false, Option.getD_some]
  congr 1
  funext j
  cases j with
  | inl j => rfl
  | inr j => fin_cases j <;> rfl

theorem finish_run {K : ℕ} (v : Option Bool) (S : Bank K) (source saved output : List Bool) :
    run (saved.length+1) (cfg (some .finish) v S source saved output) =
      cfg none none S source [] (saved.reverse ++ output) := by
  induction saved generalizing v output with
  | nil => simp [run_succ, finish_nil, run]
  | cons b saved ih =>
      rw [List.length_cons, run_succ, finish_cons, ih]
      simp

theorem emit_end {K : ℕ} (S : Bank K) (source saved output : List Bool) :
    advance (program K) (cfg (some (.emit ⟨K, by omega⟩)) none S source saved output) =
      cfg (some .finish) none S source saved output := by
  simp [advance, cfg, TM2.step, program, TM2.stepAux]

/-- Literal field serialization, including final reversal. The source stack
and existing output suffix are unchanged. The word bank is consumed. -/
theorem serialize {K : ℕ} (S : Bank K) (source output : List Bool) :
    ∃ (t : ℕ) (S' : Bank K), t ≤ 2*(encode (List.ofFn S)).length+2 ∧
      run t (cfg (some (.emit 0)) none S source [] output) =
        cfg none none S' source [] (encode (List.ofFn S) ++ output) := by
  let words := List.ofFn S
  have hw : words.length = K := List.length_ofFn
  obtain ⟨S', hs⟩ := emit_words words 0 (by omega) S source [] output (by
    intro j; simp [words])
  let t := emitTime words + ((encode words).length+2)
  refine ⟨t, S', ?_, ?_⟩
  · have := emitTime_le words
    change emitTime words + ((encode words).length+2) ≤ 2*(encode words).length+2
    omega
  · have hs' : run (emitTime words) (cfg (some (.emit (0 : Fin (K+1)))) none S source [] output) =
        cfg (some (.emit ⟨words.length, by omega⟩)) none S' source
          ((encode words).reverse ++ []) output := by simpa only [Nat.zero_add] using hs
    rw [show t = emitTime words + ((encode words).length+1+1) by omega]
    rw [run_add, hs']
    simp only [List.append_nil, zero_add, hw]
    rw [run_succ, emit_end]
    have hlen : (encode words).length = ((encode words).reverse).length := List.length_reverse.symm
    rw [hlen, finish_run]
    simp [words]

end EthInapproximability.CurrentPaper.BitMachineBankSerialize
