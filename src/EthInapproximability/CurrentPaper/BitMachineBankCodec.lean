import EthInapproximability.CurrentPaper.ProtocolWordField

/-!
# Packing a fixed finite bank of Boolean stacks

Source: locked v8 `B-effectivity-details.tex`, bit-model materialisation.
Each word uses the existing `EncodedCommunication.field` framing.  Parsing
charges individual marker and payload reads and reverses the temporary word
before installing it in the bank.  The finite bank size is a program constant,
not an unbounded internal register.  Malformed input is explicitly rejected.
-/

namespace EthInapproximability.CurrentPaper.BitMachineBankCodec

open Turing TM2.Stmt BitMachineEncoding EncodedCommunication

abbrev Stack (K : ℕ) := Fin K ⊕ Fin 3
abbrev Bank (K : ℕ) := Fin K → List Bool
abbrev Control := Option Bool

/-- Consecutive fields, in increasing bank-index order. -/
def encodeFrom {K : ℕ} (i : ℕ) (bank : Bank K) : List Bool :=
  if h : i < K then field (bank ⟨i, h⟩) ++ encodeFrom (i + 1) bank else []
termination_by K - i

def encode {K : ℕ} (bank : Bank K) : List Bool := encodeFrom 0 bank

/-- Pure semantics of the literal parser.  Initial bank words are retained as
tails; the public decoder starts with an empty bank. -/
def decodeFrom {K : ℕ} (i : ℕ) (input : List Bool) (bank : Bank K) : Option (Bank K) :=
  if h : i < K then
    match readField input with
    | none => none
    | some (word, rest) =>
        decodeFrom (i + 1) rest (Function.update bank ⟨i, h⟩ (word ++ bank ⟨i, h⟩))
  else if input = [] then some bank else none
termination_by K - i

def decode (K : ℕ) (input : List Bool) : Option (Bank K) :=
  decodeFrom 0 input (fun _ => [])

theorem decodeFrom_encodeFrom {K : ℕ} (i : ℕ) (before bank : Bank K)
    (hpast : ∀ j, j.val < i → before j = bank j)
    (hfuture : ∀ j, i ≤ j.val → before j = []) :
    decodeFrom i (encodeFrom i bank) before = some bank := by
  by_cases hi : i < K
  · rw [decodeFrom, dif_pos hi, encodeFrom, dif_pos hi, readField_append]
    have hz := hfuture ⟨i, hi⟩ (show i ≤ i from le_rfl)
    simp only [hz, List.append_nil]
    apply decodeFrom_encodeFrom
    · intro j hj
      by_cases he : j.val = i
      · have hj' : j = ⟨i, hi⟩ := Fin.ext he
        subst j
        simp
      · have hn : j ≠ ⟨i, hi⟩ := by intro h; exact he (congrArg Fin.val h)
        simpa only [Function.update_of_ne hn] using hpast j (by omega)
    · intro j hj
      have hn : j ≠ ⟨i, hi⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simpa only [Function.update_of_ne hn] using hfuture j (by omega)
  · rw [encodeFrom, dif_neg hi, decodeFrom, dif_neg hi, if_pos rfl]
    congr 1
    funext j
    exact hpast j (by omega)
termination_by K - i

@[simp] theorem decode_encode {K : ℕ} (bank : Bank K) :
    decode K (encode bank) = some bank := by
  apply decodeFrom_encodeFrom
  · intro j hj; omega
  · intro j hj; rfl

theorem decodeFrom_before {K : ℕ} (i : ℕ) (input : List Bool)
    (before bank : Bank K) (h : decodeFrom i input before = some bank)
    (j : Fin K) (hj : j.val < i) : bank j = before j := by
  rw [decodeFrom] at h
  split at h
  · rename_i hi
    cases hf : readField input with
    | none => simp only [hf] at h; cases h
    | some p =>
        rcases p with ⟨word, rest⟩
        simp only [hf] at h
        have hr := decodeFrom_before (i + 1) rest
          (Function.update before ⟨i, hi⟩ (word ++ before ⟨i, hi⟩)) bank h j (by omega)
        have hn : j ≠ ⟨i, hi⟩ := by intro he; have := congrArg Fin.val he; simp at this; omega
        simpa only [Function.update_of_ne hn] using hr
  · split at h
    · cases h; rfl
    · cases h
termination_by K - i

theorem decodeFrom_sound {K : ℕ} (i : ℕ) (input : List Bool)
    (before bank : Bank K) (h : decodeFrom i input before = some bank)
    (hfuture : ∀ j, i ≤ j.val → before j = []) :
    encodeFrom i bank = input := by
  rw [decodeFrom] at h
  split at h
  · rename_i hi
    cases hf : readField input with
    | none => simp only [hf] at h; cases h
    | some p =>
        rcases p with ⟨word, rest⟩
        simp only [hf] at h
        have hz := hfuture ⟨i, hi⟩ (show i ≤ i from le_rfl)
        have hword := decodeFrom_before (i + 1) rest
          (Function.update before ⟨i, hi⟩ (word ++ before ⟨i, hi⟩)) bank h ⟨i, hi⟩
          (show i < i + 1 by omega)
        simp only [Function.update_self, hz, List.append_nil] at hword
        have hnext := decodeFrom_sound (i + 1) rest
          (Function.update before ⟨i, hi⟩ (word ++ before ⟨i, hi⟩)) bank h (by
            intro j hj
            have hn : j ≠ ⟨i, hi⟩ := by
              intro he; have := congrArg Fin.val he; simp at this; omega
            simpa only [Function.update_of_ne hn] using hfuture j (by omega))
        rw [encodeFrom, dif_pos hi, hword, hnext]
        exact readField_sound hf
  · rename_i hi
    split at h
    · rename_i hz
      rw [encodeFrom, dif_neg hi, hz]
    · cases h
termination_by K - i

theorem encode_decode {K : ℕ} {input : List Bool} {bank : Bank K}
    (h : decode K input = some bank) : encode bank = input := by
  exact decodeFrom_sound 0 input (fun _ => []) bank h (by intros; rfl)

inductive ParserLabel (K : ℕ) where
  | scan : Fin (K + 1) → ParserLabel K
  | payload : Fin K → ParserLabel K
  | restore : Fin K → ParserLabel K
  deriving DecidableEq, Fintype

def contents {K : ℕ} (bank : Bank K) (source saved output : List Bool) :
    Stack K → List Bool :=
  Sum.elim bank (fun j => if j = 0 then source else if j = 1 then saved else output)

def parserCfg {K : ℕ} (l : Option (ParserLabel K)) (v : Control)
    (bank : Bank K) (source saved output : List Bool) :
    TM2.Cfg (fun _ : Stack K => Bool) (ParserLabel K) Control :=
  ⟨l, v, contents bank source saved output⟩

def fail {K : ℕ} : TM2.Stmt (fun _ : Stack K => Bool) (ParserLabel K) Control :=
  load (fun _ => some false) halt

def parser (K : ℕ) : ParserLabel K →
    TM2.Stmt (fun _ : Stack K => Bool) (ParserLabel K) Control
  | .scan i =>
      if h : i.val < K then
        pop (.inr 0) (fun _ b => b)
          (branch Option.isSome
            (branch (fun b => b.getD false)
              (goto (fun _ => .payload ⟨i.val, h⟩))
              (goto (fun _ => .restore ⟨i.val, h⟩))) fail)
      else
        pop (.inr 0) (fun _ b => b)
          (load (fun b => some b.isNone) halt)
  | .payload i =>
      pop (.inr 0) (fun _ b => b)
        (branch Option.isSome
          (push (.inr 1) (fun b => b.getD false)
            (goto (fun _ => .scan ⟨i.val, by omega⟩))) fail)
  | .restore i =>
      pop (.inr 1) (fun _ b => b)
        (branch Option.isSome
          (push (.inl i) (fun b => b.getD false) (goto (fun _ => .restore i)))
          (goto (fun _ => .scan ⟨i.val + 1, by omega⟩)))

def parserRun {K : ℕ} (n : ℕ)
    (c : TM2.Cfg (fun _ : Stack K => Bool) (ParserLabel K) Control) :=
  ((advance (parser K))^[n]) c

theorem parserRun_succ {K : ℕ} (n : ℕ)
    (c : TM2.Cfg (fun _ : Stack K => Bool) (ParserLabel K) Control) :
    parserRun (n + 1) c = parserRun n (advance (parser K) c) :=
  Function.iterate_succ_apply _ _ _

theorem parserRun_add {K : ℕ} (m n : ℕ)
    (c : TM2.Cfg (fun _ : Stack K => Bool) (ParserLabel K) Control) :
    parserRun (m + n) c = parserRun n (parserRun m c) := by
  simpa only [parserRun, Nat.add_comm] using
    Function.iterate_add_apply (advance (parser K)) n m c

theorem scan_nil {K : ℕ} (i : Fin K) (v : Control) (bank : Bank K)
    (saved output : List Bool) :
    advance (parser K)
      (parserCfg (some (.scan ⟨i.val, by omega⟩)) v bank [] saved output) =
      parserCfg none (some false) bank [] saved output := by
  simp only [advance, TM2.step, TM2.stepAux, parser, parserCfg, contents, fail,
    dif_pos i.isLt, Sum.elim_inr, ↓reduceIte, List.head?, List.tail,
    Option.isSome, Option.getD, cond_false]
  congr 1
  funext j
  cases j with
  | inl j => rfl
  | inr j => fin_cases j <;> rfl

theorem scan_false {K : ℕ} (i : Fin K) (v : Control) (bank : Bank K)
    (source saved output : List Bool) :
    advance (parser K)
      (parserCfg (some (.scan ⟨i.val, by omega⟩)) v bank (false :: source) saved output) =
      parserCfg (some (.restore i)) (some false) bank source saved output := by
  simp only [advance, TM2.step, TM2.stepAux, parser, parserCfg, contents,
    dif_pos i.isLt, Sum.elim_inr, ↓reduceIte, List.head?, List.tail,
    Option.isSome, Option.getD, cond_false, cond_true]
  congr 1
  funext j
  cases j with
  | inl j => rfl
  | inr j => fin_cases j <;> rfl

theorem scan_true {K : ℕ} (i : Fin K) (v : Control) (bank : Bank K)
    (source saved output : List Bool) :
    advance (parser K)
      (parserCfg (some (.scan ⟨i.val, by omega⟩)) v bank (true :: source) saved output) =
      parserCfg (some (.payload i)) (some true) bank source saved output := by
  simp only [advance, TM2.step, TM2.stepAux, parser, parserCfg, contents,
    dif_pos i.isLt, Sum.elim_inr, ↓reduceIte, List.head?, List.tail,
    Option.isSome, Option.getD, cond_true]
  congr 1
  funext j
  cases j with
  | inl j => rfl
  | inr j => fin_cases j <;> rfl

theorem payload_nil {K : ℕ} (i : Fin K) (v : Control) (bank : Bank K)
    (saved output : List Bool) :
    advance (parser K) (parserCfg (some (.payload i)) v bank [] saved output) =
      parserCfg none (some false) bank [] saved output := by
  simp only [advance, TM2.step, TM2.stepAux, parser, parserCfg, contents, fail,
    Sum.elim_inr, ↓reduceIte, List.head?, List.tail,
    Option.isSome, Option.getD, cond_false]
  congr 1
  funext j
  cases j with
  | inl j => rfl
  | inr j => fin_cases j <;> rfl

theorem payload_cons {K : ℕ} (i : Fin K) (v : Control) (bank : Bank K)
    (b : Bool) (source saved output : List Bool) :
    advance (parser K) (parserCfg (some (.payload i)) v bank (b :: source) saved output) =
      parserCfg (some (.scan ⟨i.val, by omega⟩)) (some b) bank source (b :: saved) output := by
  simp only [advance, TM2.step, TM2.stepAux, parser, parserCfg, contents,
    Sum.elim_inr, ↓reduceIte, List.head?, List.tail,
    Option.isSome, Option.getD, cond_true]
  congr 1
  funext j
  cases j with
  | inl j => rfl
  | inr j => fin_cases j <;> rfl

theorem restore_nil {K : ℕ} (i : Fin K) (v : Control) (bank : Bank K)
    (source output : List Bool) :
    advance (parser K) (parserCfg (some (.restore i)) v bank source [] output) =
      parserCfg (some (.scan ⟨i.val + 1, by omega⟩)) none bank source [] output := by
  simp only [advance, TM2.step, TM2.stepAux, parser, parserCfg, contents,
    Sum.elim_inr, ↓reduceIte, show (1 : Fin 3) ≠ 0 by decide, List.head?, List.tail,
    Option.isSome, Option.getD, cond_false]
  congr 1
  funext j
  cases j with
  | inl j => rfl
  | inr j => fin_cases j <;> rfl

theorem restore_cons {K : ℕ} (i : Fin K) (v : Control) (bank : Bank K)
    (b : Bool) (source saved output : List Bool) :
    advance (parser K) (parserCfg (some (.restore i)) v bank source (b :: saved) output) =
      parserCfg (some (.restore i)) (some b)
        (Function.update bank i (b :: bank i)) source saved output := by
  simp only [advance, TM2.step, TM2.stepAux, parser, parserCfg, contents,
    Sum.elim_inr, ↓reduceIte, show (1 : Fin 3) ≠ 0 by decide, List.head?, List.tail,
    Option.isSome, Option.getD, cond_true]
  congr 1
  funext j
  cases j with
  | inl j =>
      by_cases hj : j = i
      · subst j
        simp only [Function.update_self, Function.update_of_ne Sum.inl_ne_inr, Sum.elim_inl]
      · have hji : (Sum.inl j : Stack K) ≠ .inl i := fun h => hj (Sum.inl.inj h)
        simp only [Function.update_of_ne hji, Function.update_of_ne Sum.inl_ne_inr,
          Function.update_of_ne hj, Sum.elim_inl]
  | inr j => fin_cases j <;> rfl

theorem restore_correct {K : ℕ} (i : Fin K) (v : Control) (bank : Bank K)
    (source saved output : List Bool) :
    parserRun (saved.length + 1)
      (parserCfg (some (.restore i)) v bank source saved output) =
      parserCfg (some (.scan ⟨i.val + 1, by omega⟩)) none
        (Function.update bank i (saved.reverse ++ bank i)) source [] output := by
  induction saved generalizing v bank with
  | nil => simp [parserRun, restore_nil]
  | cons b saved ih =>
      rw [List.length_cons, parserRun_succ, restore_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

def FieldPost {K : ℕ} (i : Fin K) (bank : Bank K) (input saved output : List Bool)
    (c : TM2.Cfg (fun _ : Stack K => Bool) (ParserLabel K) Control) : Prop :=
  match readField input with
  | none => c.l = none ∧ c.var = some false ∧ c.stk (.inr 2) = output
  | some (word, rest) => c =
      parserCfg (some (.scan ⟨i.val + 1, by omega⟩)) none
        (Function.update bank i (saved.reverse ++ word ++ bank i)) rest [] output

theorem field_correct {K : ℕ} (i : Fin K) (input : List Bool) (v : Control)
    (bank : Bank K) (saved output : List Bool) :
    ∃ t ≤ 2 * input.length + saved.length + 2,
      FieldPost i bank input saved output
        (parserRun t (parserCfg (some (.scan ⟨i.val, by omega⟩)) v bank input saved output)) := by
  induction input using readField.induct generalizing v saved with
  | case1 =>
      refine ⟨1, by simp, ?_⟩
      change FieldPost i bank [] saved output
        (parserRun (0 + 1) (parserCfg _ v bank [] saved output))
      rw [parserRun_succ, scan_nil]
      simp [FieldPost, readField, parserRun, parserCfg, contents]
  | case2 rest =>
      refine ⟨saved.length + 2, by simp, ?_⟩
      rw [show saved.length + 2 = (saved.length + 1) + 1 by omega,
        parserRun_succ, scan_false, restore_correct]
      simp [FieldPost, readField]
  | case3 =>
      refine ⟨2, by simp, ?_⟩
      rw [show 2 = (0 + 1) + 1 from rfl, parserRun_succ, scan_true,
        parserRun_succ, payload_nil]
      simp [FieldPost, readField, parserRun, parserCfg, contents]
  | case4 b rest ih =>
      obtain ⟨t, ht, hpost⟩ := ih (some b) (b :: saved)
      refine ⟨t + 2, by simp at ht ⊢; omega, ?_⟩
      rw [show t + 2 = (t + 1) + 1 by omega, parserRun_succ, scan_true,
        parserRun_succ, payload_cons]
      cases hp : readField rest with
      | none => simpa [FieldPost, readField, hp] using hpost
      | some pair =>
          rcases pair with ⟨word, suffix⟩
          simpa [FieldPost, readField, hp, List.reverse_cons, List.append_assoc] using hpost

theorem scan_last {K : ℕ} (v : Control) (bank : Bank K)
    (input saved output : List Bool) :
    advance (parser K) (parserCfg (some (.scan (Fin.last K))) v bank input saved output) =
      parserCfg none (some input.isEmpty) bank input.tail saved output := by
  cases input with
  | nil =>
      simp only [advance, TM2.step, TM2.stepAux, parser, parserCfg, contents,
        Fin.val_last, lt_self_iff_false, ↓reduceDIte, Sum.elim_inr, ↓reduceIte,
        List.head?, List.tail, Option.isNone, Option.getD, List.isEmpty]
      congr 1
      funext j
      cases j with
      | inl j => rfl
      | inr j => fin_cases j <;> rfl
  | cons b input =>
      simp only [advance, TM2.step, TM2.stepAux, parser, parserCfg, contents,
        Fin.val_last, lt_self_iff_false, ↓reduceDIte, Sum.elim_inr, ↓reduceIte,
        List.head?, List.tail, Option.isNone, Option.getD, List.isEmpty]
      congr 1
      funext j
      cases j with
      | inl j => rfl
      | inr j => fin_cases j <;> rfl

def ParsePost {K : ℕ} (result : Option (Bank K)) (output : List Bool)
    (c : TM2.Cfg (fun _ : Stack K => Bool) (ParserLabel K) Control) : Prop :=
  match result with
  | none => c.l = none ∧ c.var = some false ∧ c.stk (.inr 2) = output
  | some bank => c = parserCfg none (some true) bank [] [] output

/-- All-input operational correctness.  The bound is linear in input length
for each fixed finite bank.  Successful parsing leaves both work stacks empty;
the output stack is framed and unchanged. -/
theorem parser_correct_from {K : ℕ} (i : Fin (K + 1)) (input : List Bool)
    (v : Control) (bank : Bank K) (output : List Bool) :
    ∃ t ≤ (2 * (K - i.val) + 1) * (input.length + 1),
      ParsePost (decodeFrom i.val input bank) output
        (parserRun t (parserCfg (some (.scan i)) v bank input [] output)) := by
  by_cases hi : i.val < K
  · let j : Fin K := ⟨i.val, hi⟩
    obtain ⟨t, ht, hf⟩ := field_correct j input v bank [] output
    cases hd : readField input with
    | none =>
        refine ⟨t, ?_, ?_⟩
        · simp only [List.length_nil, Nat.add_zero] at ht
          have hk : 1 ≤ K - i.val := by omega
          nlinarith
        · simpa [ParsePost, decodeFrom, hi, hd, FieldPost, j] using hf
    | some pair =>
        rcases pair with ⟨word, rest⟩
        obtain ⟨u, hu, hr⟩ := parser_correct_from ⟨i.val + 1, by omega⟩ rest none
          (Function.update bank j (word ++ bank j)) output
        have hrest : rest.length ≤ input.length := by
          have hs := congrArg List.length (readField_sound hd)
          simp only [List.length_append] at hs
          omega
        have hidx : K - i.val = K - (i.val + 1) + 1 := by omega
        refine ⟨t + u, ?_, ?_⟩
        · simp only [List.length_nil, Nat.add_zero] at ht
          have hbound := Nat.mul_le_mul_left (2 * (K - (i.val + 1)) + 1)
            (Nat.add_le_add_right hrest 1)
          dsimp only at hu
          rw [hidx]
          nlinarith
        · simp only [FieldPost, hd, List.reverse_nil, List.nil_append] at hf
          rw [parserRun_add]
          have hstart : (parserCfg (some (.scan i)) v bank input [] output) =
              parserCfg (some (.scan ⟨j.val, by omega⟩)) v bank input [] output := rfl
          rw [hstart, hf]
          rw [decodeFrom, dif_pos hi, hd]
          exact hr
  · have he : i = Fin.last K := Fin.ext (by change i.val = K; omega)
    subst i
    refine ⟨1, by simp, ?_⟩
    change ParsePost (decodeFrom K input bank) output
      (parserRun (0 + 1) (parserCfg (some (.scan (Fin.last K))) v bank input [] output))
    rw [parserRun_succ, scan_last]
    cases input <;> simp [ParsePost, decodeFrom, parserRun, parserCfg, contents]
termination_by K - i.val

theorem parser_correct (K : ℕ) (input output : List Bool) :
    ∃ t ≤ (2 * K + 1) * (input.length + 1),
      ParsePost (decode K input) output
        (parserRun t (parserCfg (some (.scan 0)) none (fun _ => []) input [] output)) := by
  simpa only [decode, Fin.val_zero, Nat.sub_zero] using
    parser_correct_from (0 : Fin (K + 1)) input none (fun _ => []) output

theorem encodeFrom_eq_drop {K : ℕ} (i : ℕ) (bank : Bank K) :
    encodeFrom i bank = ((List.ofFn bank).drop i).flatMap field := by
  by_cases hi : i < K
  · rw [encodeFrom, dif_pos hi,
      List.drop_eq_getElem_cons (show i < (List.ofFn bank).length by simpa using hi),
      List.flatMap_cons]
    congr 1
    · simp
    · exact encodeFrom_eq_drop (i + 1) bank
  · rw [encodeFrom, dif_neg hi]
    symm
    rw [List.drop_eq_nil_of_le (by simpa using Nat.le_of_not_gt hi)]
    rfl
termination_by K - i

theorem encode_eq_list {K : ℕ} (bank : Bank K) :
    encode bank = (List.ofFn bank).flatMap field := by
  simpa only [encode, List.drop_zero] using encodeFrom_eq_drop 0 bank

theorem encode_length {K : ℕ} (bank : Bank K) :
    (encode bank).length = 2 * (∑ j, (bank j).length) + K := by
  rw [encode_eq_list, List.length_flatMap]
  simp [List.map_ofFn, List.sum_ofFn, field_length, Finset.sum_add_distrib, Finset.mul_sum]

theorem word_length_le_encode {K : ℕ} (bank : Bank K) (j : Fin K) :
    (bank j).length ≤ (encode bank).length := by
  have h := Finset.single_le_sum (f := fun i : Fin K => (bank i).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  dsimp only at h
  rw [encode_length]
  omega

theorem decoded_word_length {K : ℕ} {input : List Bool} {bank : Bank K}
    (h : decode K input = some bank) (j : Fin K) :
    (bank j).length ≤ input.length := by
  rw [← encode_decode h]
  exact word_length_le_encode bank j

theorem codec_regressions :
    decode 0 [] = some (fun _ => []) ∧
    decode 0 [false] = none ∧
    decode 1 [false] = some (fun _ => []) ∧
    decode 1 [true] = none ∧
    decode 2 [false] = none ∧
    decode 2 [false, false] = some (fun _ => []) := by
  simp [decode, decodeFrom, readField]

end EthInapproximability.CurrentPaper.BitMachineBankCodec
