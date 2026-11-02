import EthInapproximability.CurrentPaper.BitMachineBankCodec
import EthInapproximability.CurrentPaper.BitMachineInline

/-!
# Extracting one word from an encoded finite bank

Source: locked v8 Appendix B, bit-model implementation, and Section 8,
effective slow repetition. The ordinary input is parsed by the literal bank
parser. A successful parse transfers the selected field twice, charging one
transition per Boolean cell each time. Invalid packets return the empty word.
No host-language decoding operation is a machine instruction.
-/

namespace EthInapproximability.CurrentPaper.BankFieldProjection

open Turing TM2.Stmt BitMachineEncoding BitMachineBankCodec

inductive Admin where
  | parsed | move | restore
  deriving DecidableEq, Fintype

abbrev Label (K : ℕ) := ParserLabel K ⊕ Admin

def program {K : ℕ} (j : Fin K) : Label K →
    TM2.Stmt (fun _ : Stack K => Bool) (Label K) Control
  | .inl l => BitMachineInline.stmt Sum.inl id id (some (.inr .parsed)) (parser K l)
  | .inr .parsed => branch (fun v => v.getD false)
      (goto (fun _ => .inr .move)) halt
  | .inr .move => pop (.inl j) (fun _ b => b)
      (branch Option.isSome
        (push (.inr 1) (fun v => v.getD false) (goto (fun _ => .inr .move)))
        (goto (fun _ => .inr .restore)))
  | .inr .restore => pop (.inr 1) (fun _ b => b)
      (branch Option.isSome
        (push (.inr 2) (fun v => v.getD false) (goto (fun _ => .inr .restore))) halt)

def cfg {K : ℕ} (l : Option (Label K)) (v : Control) (bank : Bank K)
    (source saved output : List Bool) :
    TM2.Cfg (fun _ : Stack K => Bool) (Label K) Control :=
  ⟨l, v, contents bank source saved output⟩

def run {K : ℕ} (j : Fin K) (t : ℕ)
    (c : TM2.Cfg (fun _ : Stack K => Bool) (Label K) Control) :=
  ((advance (program j))^[t]) c

theorem run_add {K : ℕ} (j : Fin K) (t u : ℕ)
    (c : TM2.Cfg (fun _ : Stack K => Bool) (Label K) Control) :
    run j (t+u) c = run j u (run j t c) := by
  simpa only [run, Nat.add_comm] using
    Function.iterate_add_apply (advance (program j)) u t c

theorem run_succ {K : ℕ} (j : Fin K) (t : ℕ)
    (c : TM2.Cfg (fun _ : Stack K => Bool) (Label K) Control) :
    run j (t+1) c = run j t (advance (program j) c) :=
  Function.iterate_succ_apply _ _ _

theorem parsed_step {K : ℕ} (j : Fin K) (bank : Bank K) :
    advance (program j) (cfg (some (.inr .parsed)) (some true) bank [] [] []) =
      cfg (some (.inr .move)) (some true) bank [] [] [] := rfl

theorem move_nil {K : ℕ} (j : Fin K) (v : Control) (bank : Bank K)
    (source saved output : List Bool) (hj : bank j = []) :
    advance (program j) (cfg (some (.inr .move)) v bank source saved output) =
      cfg (some (.inr .restore)) none bank source saved output := by
  simp only [advance, TM2.step, program, cfg, contents, TM2.stepAux,
    Sum.elim_inl, hj, List.head?, List.tail, Option.isSome, cond_false, Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k =>
      by_cases hk : k = j
      · subst k; simp only [Function.update_self, Sum.elim_inl, hj]
      · simp only [Function.update_of_ne (show (Sum.inl k : Stack K) ≠ .inl j from
          fun h => hk (Sum.inl.inj h)), Sum.elim_inl]
  | inr k => rfl

theorem move_cons {K : ℕ} (j : Fin K) (v : Control) (bank : Bank K)
    (b : Bool) (word source saved output : List Bool) (hj : bank j = b :: word) :
    advance (program j) (cfg (some (.inr .move)) v bank source saved output) =
      cfg (some (.inr .move)) (some b) (Function.update bank j word)
        source (b :: saved) output := by
  simp only [advance, TM2.step, program, cfg, contents, TM2.stepAux,
    Sum.elim_inl, hj, List.head?, List.tail, Option.isSome, cond_true,
    Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k =>
      by_cases hk : k = j
      · subst k
        simp only [Function.update_of_ne Sum.inl_ne_inr, Function.update_self, Sum.elim_inl]
      · simp only [Function.update_of_ne Sum.inl_ne_inr,
          Function.update_of_ne (show (Sum.inl k : Stack K) ≠ .inl j from
            fun h => hk (Sum.inl.inj h)), Function.update_of_ne hk, Sum.elim_inl]
  | inr k => fin_cases k <;> rfl

theorem move_run {K : ℕ} (j : Fin K) (word : List Bool) (v : Control)
    (bank : Bank K) (source saved output : List Bool) (hj : bank j = word) :
    run j (word.length+1) (cfg (some (.inr .move)) v bank source saved output) =
      cfg (some (.inr .restore)) none (Function.update bank j [])
        source (word.reverse ++ saved) output := by
  induction word generalizing v bank saved with
  | nil =>
      simp only [List.length_nil, Nat.zero_add, run, Function.iterate_one,
        List.reverse_nil, List.nil_append]
      rw [move_nil j v bank source saved output hj]
      rw [Function.update_eq_self_iff.mpr hj.symm]
  | cons b word ih =>
      rw [List.length_cons, run_succ, move_cons j v bank b word source saved output hj,
        ih (some b) (Function.update bank j word) (b :: saved) (by simp)]
      simp only [Function.update_idem, List.reverse_cons, List.append_assoc,
        List.singleton_append]

theorem restore_nil {K : ℕ} (j : Fin K) (v : Control) (bank : Bank K)
    (source output : List Bool) :
    advance (program j) (cfg (some (.inr .restore)) v bank source [] output) =
      cfg none none bank source [] output := by
  simp only [advance, TM2.step, program, cfg, contents, TM2.stepAux,
    Sum.elim_inr, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte,
    List.head?, List.tail, Option.isSome, cond_false, Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl

theorem restore_cons {K : ℕ} (j : Fin K) (v : Control) (bank : Bank K)
    (b : Bool) (source saved output : List Bool) :
    advance (program j) (cfg (some (.inr .restore)) v bank source (b :: saved) output) =
      cfg (some (.inr .restore)) (some b) bank source saved (b :: output) := by
  simp only [advance, TM2.step, program, cfg, contents, TM2.stepAux,
    Sum.elim_inr, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte,
    List.head?, List.tail, Option.isSome, cond_true, Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl

theorem restore_run {K : ℕ} (j : Fin K) (saved : List Bool) (v : Control)
    (bank : Bank K) (source output : List Bool) :
    run j (saved.length+1) (cfg (some (.inr .restore)) v bank source saved output) =
      cfg none none bank source [] (saved.reverse ++ output) := by
  induction saved generalizing v output with
  | nil => simp [run, restore_nil]
  | cons b saved ih =>
      rw [List.length_cons, run_succ, restore_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

theorem parse_run {K : ℕ} (j : Fin K) (input : List Bool) (bank : Bank K)
    (hd : decode K input = some bank) :
    ∃ t ≤ (2*K+1)*(input.length+1),
      run j t (cfg (some (.inl (.scan 0))) none (fun _ => []) input [] []) =
        cfg (some (.inr .parsed)) (some true) bank [] [] [] := by
  obtain ⟨t, ht, hp⟩ := parser_correct K input []
  rw [hd] at hp
  change parserRun t (parserCfg (some (.scan 0)) none (fun _ => []) input [] []) =
    parserCfg none (some true) bank [] [] [] at hp
  have hh := congrArg (fun c => c.l) hp
  change _ = none at hh
  obtain ⟨u, hu, hr⟩ := BitMachineInline.outputs
    (Sum.inl : ParserLabel K → Label K) id id (fun _ => rfl)
    (some (.inr .parsed)) (parser K) (program j) (fun _ => rfl)
    (parserCfg (some (.scan 0)) none (fun _ => []) input [] []) t hh
  refine ⟨u, hu.trans ht, ?_⟩
  unfold parserRun at hp
  rw [hp] at hr
  exact hr

theorem valid_run {K : ℕ} (j : Fin K) (input : List Bool) (bank : Bank K)
    (hd : decode K input = some bank) :
    ∃ t ≤ (2*K+3)*(input.length+1)+1,
      run j t (cfg (some (.inl (.scan 0))) none (fun _ => []) input [] []) =
        cfg none none (Function.update bank j []) [] [] (bank j) := by
  obtain ⟨a, ha, hp⟩ := parse_run j input bank hd
  have hl := decoded_word_length hd j
  refine ⟨a+1+((bank j).length+1)+((bank j).length+1), by nlinarith, ?_⟩
  rw [run_add j (a+1+((bank j).length+1)) ((bank j).length+1),
    run_add j (a+1) ((bank j).length+1), run_add j a 1, hp]
  have hone : run j 1 (cfg (some (.inr .parsed)) (some true) bank [] [] []) =
      cfg (some (.inr .move)) (some true) bank [] [] [] := parsed_step j bank
  rw [hone]
  change run j ((bank j).length+1)
    (run j ((bank j).length+1) (cfg (some (.inr .move)) (some true) bank [] [] [])) = _
  rw [move_run j (bank j) (some true) bank [] [] [] rfl]
  simp only [List.append_nil]
  have hr := restore_run j (bank j).reverse none (Function.update bank j []) [] []
  simpa only [List.length_reverse, List.reverse_reverse, List.append_nil] using hr

theorem reject_run {K : ℕ} (j : Fin K) (input : List Bool)
    (hd : decode K input = none) :
    ∃ t ≤ (2*K+1)*(input.length+1)+1,
      let c := run j t (cfg (some (.inl (.scan 0))) none (fun _ => []) input [] [])
      c.l = none ∧ c.stk (.inr 2) = [] := by
  obtain ⟨t, ht, hp⟩ := parser_correct K input []
  rw [hd] at hp
  change (parserRun t _).l = none ∧ (parserRun t _).var = some false ∧
    (parserRun t _).stk (.inr 2) = [] at hp
  let c : TM2.Cfg (fun _ : Stack K => Bool) (ParserLabel K) Control :=
    parserRun t (parserCfg (some (.scan 0)) none (fun _ => []) input [] [])
  change c.l = none ∧ c.var = some false ∧ c.stk (.inr 2) = [] at hp
  obtain ⟨u, hu, hr⟩ := BitMachineInline.outputs
    (Sum.inl : ParserLabel K → Label K) id id (fun _ => rfl)
    (some (.inr .parsed)) (parser K) (program j) (fun _ => rfl)
    (parserCfg (some (.scan 0)) none (fun _ => []) input [] []) t hp.1
  have hf : advance (program j)
      (BitMachineInline.cfg (Sum.inl : ParserLabel K → Label K) id
        (some (.inr .parsed)) c) =
      (⟨none, some false, c.stk⟩ : TM2.Cfg (fun _ : Stack K => Bool) (Label K) Control) := by
    simp only [BitMachineInline.cfg, hp.1, hp.2.1, id_eq, advance, TM2.step,
      program, TM2.stepAux, Option.getD_some, cond_false]
  refine ⟨u+1, by omega, ?_⟩
  change _ ∧ _
  change run j u (cfg (some (.inl (.scan 0))) none (fun _ => []) input [] []) =
    BitMachineInline.cfg (Sum.inl : ParserLabel K → Label K) id
      (some (.inr .parsed)) c at hr
  rw [run_add]
  simp only [run, Function.iterate_one] at hr ⊢
  rw [hr, hf]
  exact ⟨rfl, hp.2.2⟩

def result {K : ℕ} (j : Fin K) (input : List Bool) : List Bool :=
  match decode K input with
  | none => []
  | some bank => bank j

@[simp] theorem result_encode {K : ℕ} (j : Fin K) (bank : Bank K) :
    result j (encode bank) = bank j := by simp [result]

noncomputable def machine {K : ℕ} (j : Fin K) : BitMachine.Machine :=
  ofFinite (.inr 0 : Stack K) (.inr 2) (.inl (.scan 0)) none (program j)

theorem initial_cfg {K : ℕ} (input : List Bool) :
    rawInit (.inr 0 : Stack K) (.inl (.scan 0) : Label K) none input =
      cfg (some (.inl (.scan 0))) none (fun _ => []) input [] [] := by
  unfold rawInit cfg contents
  congr 1
  funext k
  cases k with
  | inl k => simp
  | inr k => fin_cases k <;> rfl

theorem outputs {K : ℕ} (j : Fin K) (input : List Bool) :
    (machine j).OutputsWithin input (result j input) ((2*K+4)*(input.length+1)) := by
  cases hd : decode K input with
  | none =>
      obtain ⟨t, ht, hh, ho⟩ := reject_run j input hd
      apply outputsWithin_of_raw_run (.inr 0 : Stack K) (.inr 2) (.inl (.scan 0))
        none (program j) input (result j input) t _ (by nlinarith)
      · simpa only [initial_cfg, run] using hh
      · simpa only [initial_cfg, run, result, hd] using ho
  | some bank =>
      obtain ⟨t, ht, he⟩ := valid_run j input bank hd
      apply outputsWithin_of_raw_run (.inr 0 : Stack K) (.inr 2) (.inl (.scan 0))
        none (program j) input (result j input) t _ (by nlinarith)
      · change (run j t _).l = none
        rw [initial_cfg, he]
        rfl
      · change (run j t _).stk (.inr 2) = _
        rw [initial_cfg, he]
        simp only [cfg, contents, result, hd, Sum.elim_inr,
          show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte]

theorem result_length {K : ℕ} (j : Fin K) (input : List Bool) :
    (result j input).length ≤ input.length := by
  cases hd : decode K input with
  | none => simp [result, hd]
  | some bank => simpa only [result, hd] using decoded_word_length hd j

theorem polytime {K : ℕ} (j : Fin K) : BitMachine.Polytime (result j) := by
  refine ⟨machine j, 2*K+4, 1, ?_⟩
  intro input
  simpa only [pow_one] using outputs j input

end EthInapproximability.CurrentPaper.BankFieldProjection
