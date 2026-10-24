import EthInapproximability.CurrentPaper.SourceCSPRowController

/-!
# Total operational parsing of a fixed constraint row

Source: frozen v8 `06-eth.tex`, `thm:paper-sparse-gap-source`, explicit
source construction. This file treats malformed canonical fields and
truncated truth tables. Vertex-range comparison remains separately exposed.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowController

open Turing BitMachineEncoding EncodedCommunication

theorem after_failure {q H : ℕ} (i : Fin q) (v : Control) (S : Stack q → List Bool)
    (word : List Bool) (hword : S (.inl i) = false :: word) :
    (advance (program q H) ⟨some (.after i), v, S⟩).l = none ∧
      (advance (program q H) ⟨some (.after i), v, S⟩).stk (.inr 2) =
        false :: S (.inr 2) := by
  simp only [advance, TM2.step, TM2.stepAux, program, hword, List.head?, List.tail,
    Option.getD_some, cond_false, Function.update_self,
    Function.update_of_ne Sum.inr_ne_inl]
  exact ⟨True.intro, True.intro⟩

theorem header_failure_run {q H : ℕ} (i : Fin q) (bank : Bank q)
    (input output : List Bool) (hf : readNat input = none) :
    ∃ t ≤ 2 * input.length + 3,
      let c := run (H := H) t
        (cfg (some (.header i .scan)) (none, none) bank input [] output)
      c.l = none ∧ c.stk (.inr 2) = false :: output := by
  have hh : ProtocolBinaryHeader.readChecked none input = none := by
    have hm := ProtocolBinaryHeader.readChecked_readNat input
    rw [hf] at hm
    cases hx : ProtocolBinaryHeader.readChecked none input with
    | none => rfl
    | some p => simp [hx] at hm
  let localStart := ProtocolBinaryHeader.cfg (some .scan) (none, none) input [] (bank i)
  obtain ⟨t, ht, hp⟩ := ProtocolBinaryHeader.scan_correct input none none [] (bank i)
  simp only [ProtocolBinaryHeader.Post, hh] at hp
  let terminal := ProtocolBinaryHeader.run t localStart
  have hl : terminal.l = none := hp.1
  have hout : terminal.stk 2 = false :: bank i := hp.2
  obtain ⟨u, hu, hr⟩ := BitMachineStackEmbedding.outputs (fieldStacks i)
    (contents bank input [] output) (.header i : ProtocolBinaryHeader.Label → Label q H)
    id id (fun _ => rfl) (some (.after i)) ProtocolBinaryHeader.program
    (program q H) (fun _ => rfl) localStart t hp.1
  let S := BitMachineStackEmbedding.bank (fieldStacks i) (contents bank input [] output) terminal.stk
  have hs : S (.inl i) = false :: bank i := by
    have hb := BitMachineStackEmbedding.bank_at (fieldStacks i) (contents bank input [] output)
      terminal.stk (2 : Fin 3)
    simpa only [fieldStacks, ↓reduceIte, show ¬(2 : Fin 3) = 0 by decide,
      show ¬(2 : Fin 3) = 1 by decide, hout] using hb
  have hframe : S (.inr 2) = output := by
    have he : ¬∃ k, fieldStacks i k = Sum.inr (2 : Fin 3) := by
      rintro ⟨k, hk⟩
      fin_cases k <;> simp [fieldStacks] at hk
    exact BitMachineStackEmbedding.bank_outside _ _ _ _ he
  have hrun : run u (cfg (some (.header i .scan)) (none, none) bank input [] output) =
      (⟨some (.after i), terminal.var, S⟩ : TM2.Cfg (fun _ : Stack q => Bool) (Label q H) Control) := by
    change run u _ = BitMachineStackEmbedding.cfg _ _ _ _ _ terminal at hr
    simp only [localStart, field_cfg, Function.update_eq_self] at hr
    simpa only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, hl, id_eq] using hr
  refine ⟨u + 1, by simp only [List.length_nil, Nat.add_zero] at ht; omega, ?_⟩
  rw [run_add, run_one, hrun]
  simpa only [hframe] using after_failure (H := H) i terminal.var S (bank i) hs

def readQueriesFrom {q : ℕ} (i : ℕ) (input : List Bool) (bank : Bank q) :
    Option (Bank q × List Bool) :=
  if h : i < q then do
    let (n, rest) ← readNat input
    readQueriesFrom (i + 1) rest (Function.update bank ⟨i, h⟩ (n.bits ++ bank ⟨i, h⟩))
  else some (bank, input)
termination_by q - i

def QueriesPost {q H : ℕ} (parsed : Option (Bank q × List Bool)) (output : List Bool)
    (c : TM2.Cfg (fun _ : Stack q => Bool) (Label q H) Control) : Prop :=
  match parsed with
  | none => c.l = none ∧ c.stk (.inr 2) = false :: output
  | some (bank, rest) => ∃ w, c = cfg (some (.start (Fin.last q))) w bank rest [] output

/-- Every input reaches either genuine rejection or the exact parsed query
bank. The bound depends on the physical input length, including on failure. -/
theorem queries_total_from {q H : ℕ} (i : Fin (q + 1)) (input : List Bool)
    (bank : Bank q) (v : Control) (output : List Bool) :
    ∃ t ≤ (q - i.val) * (2 * input.length + 4),
      QueriesPost (readQueriesFrom i.val input bank) output
        (run (H := H) t (cfg (some (.start i)) v bank input [] output)) := by
  by_cases hi : i.val < q
  · let j : Fin q := ⟨i.val, hi⟩
    cases hd : readNat input with
    | none =>
        obtain ⟨t, ht, hp⟩ := header_failure_run (H := H) j bank input output hd
        refine ⟨1 + t, ?_, ?_⟩
        · have hk : 1 ≤ q - i.val := by omega
          nlinarith
        · rw [run_add, run_one, start_step i hi]
          rw [readQueriesFrom, dif_pos hi, hd]
          simp only [Bind.bind, Option.bind, QueriesPost]
          exact hp
    | some pair =>
        obtain ⟨n, rest⟩ := pair
        have he := readNat_sound hd
        let bank' := Function.update bank j (n.bits ++ bank j)
        obtain ⟨t, ht, w, hw⟩ := header_valid_run (H := H) j n bank rest output
        rw [he] at ht hw
        obtain ⟨u, hu, hp⟩ := queries_total_from (H := H) ⟨i.val + 1, by omega⟩ rest bank'
          (none, some true) output
        refine ⟨1 + t + 1 + u, ?_, ?_⟩
        · have hrest : rest.length ≤ input.length := by
            have hh := congrArg List.length he
            simp only [List.length_append] at hh
            omega
          have hbound := Nat.mul_le_mul_left (q - (i.val + 1))
            (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hrest) 4)
          change u ≤ (q - (i.val + 1)) * (2 * rest.length + 4) at hu
          have hidx : q - i.val = q - (i.val + 1) + 1 := by omega
          rw [hidx]
          nlinarith
        · rw [run_add, run_add, run_add]
          simp only [run_one]
          rw [start_step i hi]
          change QueriesPost (readQueriesFrom i.val input bank) output
            (run u (advance (program q H)
              (run t (cfg (some (.header j .scan)) (none, none) bank input [] output))))
          rw [hw, after_success]
          rw [readQueriesFrom, dif_pos hi, hd]
          simp only [Bind.bind, Option.bind]
          exact hp
  · have he : i = Fin.last q := Fin.ext (by change i.val = q; omega)
    refine ⟨0, by omega, ?_⟩
    rw [readQueriesFrom, dif_neg hi]
    simp only [QueriesPost]
    exact ⟨v, by rw [he]; rfl⟩
termination_by q - i.val

theorem table_total_run {q H : ℕ} (bank : Bank q) (input output : List Bool) :
    ∃ t ≤ 2 * H + 2,
      let c := run (H := H) t
        (cfg (some (.table (.read 0))) (none, none) bank input [] output)
      c.l = none ∧ c.stk (.inr 2) = SourceCSPRowMachine.result H input ++ output := by
  by_cases hlen : H ≤ input.length
  · obtain ⟨t, ht, hr⟩ := table_valid_run (H := H) bank
      (input.take H) (input.drop H) output (by simp [hlen])
    simp only [List.take_append_drop] at hr
    refine ⟨t, ht, ?_⟩
    rw [hr]
    simp only [cfg, contents, Sum.elim_inr, show ¬(2 : Fin 3) = 0 by decide,
      show ¬(2 : Fin 3) = 1 by decide, ↓reduceIte, SourceCSPRowMachine.result,
      if_pos hlen, List.cons_append]
    exact ⟨True.intro, True.intro⟩
  · have hs := SourceCSPRowMachine.short_run input (0 : Fin (H + 1))
      (by simp only [Fin.val_zero, Nat.zero_add]; omega) none [] output
    have hh := congrArg (fun c => c.l) hs
    change _ = none at hh
    obtain ⟨t, ht, hr⟩ := BitMachineStackEmbedding.outputs (tableStacks q)
      (contents bank input [] output) (.table : SourceCSPRowMachine.Label H → Label q H)
      (fun b => (none, b)) Prod.snd (fun _ => rfl) none
      (SourceCSPRowMachine.program H) (program q H) (fun _ => rfl)
      (SourceCSPRowMachine.cfg (some (.read 0)) none input [] output) (input.length + 1) hh
    change run t _ = BitMachineStackEmbedding.cfg _ _ _ _ _ (SourceCSPRowMachine.run _ _) at hr
    rw [hs] at hr
    simp only [table_cfg, Option.map_some, Option.map_none] at hr
    refine ⟨t, by omega, ?_⟩
    rw [hr]
    simp only [cfg, contents, Sum.elim_inr, show ¬(2 : Fin 3) = 0 by decide,
      show ¬(2 : Fin 3) = 1 by decide, ↓reduceIte, SourceCSPRowMachine.result,
      if_neg hlen, List.singleton_append]
    exact ⟨True.intro, True.intro⟩

def rowResult (q H : ℕ) (input : List Bool) : List Bool :=
  match readQueriesFrom (q := q) 0 input (fun _ => []) with
  | none => [false]
  | some (_, rest) => SourceCSPRowMachine.result H rest

/-- All-input halting and the literal failure/success output for canonical
query parsing followed by a fixed truth table. No vertex-range claim is made. -/
theorem controller_total (q H : ℕ) (input output : List Bool) :
    ∃ t ≤ q * (2 * input.length + 4) + 2 * H + 3,
      let c := run t (cfg (some (.start 0)) (none, none) (fun _ => []) input [] output)
      c.l = (none : Option (Label q H)) ∧ c.stk (.inr 2) = rowResult q H input ++ output := by
  obtain ⟨t, ht, hp⟩ := queries_total_from (H := H) (0 : Fin (q + 1)) input
    (fun _ => []) (none, none) output
  simp only [Fin.val_zero, Nat.sub_zero] at ht hp
  cases hd : readQueriesFrom (q := q) 0 input (fun _ => []) with
  | none =>
      refine ⟨t, by omega, ?_⟩
      simpa only [QueriesPost, hd, rowResult, List.singleton_append] using hp
  | some pair =>
      obtain ⟨bank, rest⟩ := pair
      simp only [QueriesPost, hd] at hp
      obtain ⟨w, hw⟩ := hp
      obtain ⟨u, hu, hr⟩ := table_total_run (H := H) bank rest output
      refine ⟨t + 1 + u, by omega, ?_⟩
      rw [run_add, run_add, run_one, hw, start_table]
      simpa only [rowResult, hd] using hr

noncomputable def controller (q H : ℕ) : BitMachine.Machine :=
  ofFinite (Sum.inr (0 : Fin 3) : Stack q) (.inr 2) (.start 0 : Label q H)
    ((none, none) : Control) (program q H)

theorem controller_init (q H : ℕ) (input : List Bool) :
    rawInit (Sum.inr (0 : Fin 3) : Stack q) (.start 0 : Label q H)
      ((none, none) : Control) input =
      cfg (some (.start 0)) (none, none) (fun _ => []) input [] [] := by
  unfold rawInit cfg
  congr 1
  funext k
  cases k with
  | inl j => simp [contents]
  | inr j => fin_cases j <;> rfl

theorem controller_outputs (q H : ℕ) (input : List Bool) :
    (controller q H).OutputsWithin input (rowResult q H input)
      (q * (2 * input.length + 4) + 2 * H + 3) := by
  obtain ⟨t, ht, hp⟩ := controller_total q H input []
  apply outputsWithin_of_raw_run (Sum.inr (0 : Fin 3) : Stack q) (.inr 2)
    (.start 0 : Label q H) ((none, none) : Control) (program q H)
    input (rowResult q H input) t _ ht
  · rw [controller_init]
    exact hp.1
  · rw [controller_init]
    simpa only [List.append_nil] using hp.2

theorem controller_polytime (q H : ℕ) : BitMachine.Polytime (rowResult q H) := by
  refine ⟨controller q H, 4 * q + 2 * H + 3, 1, ?_⟩
  intro input
  have h := controller_outputs q H input
  apply BitMachine.outputsWithin_mono (controller q H) h
  simp only [pow_one]
  nlinarith

end EthInapproximability.CurrentPaper.SourceCSPRowController
