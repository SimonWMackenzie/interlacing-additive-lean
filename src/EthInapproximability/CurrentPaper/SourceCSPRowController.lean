import EthInapproximability.CurrentPaper.SourceCSPRowMachine
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
# A finite-bank controller for one literal constraint row

Source: frozen v8 `06-eth.tex`, `thm:paper-sparse-gap-source`, explicit
Boolean-source construction. Canonical query fields are read by the actual
header subroutine, and the fixed-size truth table by the actual block
subroutine. The vertex-range test is a separate component: this controller
does not yet assert correctness of the full checked CSP decoder.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowController

open Turing TM2.Stmt BitMachineEncoding

abbrev Stack (q : ℕ) := Fin q ⊕ Fin 3
abbrev Bank (q : ℕ) := Fin q → List Bool
abbrev Control := ProtocolBinaryHeader.Control

inductive Label (q H : ℕ) where
  | start : Fin (q + 1) → Label q H
  | header : Fin q → ProtocolBinaryHeader.Label → Label q H
  | after : Fin q → Label q H
  | table : SourceCSPRowMachine.Label H → Label q H
  deriving DecidableEq, Fintype

def fieldStacks {q : ℕ} (i : Fin q) : Fin 3 ↪ Stack q where
  toFun k := if k = 0 then .inr 0 else if k = 1 then .inr 1 else .inl i
  inj' := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all

def tableStacks (q : ℕ) : Fin 3 ↪ Stack q := ⟨Sum.inr, Sum.inr_injective⟩

def program (q H : ℕ) : Label q H → TM2.Stmt (fun _ : Stack q => Bool) (Label q H) Control
  | .start i =>
      if h : i.val < q then
        load (fun _ => (none, none)) (goto (fun _ => .header ⟨i.val, h⟩ .scan))
      else load (fun _ => (none, none)) (goto (fun _ => .table (.read 0)))
  | .header i l => BitMachineStackEmbedding.stmt (fieldStacks i)
      (.header i) id id (some (.after i)) (ProtocolBinaryHeader.program l)
  | .after i =>
      pop (.inl i) (fun _ b => (none, b))
        (branch (fun v => v.2.getD false)
          (goto (fun _ => .start ⟨i.val + 1, by omega⟩))
          (push (.inr 2) (fun _ => false) halt))
  | .table l => BitMachineStackEmbedding.stmt (tableStacks q)
      .table (fun b => (none, b)) Prod.snd none (SourceCSPRowMachine.program H l)

def contents {q : ℕ} (bank : Bank q) (source saved output : List Bool) : Stack q → List Bool :=
  Sum.elim bank (fun k => if k = 0 then source else if k = 1 then saved else output)

def cfg {q H : ℕ} (l : Option (Label q H)) (v : Control)
    (bank : Bank q) (source saved output : List Bool) :
    TM2.Cfg (fun _ : Stack q => Bool) (Label q H) Control :=
  ⟨l, v, contents bank source saved output⟩

def run {q H : ℕ} (t : ℕ)
    (c : TM2.Cfg (fun _ : Stack q => Bool) (Label q H) Control) :=
  ((advance (program q H))^[t]) c

theorem run_add {q H : ℕ} (t u : ℕ)
    (c : TM2.Cfg (fun _ : Stack q => Bool) (Label q H) Control) :
    run (t + u) c = run u (run t c) := by
  simpa only [run, Nat.add_comm] using Function.iterate_add_apply (advance (program q H)) u t c

theorem field_bank {q : ℕ} (i : Fin q) (bank : Bank q)
    (oldSource oldSaved output source saved word : List Bool) :
    BitMachineStackEmbedding.bank (fieldStacks i) (contents bank oldSource oldSaved output)
      (ProtocolBinaryHeader.stackContents source saved word) =
      contents (Function.update bank i word) source saved output := by
  funext k
  cases k with
  | inl j =>
      by_cases hj : j = i
      · subst j
        have h := BitMachineStackEmbedding.bank_at (fieldStacks i)
          (contents bank oldSource oldSaved output)
          (ProtocolBinaryHeader.stackContents source saved word) (2 : Fin 3)
        simpa [fieldStacks, contents, ProtocolBinaryHeader.stackContents] using h
      · have hout : ¬∃ t, fieldStacks i t = Sum.inl j := by
          rintro ⟨t, ht⟩
          fin_cases t <;> simp [fieldStacks, hj, Ne.symm hj] at ht
        rw [BitMachineStackEmbedding.bank_outside _ _ _ _ hout]
        simp [contents, hj]
  | inr j =>
      fin_cases j
      · have h := BitMachineStackEmbedding.bank_at (fieldStacks i)
          (contents bank oldSource oldSaved output)
          (ProtocolBinaryHeader.stackContents source saved word) (0 : Fin 3)
        simpa [fieldStacks, contents, ProtocolBinaryHeader.stackContents] using h
      · have h := BitMachineStackEmbedding.bank_at (fieldStacks i)
          (contents bank oldSource oldSaved output)
          (ProtocolBinaryHeader.stackContents source saved word) (1 : Fin 3)
        simpa [fieldStacks, contents, ProtocolBinaryHeader.stackContents] using h
      · have hout : ¬∃ t, fieldStacks i t = Sum.inr (2 : Fin 3) := by
          rintro ⟨t, ht⟩
          fin_cases t <;> simp [fieldStacks] at ht
        exact BitMachineStackEmbedding.bank_outside _ _ _ _ hout

theorem field_cfg {q H : ℕ} (i : Fin q) (bank : Bank q)
    (oldSource oldSaved output source saved word : List Bool)
    (l : Option ProtocolBinaryHeader.Label) (v : Control) :
    BitMachineStackEmbedding.cfg (fieldStacks i) (contents bank oldSource oldSaved output)
      (.header i) id (some (.after i : Label q H))
      (ProtocolBinaryHeader.cfg l v source saved word) =
      cfg (match l with | none => some (.after i) | some l => some (.header i l)) v
        (Function.update bank i word) source saved output := by
  simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, ProtocolBinaryHeader.cfg, cfg, id_eq, field_bank]
  cases l <;> rfl

theorem start_step {q H : ℕ} (i : Fin (q + 1)) (hi : i.val < q)
    (v : Control) (bank : Bank q) (source saved output : List Bool) :
    advance (program q H) (cfg (some (.start i)) v bank source saved output) =
      cfg (some (.header ⟨i.val, hi⟩ .scan)) (none, none) bank source saved output := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg, hi, ↓reduceDIte, Option.getD_some]

theorem after_success {q H : ℕ} (i : Fin q) (v : Control) (bank : Bank q)
    (source saved output word : List Bool) :
    advance (program q H)
      (cfg (some (.after i)) v (Function.update bank i (true :: word)) source saved output) =
      cfg (some (.start ⟨i.val + 1, by omega⟩)) (none, some true)
        (Function.update bank i word) source saved output := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg, contents, Sum.elim_inl,
    Function.update_self, List.head?, List.tail, Option.getD_some, cond_true]
  congr 1
  funext k
  cases k with
  | inl j =>
      by_cases hj : j = i
      · subst j; simp only [Function.update_self, Sum.elim_inl]
      · have hji : (Sum.inl j : Stack q) ≠ .inl i := fun h => hj (Sum.inl.inj h)
        simp only [Function.update_of_ne hji, Sum.elim_inl, Function.update_of_ne hj]
  | inr j => simp only [Function.update_of_ne Sum.inr_ne_inl, Sum.elim_inr]

theorem header_valid_run {q H : ℕ} (i : Fin q) (n : ℕ) (bank : Bank q)
    (rest output : List Bool) :
    ∃ t ≤ 2 * (EncodedCommunication.natField n ++ rest).length + 2,
      ∃ v, run (H := H) t (cfg (some (.header i .scan)) (none, none) bank
        (EncodedCommunication.natField n ++ rest) [] output) =
        cfg (some (.after i)) v (Function.update bank i (true :: (n.bits ++ bank i)))
          rest [] output := by
  have hh : ProtocolBinaryHeader.readChecked none
      (EncodedCommunication.natField n ++ rest) = some (n.bits, rest) := by
    simp [ProtocolBinaryHeader.readChecked_spec, EncodedCommunication.natField,
      EncodedCommunication.readField_append, ProtocolBinaryHeader.canonicalFrom_none,
      ProtocolBinaryHeader.canonical_of_bits]
  let localStart := ProtocolBinaryHeader.cfg (some .scan) (none, none)
    (EncodedCommunication.natField n ++ rest) [] (bank i)
  obtain ⟨t, ht, hp⟩ := ProtocolBinaryHeader.scan_correct
    (EncodedCommunication.natField n ++ rest) none none [] (bank i)
  simp only [ProtocolBinaryHeader.Post, hh, List.reverse_nil, List.nil_append] at hp
  let terminal := ProtocolBinaryHeader.run t localStart
  have he : terminal = ProtocolBinaryHeader.cfg none terminal.var rest []
      (true :: (n.bits ++ bank i)) := by
    have hl : terminal.l = none := hp.1
    have hs : terminal.stk = ProtocolBinaryHeader.stackContents rest []
        (true :: (n.bits ++ bank i)) := by
      funext k
      fin_cases k
      · exact hp.2.1
      · exact hp.2.2.1
      · exact hp.2.2.2
    change (⟨terminal.l, terminal.var, terminal.stk⟩ :
      TM2.Cfg (fun _ : Fin 3 => Bool) ProtocolBinaryHeader.Label Control) = _
    rw [hl, hs]
    rfl
  obtain ⟨u, hu, hr⟩ := BitMachineStackEmbedding.outputs (fieldStacks i)
    (contents bank (EncodedCommunication.natField n ++ rest) [] output)
    (.header i : ProtocolBinaryHeader.Label → Label q H) id id (fun _ => rfl)
    (some (.after i)) ProtocolBinaryHeader.program (program q H) (fun _ => rfl)
    localStart t hp.1
  refine ⟨u, hu.trans (by simpa using ht), terminal.var, ?_⟩
  change run u _ = _ at hr
  change run u _ = BitMachineStackEmbedding.cfg _ _ _ _ _ terminal at hr
  rw [he] at hr
  simp only [localStart, field_cfg, Function.update_eq_self] at hr
  exact hr

def queriesFrom {q : ℕ} (i : ℕ) (query : Fin q → ℕ) : List Bool :=
  if h : i < q then
    EncodedCommunication.natField (query ⟨i, h⟩) ++ queriesFrom (i + 1) query
  else []
termination_by q - i

theorem run_one {q H : ℕ} (c : TM2.Cfg (fun _ : Stack q => Bool) (Label q H) Control) :
    run 1 c = advance (program q H) c := rfl

/-- All query fields are really parsed and installed in their labelled
bank slots. This statement assumes literal canonical fields, not an oracle
answer from the parser; the field subroutine performs each read. -/
theorem queries_run_from {q H : ℕ} (i : Fin (q + 1)) (query : Fin q → ℕ)
    (bank : Bank q) (v : Control) (rest output : List Bool)
    (hpast : ∀ j, j.val < i.val → bank j = (query j).bits)
    (hfuture : ∀ j, i.val ≤ j.val → bank j = []) :
    ∃ t ≤ (q - i.val) * (2 * (queriesFrom i.val query ++ rest).length + 4),
      ∃ w, run (H := H) t
        (cfg (some (.start i)) v bank (queriesFrom i.val query ++ rest) [] output) =
        cfg (some (.start (Fin.last q))) w (fun j => (query j).bits) rest [] output := by
  by_cases hi : i.val < q
  · let j : Fin q := ⟨i.val, hi⟩
    let bank' := Function.update bank j (query j).bits
    have hb : bank j = [] := hfuture j le_rfl
    obtain ⟨t, ht, w, hw⟩ := header_valid_run (H := H) j (query j) bank
      (queriesFrom (i.val + 1) query ++ rest) output
    simp only [hb, List.append_nil] at hw
    obtain ⟨u, hu, z, hz⟩ := queries_run_from (H := H)
      ⟨i.val + 1, by omega⟩ query bank' (none, some true) rest output (by
        intro k hk
        by_cases he : k = j
        · subst k; exact Function.update_self j (query j).bits bank
        · have hk' : k.val < i.val := by
            have hneq : k.val ≠ i.val := fun h => he (Fin.ext h)
            change k.val < i.val + 1 at hk
            omega
          simpa only [bank', Function.update_of_ne he] using hpast k hk') (by
        intro k hk
        have he : k ≠ j := by
          intro he
          subst k
          change i.val + 1 ≤ i.val at hk
          omega
        simpa only [bank', Function.update_of_ne he] using hfuture k (by
          change i.val + 1 ≤ k.val at hk
          omega))
    refine ⟨1 + t + 1 + u, ?_, z, ?_⟩
    · rw [queriesFrom, dif_pos hi]
      have hlen : (queriesFrom (i.val + 1) query ++ rest).length ≤
          (EncodedCommunication.natField (query j) ++ queriesFrom (i.val + 1) query ++ rest).length := by
        simp only [List.length_append]
        omega
      have hbound := Nat.mul_le_mul_left (q - (i.val + 1))
        (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hlen) 4)
      have hi' : q - i.val = q - (i.val + 1) + 1 := by omega
      change u ≤ (q - (i.val + 1)) *
        (2 * (queriesFrom (i.val + 1) query ++ rest).length + 4) at hu
      simp only [List.length_append] at ht hbound ⊢
      rw [hi']
      dsimp only [j] at ht hbound
      simp only [List.length_append] at hu ht
      nlinarith
    · rw [run_add, run_add, run_add]
      simp only [run_one]
      rw [start_step i hi]
      rw [queriesFrom, dif_pos hi, List.append_assoc]
      change run u (advance (program q H)
        (run t (cfg (some (.header j .scan)) (none, none) bank
          (EncodedCommunication.natField (query j) ++
            (queriesFrom (i.val + 1) query ++ rest)) [] output))) = _
      rw [hw, after_success]
      exact hz
  · have he : i = Fin.last q := Fin.ext (by change i.val = q; omega)
    have hb : bank = fun j => (query j).bits := by
      funext j
      exact hpast j (by omega)
    refine ⟨0, by omega, v, ?_⟩
    rw [queriesFrom, dif_neg hi, List.nil_append, hb, he]
    rfl
termination_by q - i.val

theorem table_bank {q : ℕ} (bank : Bank q) (oldSource oldSaved oldOutput : List Bool)
    (source saved output : List Bool) :
    BitMachineStackEmbedding.bank (tableStacks q) (contents bank oldSource oldSaved oldOutput)
      (SourceCSPRowMachine.contents source saved output) = contents bank source saved output := by
  funext k
  cases k with
  | inl j =>
      exact BitMachineStackEmbedding.bank_outside _ _ _ _ (by
        rintro ⟨t, ht⟩
        cases ht)
  | inr j =>
      exact BitMachineStackEmbedding.bank_at (tableStacks q) _ _ j

theorem table_cfg {q H : ℕ} (bank : Bank q) (oldSource oldSaved oldOutput : List Bool)
    (source saved output : List Bool) (l : Option (SourceCSPRowMachine.Label H))
    (v : SourceCSPRowMachine.Control) :
    BitMachineStackEmbedding.cfg (tableStacks q) (contents bank oldSource oldSaved oldOutput)
      .table (fun b => (none, b)) (none : Option (Label q H))
      (SourceCSPRowMachine.cfg l v source saved output) =
      cfg (l.map .table) (none, v) bank source saved output := by
  simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, SourceCSPRowMachine.cfg, cfg, table_bank]
  cases l <;> rfl

theorem table_valid_run {q H : ℕ} (bank : Bank q) (table rest output : List Bool)
    (ht : table.length = H) :
    ∃ t ≤ 2 * H + 2, run t
      (cfg (some (.table (.read 0))) (none, none) bank (table ++ rest) [] output) =
      cfg (H := H) none (none, none) bank rest [] (true :: (table ++ output)) := by
  have h := SourceCSPRowMachine.table_run H table rest output ht
  have hh := congrArg (fun c => c.l) h
  change _ = none at hh
  obtain ⟨t, htime, hr⟩ := BitMachineStackEmbedding.outputs (tableStacks q)
    (contents bank (table ++ rest) [] output)
    (.table : SourceCSPRowMachine.Label H → Label q H) (fun b => (none, b)) Prod.snd
    (fun _ => rfl) none (SourceCSPRowMachine.program H) (program q H) (fun _ => rfl)
    (SourceCSPRowMachine.cfg (some (.read 0)) none (table ++ rest) [] output) (2 * H + 2) hh
  refine ⟨t, htime, ?_⟩
  change run t _ = _ at hr
  change run t _ = BitMachineStackEmbedding.cfg _ _ _ _ _
    (SourceCSPRowMachine.run (2 * H + 2) _) at hr
  rw [h] at hr
  simpa only [table_cfg, Option.map_some, Option.map_none] using hr

theorem start_table {q H : ℕ} (bank : Bank q) (v : Control)
    (source saved output : List Bool) :
    advance (program q H) (cfg (some (.start (Fin.last q))) v bank source saved output) =
      cfg (some (.table (.read 0))) (none, none) bank source saved output := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg, Fin.val_last,
    lt_self_iff_false, ↓reduceDIte, Option.getD_some]

/-- One concrete controller reads all canonical query words and all truth
bits, preserving the source suffix and the exact separate query bank. -/
theorem row_run (q H : ℕ) (query : Fin q → ℕ) (table rest output : List Bool)
    (ht : table.length = H) :
    ∃ t ≤ q * (2 * (queriesFrom 0 query ++ table ++ rest).length + 4) + 2 * H + 3,
      run t (cfg (some (.start 0)) (none, none) (fun _ => [])
        (queriesFrom 0 query ++ table ++ rest) [] output) =
      cfg (H := H) none (none, none) (fun j => (query j).bits) rest []
        (true :: (table ++ output)) := by
  obtain ⟨t, htime, w, hr⟩ := queries_run_from (H := H) (0 : Fin (q + 1)) query
    (fun _ => []) (none, none) (table ++ rest) output
    (by intro j hj; change j.val < 0 at hj; omega) (by intros; rfl)
  simp only [Fin.val_zero] at hr
  obtain ⟨u, hu, hm⟩ := table_valid_run (fun j => (query j).bits) table rest output ht
  refine ⟨t + 1 + u, ?_, ?_⟩
  · simp only [Fin.val_zero, Nat.sub_zero, ← List.append_assoc] at htime
    omega
  · rw [run_add, run_add, run_one, List.append_assoc, hr, start_table]
    exact hm

theorem queriesFrom_eq_drop {q : ℕ} (i : ℕ) (query : Fin q → ℕ) :
    queriesFrom i query =
      ((List.ofFn fun j => EncodedCommunication.natField (query j)).drop i).flatten := by
  by_cases hi : i < q
  · rw [queriesFrom, dif_pos hi, List.drop_eq_getElem_cons (by simpa using hi), List.flatten_cons]
    congr 1
    · simp
    · exact queriesFrom_eq_drop (i + 1) query
  · rw [queriesFrom, dif_neg hi, List.drop_eq_nil_of_le (by simpa using Nat.le_of_not_gt hi)]
    rfl
termination_by q - i

theorem rowFields_eq {n a q : ℕ} (row : SourceCSPCodec.Row n a q) :
    SourceCSPCodec.rowFields row =
      queriesFrom 0 (fun j => (row.1 j).val) ++ List.ofFn row.2 := by
  rw [queriesFrom_eq_drop]
  simp only [List.drop_zero, SourceCSPCodec.rowFields, SourceCSPCodec.fnFields,
    SourceCSPCodec.ofFn_singleton_flatten]

/-- The actual row in the CSP codec is consumed literally. Query bounds
are supplied by the typed row here, not checked by this theorem's controller. -/
theorem csp_row_run {n a q : ℕ} (row : SourceCSPCodec.Row n a q) (rest output : List Bool) :
    ∃ t ≤ q * (2 * (SourceCSPCodec.rowFields row ++ rest).length + 4) + 2 * a ^ q + 3,
      run t (cfg (some (.start 0)) (none, none) (fun _ => [])
        (SourceCSPCodec.rowFields row ++ rest) [] output) =
      cfg (H := a ^ q) none (none, none) (fun j => (row.1 j).val.bits) rest []
        (true :: (List.ofFn row.2 ++ output)) := by
  rw [rowFields_eq]
  exact row_run q (a ^ q) (fun j => (row.1 j).val) (List.ofFn row.2) rest output List.length_ofFn

end EthInapproximability.CurrentPaper.SourceCSPRowController
