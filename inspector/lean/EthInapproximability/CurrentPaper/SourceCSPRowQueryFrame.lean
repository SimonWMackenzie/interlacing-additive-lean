import EthInapproximability.CurrentPaper.SourceCSPRowControllerTotal
import EthInapproximability.CurrentPaper.SourceCSPQueryBankTotal
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-!
# Shared physical bank for a row parser and query-range validator

The parsed binary query at index `j` and the range validator's input at `j`
are the same physical stack. All other work stacks are separate. This is a
framing interface, not yet the controller that dispatches between the two.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowQueryFrame

open BitMachineStackEmbedding
open Turing
open BitMachineEncoding

abbrev Stack (q : Nat) := (Fin q × Fin 5) ⊕ Fin 5

def rowEmbedding {q : Nat} : SourceCSPRowController.Stack q ↪ Stack q where
  toFun
    | .inl j => .inl (j, 0)
    | .inr k => .inr ⟨k.val, by omega⟩
  inj' := by
    intro x y h
    cases x <;> cases y <;> simp_all [Fin.ext_iff]

def queryEmbedding {q : Nat} : SourceCSPQueryBank.Stack q ↪ Stack q where
  toFun
    | .inl p => .inl p
    | .inr k => .inr ⟨k.val + 3, by omega⟩
  inj' := by
    intro x y h
    cases x <;> cases y <;> simp_all [Fin.ext_iff]

def initial {q : Nat} (input cap : List Bool) : Stack q → List Bool :=
  Sum.elim (fun _ => [])
    (fun k => if k = 0 then input else if k = 3 then cap else [])

noncomputable def parsed {q : Nat} (before : Stack q → List Bool)
    (bank : SourceCSPRowController.Bank q)
    (source saved output : List Bool) : Stack q → List Bool :=
  BitMachineStackEmbedding.bank rowEmbedding before
    (SourceCSPRowController.contents bank source saved output)

def checked {q : Nat} (S : Stack q → List Bool) :
    SourceCSPQueryBank.Stack q → List Bool := fun k => S (queryEmbedding k)

theorem row_initial {q : Nat} (input cap : List Bool) :
    (fun k => initial (q := q) input cap (rowEmbedding k)) =
      SourceCSPRowController.contents (fun _ => []) input [] [] := by
  funext k
  cases k with
  | inl j => rfl
  | inr k => fin_cases k <;> rfl

theorem cap_preserved {q : Nat} (before : Stack q → List Bool)
    (bank : SourceCSPRowController.Bank q)
    (source saved output : List Bool) :
    (parsed before bank source saved output) (.inr 3) = before (.inr 3) := by
  apply bank_outside
  intro ⟨k, hk⟩
  cases k with
  | inl j => cases hk
  | inr k => fin_cases k <;> simp [rowEmbedding] at hk

theorem status_preserved {q : Nat} (before : Stack q → List Bool)
    (bank : SourceCSPRowController.Bank q)
    (source saved output : List Bool) :
    (parsed before bank source saved output) (.inr 4) = before (.inr 4) := by
  apply bank_outside
  intro ⟨k, hk⟩
  cases k with
  | inl j => cases hk
  | inr k => fin_cases k <;> simp [rowEmbedding] at hk

theorem parsed_query {q : Nat} (before : Stack q → List Bool)
    (bank : SourceCSPRowController.Bank q)
    (source saved output : List Bool) (j : Fin q) :
    (parsed before bank source saved output) (.inl (j, 0)) = bank j := by
  change BitMachineStackEmbedding.bank rowEmbedding before
    (SourceCSPRowController.contents bank source saved output)
      (rowEmbedding (.inl j)) = _
  rw [bank_at]
  rfl

theorem work_preserved {q : Nat} (before : Stack q → List Bool)
    (bank : SourceCSPRowController.Bank q)
    (source saved output : List Bool) (j : Fin q) (k : Fin 5)
    (hk : k ≠ 0) :
    (parsed before bank source saved output) (.inl (j, k)) =
      before (.inl (j, k)) := by
  apply bank_outside
  intro ⟨r, hr⟩
  cases r with
  | inl u =>
      change (Sum.inl (u, (0 : Fin 5)) : Stack q) = .inl (j, k) at hr
      have hz : (0 : Fin 5) = k := congrArg Prod.snd (Sum.inl.inj hr)
      exact hk hz.symm
  | inr u => cases hr

theorem checker_ready {q : Nat} (query : Fin q → List Bool)
    (input cap source saved output : List Bool) :
    SourceCSPQueryBank.RawReady query cap 0
      (checked (parsed (initial input cap) query source saved output)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (parsed (initial input cap) query source saved output) (.inr 3) = cap
    rw [cap_preserved]
    rfl
  · change (parsed (initial input cap) query source saved output) (.inr 4) = []
    rw [status_preserved]
    rfl
  · intro j
    change (parsed (initial input cap) query source saved output) (.inl (j, 0)) = query j
    exact parsed_query _ _ _ _ _ j
  · intro j hj
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals
      change (parsed (initial input cap) query source saved output) (.inl (j, _)) = []
      rw [work_preserved]
      · rfl
      · decide

def queryProgram {q : Nat} (l : SourceCSPQueryBank.Label q) :
    TM2.Stmt (fun _ : Stack q => Bool) (SourceCSPQueryBank.Label q)
      SourceCSPQueryBank.Control :=
  BitMachineStackEmbedding.stmt queryEmbedding id id id none
    (SourceCSPQueryBank.program l)

def queryRun {q : Nat} (t : Nat)
    (c : TM2.Cfg (fun _ : Stack q => Bool)
      (SourceCSPQueryBank.Label q) SourceCSPQueryBank.Control) :=
  ((advance queryProgram)^[t]) c

def rowProgram {q H : Nat} (l : SourceCSPRowController.Label q H) :
    TM2.Stmt (fun _ : Stack q => Bool) (SourceCSPRowController.Label q H)
      SourceCSPRowController.Control :=
  BitMachineStackEmbedding.stmt rowEmbedding id id id none
    (SourceCSPRowController.program q H l)

def rowRun {q H : Nat} (t : Nat)
    (c : TM2.Cfg (fun _ : Stack q => Bool)
      (SourceCSPRowController.Label q H) SourceCSPRowController.Control) :=
  ((advance rowProgram)^[t]) c

theorem parsed_row_run {q H : Nat} (query : Fin q → Nat)
    (table rest cap : List Bool) (ht : table.length = H) :
    ∃ t, t ≤ q * (2 * (SourceCSPRowController.queriesFrom 0 query ++
          table ++ rest).length + 4) + 2 * H + 3 ∧
      rowRun t (⟨some (.start 0), (none, none),
        initial (SourceCSPRowController.queriesFrom 0 query ++ table ++ rest) cap⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            (SourceCSPRowController.Label q H) SourceCSPRowController.Control) =
        ⟨none, (none, none),
          parsed
            (initial (SourceCSPRowController.queriesFrom 0 query ++ table ++ rest) cap)
            (fun j => (query j).bits) rest [] (true :: table)⟩ := by
  let input := SourceCSPRowController.queriesFrom 0 query ++ table ++ rest
  let before : Stack q → List Bool := initial input cap
  let localCfg : TM2.Cfg (fun _ : SourceCSPRowController.Stack q => Bool)
      (SourceCSPRowController.Label q H) SourceCSPRowController.Control :=
    SourceCSPRowController.cfg (some (.start 0)) (none, none) (fun _ => []) input [] []
  obtain ⟨t, htbound, hr⟩ :=
    SourceCSPRowController.row_run q H query table rest [] ht
  have hhalt : (SourceCSPRowController.run t localCfg).l = none := by
    change (SourceCSPRowController.run t
      (SourceCSPRowController.cfg (some (.start 0)) (none, none)
        (fun _ => []) input [] [])).l = none
    rw [hr]
    rfl
  obtain ⟨u, hu, hrun⟩ := BitMachineStackEmbedding.outputs rowEmbedding before
    id id id (fun _ => rfl) none (SourceCSPRowController.program q H)
    (rowProgram (q := q) (H := H))
    (fun _ => rfl) localCfg t hhalt
  have hstart : BitMachineStackEmbedding.cfg rowEmbedding before id id none localCfg =
      (⟨some (.start 0), (none, none), before⟩ :
        TM2.Cfg (fun _ : Stack q => Bool)
          (SourceCSPRowController.Label q H) SourceCSPRowController.Control) := by
    simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, localCfg, SourceCSPRowController.cfg, id_eq]
    congr 1
    apply bank_eq_self
    intro k
    cases k with
    | inl j => rfl
    | inr k => fin_cases k <;> rfl
  change rowRun u (BitMachineStackEmbedding.cfg rowEmbedding before id id none localCfg) =
    BitMachineStackEmbedding.cfg rowEmbedding before id id none
      (SourceCSPRowController.run t localCfg) at hrun
  rw [hr, hstart] at hrun
  refine ⟨u, hu.trans htbound, ?_⟩
  simpa only [rowRun, before, parsed, List.append_nil, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    SourceCSPRowController.cfg, id_eq, Option.map_none] using hrun

/-- With the parser's words installed on the shared stacks, the embedded
literal query program validates all labels without copying the words. -/
theorem checked_query_run {q : Nat} (query : Fin q → List Bool)
    (input cap source saved output : List Bool) (L : Nat)
    (hword : ∀ j : Fin q, (query j).length ≤ L)
    (hcap : cap.length ≤ L) :
    ∃ t v S b, t ≤ q * (100 * (L + 1) ^ 2) + 1 ∧
      queryRun t
        (⟨some (.start 0), (((none, none), (none, false)), none),
          parsed (initial input cap) query source saved output⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            (SourceCSPQueryBank.Label q) SourceCSPQueryBank.Control) =
        ⟨none, v, S⟩ ∧
      S (.inr 4) = [b] ∧
      (b = true ↔ ∀ j : Fin q,
        EncodedCommunication.bitsValue (query j) ≤ cap.length) := by
  let before := parsed (initial input cap) query source saved output
  let localCfg : SourceCSPQueryBank.Config q :=
    ⟨some (.start 0), (((none, none), (none, false)), none), checked before⟩
  obtain ⟨t, v, S, b, ht, hr, hstatus, hb⟩ :=
    SourceCSPQueryBank.raw_total_from query cap L hword hcap 0
      (checked before) (checker_ready query input cap source saved output) _
  have hlocal : localCfg =
      (⟨some (.start 0), (((none, none), (none, false)), none),
        checked before⟩ : SourceCSPQueryBank.Config q) := rfl
  have hhalt : (SourceCSPQueryBank.run t localCfg).l = none := by
    rw [hlocal, hr]
  obtain ⟨u, hu, hrun⟩ := BitMachineStackEmbedding.outputs
    queryEmbedding before id id id (fun _ => rfl) none
    SourceCSPQueryBank.program queryProgram (fun _ => rfl)
    localCfg t hhalt
  have hstart : BitMachineStackEmbedding.cfg queryEmbedding before id id none localCfg =
      (⟨some (.start 0), (((none, none), (none, false)), none), before⟩ :
        TM2.Cfg (fun _ : Stack q => Bool)
          (SourceCSPQueryBank.Label q) SourceCSPQueryBank.Control) := by
    simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, localCfg, id_eq]
    congr 1
    apply bank_eq_self
    intro k
    rfl
  change queryRun u (BitMachineStackEmbedding.cfg queryEmbedding before id id none localCfg) =
    BitMachineStackEmbedding.cfg queryEmbedding before id id none
      (SourceCSPQueryBank.run t localCfg) at hrun
  rw [hlocal, hr] at hrun
  rw [hstart] at hrun
  refine ⟨u, v, bank queryEmbedding before S, b, ?_, ?_, ?_, ?_⟩
  · simpa only [Fin.val_zero, Nat.sub_zero] using hu.trans ht
  · simpa only [queryRun, BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg] using hrun
  · change bank queryEmbedding before S (queryEmbedding (.inr 1)) = _
    rw [bank_at]
    exact hstatus
  · simpa only [Fin.val_zero, Nat.zero_le, forall_const] using hb

def combinedProgram (q H : Nat) :=
  BitMachineRawSequence.program (rowProgram (q := q) (H := H))
    (queryProgram (q := q)) (.start 0 : SourceCSPQueryBank.Label q)
    ((none, none) : SourceCSPRowController.Control)
    ((((none, none), (none, false)), none) : SourceCSPQueryBank.Control)

/-- A valid canonical row is physically parsed and its labels are physically
range-checked on the same bank. This proves the two-stage run only; it does
not yet emit clauses or serialize a complete CSP. -/
theorem combined_valid_row {n a q : Nat} (row : SourceCSPCodec.Row n a q)
    (hn : 0 < n) (rest : List Bool) (L : Nat)
    (hword : ∀ j : Fin q, ((row.1 j).val.bits).length ≤ L)
    (hcap : n - 1 ≤ L) :
    ∃ t c, t ≤ q * (2 * (SourceCSPCodec.rowFields row ++ rest).length + 4) +
        2 * a ^ q + 3 + q * (100 * (L + 1) ^ 2) + 2 ∧
      ((advance (combinedProgram q (a ^ q)))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (.start 0 : SourceCSPRowController.Label q (a ^ q))),
          ((none, none), (((none, none), (none, false)), none)),
          initial (SourceCSPCodec.rowFields row ++ rest)
            (List.replicate (n - 1) true)⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            (BitMachineRawSequence.Label
              (SourceCSPRowController.Label q (a ^ q))
              (SourceCSPQueryBank.Label q))
            (SourceCSPRowController.Control × SourceCSPQueryBank.Control)) = c ∧
      c.l = none ∧ c.stk (.inr 4) = [true] := by
  let query : Fin q → Nat := fun j => (row.1 j).val
  let table := List.ofFn row.2
  let input := SourceCSPCodec.rowFields row ++ rest
  have hin : SourceCSPRowController.queriesFrom 0 query ++ table ++ rest = input := by
    simp only [input, query, table, SourceCSPRowController.rowFields_eq]
  obtain ⟨tr, htr, hrunr⟩ := parsed_row_run query table rest
    (List.replicate (n - 1) true) (show table.length = a ^ q by simp [table])
  rw [hin] at htr hrunr
  obtain ⟨tq, vq, Sq, b, htq, hrunq, hstatus, hb⟩ :=
    checked_query_run (fun j => (row.1 j).val.bits) input
      (List.replicate (n - 1) true) rest [] (true :: table) L
      hword (by simpa only [List.length_replicate] using hcap)
  have hall : ∀ j : Fin q,
      EncodedCommunication.bitsValue ((row.1 j).val.bits) ≤
        (List.replicate (n - 1) true).length := by
    intro j
    simp only [List.length_replicate, EncodedCommunication.bitsValue_bits]
    omega
  have hbtrue : b = true := hb.mpr hall
  let Srow := parsed (initial input (List.replicate (n - 1) true))
    (fun j => (query j).bits) rest [] (true :: table)
  have hsame : Srow = parsed (initial input (List.replicate (n - 1) true))
      (fun j => (row.1 j).val.bits) rest [] (true :: table) := rfl
  have hr : ((advance (rowProgram (q := q) (H := a ^ q)))^[tr])
      (⟨some (.start 0), (none, none),
        initial input (List.replicate (n - 1) true)⟩ :
        TM2.Cfg (fun _ : Stack q => Bool)
          (SourceCSPRowController.Label q (a ^ q))
          SourceCSPRowController.Control) = ⟨none, (none, none), Srow⟩ := by
    simpa only [rowRun, Srow] using hrunr
  have hq : ((advance (queryProgram (q := q)))^[tq])
      (⟨some (.start 0), (((none, none), (none, false)), none), Srow⟩ :
        TM2.Cfg (fun _ : Stack q => Bool)
          (SourceCSPQueryBank.Label q) SourceCSPQueryBank.Control) =
        ⟨none, vq, Sq⟩ := by
    rw [hsame]
    simpa only [queryRun] using hrunq
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs
    (rowProgram (q := q) (H := a ^ q)) (queryProgram (q := q))
    (.start 0 : SourceCSPRowController.Label q (a ^ q))
    (.start 0 : SourceCSPQueryBank.Label q)
    ((none, none) : SourceCSPRowController.Control) (none, none)
    ((((none, none), (none, false)), none) : SourceCSPQueryBank.Control) vq
    (initial input (List.replicate (n - 1) true)) Srow Sq tr tq hr hq
  refine ⟨t, ⟨none, ((none, none), vq), Sq⟩, ?_, ?_, rfl, ?_⟩
  · have hrbound : tr ≤ q * (2 * input.length + 4) + 2 * a ^ q + 3 := by
      simpa only [input] using htr
    dsimp only [input] at hrbound
    omega
  · simpa only [combinedProgram, input] using hrun
  · change Sq (.inr 4) = [true]
    rw [hstatus, hbtrue]

end EthInapproximability.CurrentPaper.SourceCSPRowQueryFrame
