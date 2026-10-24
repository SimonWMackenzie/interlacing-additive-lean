import EthInapproximability.CurrentPaper.SourceCSPRowQueryFrame
import EthInapproximability.CurrentPaper.SourceCSPQueryBankValid

/-!
# Retained unary coordinates after physical row validation

This companion to the reviewed row frame exposes the exact unary coordinates
needed by the subsequent clause writer. It does not change the frozen frame.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowQueryUnary

open Turing BitMachineEncoding BitMachineStackEmbedding

theorem checked_start {q : Nat} (query : Fin q → List Bool)
    (input cap source saved output : List Bool) :
    SourceCSPRowQueryFrame.checked
      (SourceCSPRowQueryFrame.parsed
        (SourceCSPRowQueryFrame.initial input cap)
        query source saved output) =
      SourceCSPQueryBank.startBank query cap := by
  let S := SourceCSPRowQueryFrame.checked
    (SourceCSPRowQueryFrame.parsed
      (SourceCSPRowQueryFrame.initial input cap)
      query source saved output)
  have hready : SourceCSPQueryBank.RawReady query cap 0 S :=
    SourceCSPRowQueryFrame.checker_ready query input cap source saved output
  funext k
  cases k with
  | inl p =>
      obtain ⟨j, r⟩ := p
      fin_cases r
      · exact hready.query_eq j
      · exact (hready.future j (by simp)).1
      · exact (hready.future j (by simp)).2.1
      · exact (hready.future j (by simp)).2.2.1
      · exact (hready.future j (by simp)).2.2.2
  | inr r =>
      fin_cases r
      · exact hready.cap_eq
      · exact hready.status

theorem framed_valid_query {n a q : Nat} (row : SourceCSPCodec.Row n a q)
    (hn : 0 < n) (input source saved output : List Bool) (L : Nat)
    (hword : ∀ j : Fin q, (row.1 j).val.bits.length ≤ L)
    (hcap : n - 1 ≤ L) :
    ∃ t v S, t ≤ q * (100 * (L + 1) ^ 2) + 1 ∧
      SourceCSPRowQueryFrame.queryRun t
        (⟨some (.start 0), (((none, none), (none, false)), none),
          SourceCSPRowQueryFrame.parsed
            (SourceCSPRowQueryFrame.initial input (List.replicate (n - 1) true))
            (fun j => (row.1 j).val.bits) source saved output⟩ :
          TM2.Cfg (fun _ : SourceCSPRowQueryFrame.Stack q => Bool)
            (SourceCSPQueryBank.Label q) SourceCSPQueryBank.Control) =
        ⟨none, v, S⟩ ∧
      S (.inr 4) = [true] ∧
      (∀ j : Fin q, S (.inl (j, 1)) = List.replicate (row.1 j).val true) ∧
      S (.inr 0) = source ∧ S (.inr 2) = output := by
  let before := SourceCSPRowQueryFrame.parsed
    (SourceCSPRowQueryFrame.initial input (List.replicate (n - 1) true))
    (fun j => (row.1 j).val.bits) source saved output
  let localCfg : SourceCSPQueryBank.Config q :=
    ⟨some (.start 0), (((none, none), (none, false)), none),
      SourceCSPQueryBank.startBank (fun j => (row.1 j).val.bits)
        (List.replicate (n - 1) true)⟩
  obtain ⟨t, v, S, ht, hr, hs, hu⟩ :=
    SourceCSPQueryBank.valid_queries_run row hn L hword hcap
  have hhalt : (SourceCSPQueryBank.run t localCfg).l = none := by
    rw [hr]
  obtain ⟨u, huBound, hrun⟩ := outputs SourceCSPRowQueryFrame.queryEmbedding
    before id id id (fun _ => rfl) none
    SourceCSPQueryBank.program SourceCSPRowQueryFrame.queryProgram
    (fun _ => rfl) localCfg t hhalt
  have hstart : cfg SourceCSPRowQueryFrame.queryEmbedding before id id none localCfg =
      (⟨some (.start 0), (((none, none), (none, false)), none), before⟩ :
        TM2.Cfg (fun _ : SourceCSPRowQueryFrame.Stack q => Bool)
          (SourceCSPQueryBank.Label q) SourceCSPQueryBank.Control) := by
    simp only [cfg, stackCfg, BitMachineInline.cfg, localCfg, id_eq]
    congr 1
    apply bank_eq_self
    intro k
    exact (congrFun (checked_start (fun j => (row.1 j).val.bits)
      input (List.replicate (n - 1) true) source saved output) k).symm
  change ((advance SourceCSPQueryBank.program)^[t]) localCfg = _ at hr
  rw [hr, hstart] at hrun
  refine ⟨u, v, bank SourceCSPRowQueryFrame.queryEmbedding before S,
    huBound.trans ht, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [SourceCSPRowQueryFrame.queryRun, cfg, stackCfg,
      BitMachineInline.cfg, id_eq, Option.map_none] using hrun
  · change bank SourceCSPRowQueryFrame.queryEmbedding before S
      (SourceCSPRowQueryFrame.queryEmbedding (.inr 1)) = _
    rw [bank_at]
    exact hs
  · intro j
    change bank SourceCSPRowQueryFrame.queryEmbedding before S
      (SourceCSPRowQueryFrame.queryEmbedding (.inl (j, 1))) = _
    rw [bank_at]
    exact hu j
  · calc
      bank SourceCSPRowQueryFrame.queryEmbedding before S (.inr 0) =
          before (.inr 0) := by
        apply bank_outside
        rintro ⟨k, hk⟩
        cases k with
        | inl p => cases hk
        | inr r => fin_cases r <;> simp [SourceCSPRowQueryFrame.queryEmbedding] at hk
      _ = source := by
        change SourceCSPRowQueryFrame.parsed _ _ _ _ _ (.inr 0) = source
        change bank SourceCSPRowQueryFrame.rowEmbedding _ _
          (SourceCSPRowQueryFrame.rowEmbedding (.inr 0)) = source
        rw [bank_at]
        rfl
  · calc
      bank SourceCSPRowQueryFrame.queryEmbedding before S (.inr 2) =
          before (.inr 2) := by
        apply bank_outside
        rintro ⟨k, hk⟩
        cases k with
        | inl p => cases hk
        | inr r => fin_cases r <;> simp [SourceCSPRowQueryFrame.queryEmbedding] at hk
      _ = output := by
        change SourceCSPRowQueryFrame.parsed _ _ _ _ _ (.inr 2) = output
        change bank SourceCSPRowQueryFrame.rowEmbedding _ _
          (SourceCSPRowQueryFrame.rowEmbedding (.inr 2)) = output
        rw [bank_at]
        rfl

/-- Physical parse-and-check of one canonical row with the exact retained
unary coordinates exposed to a subsequent clause generator. -/
theorem combined_valid_row_unary {n a q : Nat} (row : SourceCSPCodec.Row n a q)
    (hn : 0 < n) (rest : List Bool) (L : Nat)
    (hword : ∀ j : Fin q, (row.1 j).val.bits.length ≤ L)
    (hcap : n - 1 ≤ L) :
    ∃ t c, t ≤ q * (2 * (SourceCSPCodec.rowFields row ++ rest).length + 4) +
        2 * a ^ q + 3 + q * (100 * (L + 1) ^ 2) + 2 ∧
      ((advance (SourceCSPRowQueryFrame.combinedProgram q (a ^ q)))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (.start 0 : SourceCSPRowController.Label q (a ^ q))),
          ((none, none), (((none, none), (none, false)), none)),
          SourceCSPRowQueryFrame.initial (SourceCSPCodec.rowFields row ++ rest)
            (List.replicate (n - 1) true)⟩ :
          TM2.Cfg (fun _ : SourceCSPRowQueryFrame.Stack q => Bool)
            (BitMachineRawSequence.Label
              (SourceCSPRowController.Label q (a ^ q))
              (SourceCSPQueryBank.Label q))
            (SourceCSPRowController.Control × SourceCSPQueryBank.Control)) = c ∧
      c.l = none ∧ c.stk (.inr 4) = [true] ∧
      (∀ j : Fin q, c.stk (.inl (j, 1)) =
        List.replicate (row.1 j).val true) ∧
      c.stk (.inr 0) = rest ∧
      c.stk (.inr 2) = true :: List.ofFn row.2 := by
  let query : Fin q → Nat := fun j => (row.1 j).val
  let table := List.ofFn row.2
  let input := SourceCSPCodec.rowFields row ++ rest
  have hin : SourceCSPRowController.queriesFrom 0 query ++ table ++ rest = input := by
    simp only [input, query, table, SourceCSPRowController.rowFields_eq]
  obtain ⟨tr, htr, hrunr⟩ := SourceCSPRowQueryFrame.parsed_row_run
    query table rest (List.replicate (n - 1) true)
    (show table.length = a ^ q by simp [table])
  rw [hin] at htr hrunr
  let Srow := SourceCSPRowQueryFrame.parsed
    (SourceCSPRowQueryFrame.initial input (List.replicate (n - 1) true))
    (fun j => (query j).bits) rest [] (true :: table)
  have hsame : Srow = SourceCSPRowQueryFrame.parsed
      (SourceCSPRowQueryFrame.initial input (List.replicate (n - 1) true))
      (fun j => (row.1 j).val.bits) rest [] (true :: table) := rfl
  obtain ⟨tq, vq, Sq, htq, hrunq, hstatus, hunary, hsource, houtput⟩ :=
    framed_valid_query row hn input rest [] (true :: table) L hword hcap
  have hr : ((advance (SourceCSPRowQueryFrame.rowProgram (q := q) (H := a ^ q)))^[tr])
      (⟨some (.start 0), (none, none),
        SourceCSPRowQueryFrame.initial input (List.replicate (n - 1) true)⟩ :
        TM2.Cfg (fun _ : SourceCSPRowQueryFrame.Stack q => Bool)
          (SourceCSPRowController.Label q (a ^ q))
          SourceCSPRowController.Control) = ⟨none, (none, none), Srow⟩ := by
    simpa only [SourceCSPRowQueryFrame.rowRun, Srow] using hrunr
  have hq : ((advance (SourceCSPRowQueryFrame.queryProgram (q := q)))^[tq])
      (⟨some (.start 0), (((none, none), (none, false)), none), Srow⟩ :
        TM2.Cfg (fun _ : SourceCSPRowQueryFrame.Stack q => Bool)
          (SourceCSPQueryBank.Label q) SourceCSPQueryBank.Control) =
        ⟨none, vq, Sq⟩ := by
    rw [hsame]
    simpa only [SourceCSPRowQueryFrame.queryRun] using hrunq
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs
    (SourceCSPRowQueryFrame.rowProgram (q := q) (H := a ^ q))
    (SourceCSPRowQueryFrame.queryProgram (q := q))
    (.start 0 : SourceCSPRowController.Label q (a ^ q))
    (.start 0 : SourceCSPQueryBank.Label q)
    ((none, none) : SourceCSPRowController.Control) (none, none)
    ((((none, none), (none, false)), none) : SourceCSPQueryBank.Control) vq
    (SourceCSPRowQueryFrame.initial input (List.replicate (n - 1) true))
    Srow Sq tr tq hr hq
  refine ⟨t, ⟨none, ((none, none), vq), Sq⟩, ?_, ?_, rfl,
    hstatus, hunary, ?_, ?_⟩
  · have hrbound : tr ≤ q * (2 * input.length + 4) + 2 * a ^ q + 3 := by
      simpa only [input] using htr
    dsimp only [input] at hrbound
    omega
  · simpa only [SourceCSPRowQueryFrame.combinedProgram, input] using hrun
  · exact hsource
  · exact houtput

end EthInapproximability.CurrentPaper.SourceCSPRowQueryUnary
