import EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalRow

/-!
# Exact successful arbitrary-row parser bank

When the canonical numeric fields and the fixed truth table are physically
present, the all-input source parser leaves their exact bank and unread suffix.
This is not restricted to a pre-supplied typed CSP row.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalRowSuccess

open Turing BitMachineEncoding BitMachineStackEmbedding

theorem parser_success_local {q H : Nat} (input : List Bool)
    (bank : SourceCSPRowController.Bank q) (rest : List Bool)
    (hparse : SourceCSPRowController.readQueriesFrom (q := q) 0 input
        (fun _ => []) = some (bank, rest))
    (htable : H ≤ rest.length) :
    ∃ t, t ≤ q * (2 * input.length + 4) + 2 * H + 3 ∧
      SourceCSPRowController.run (q := q) (H := H) t
        (SourceCSPRowController.cfg (some (.start 0)) (none, none)
          (fun _ => []) input [] []) =
      SourceCSPRowController.cfg none (none, none) bank
        (rest.drop H) [] (true :: rest.take H) := by
  obtain ⟨t, ht, hp⟩ := SourceCSPRowController.queries_total_from
    (H := H) (0 : Fin (q + 1)) input (fun _ => []) (none, none) []
  simp only [Fin.val_zero, Nat.sub_zero,
    SourceCSPRowController.QueriesPost, hparse] at hp ht
  obtain ⟨w, hrun⟩ := hp
  have hrest : rest.take H ++ rest.drop H = rest := List.take_append_drop H rest
  obtain ⟨u, hu, htableRun⟩ := SourceCSPRowController.table_valid_run
    (q := q) (H := H)
    bank (rest.take H) (rest.drop H) [] (by simp [htable])
  refine ⟨t + 1 + u, by omega, ?_⟩
  rw [SourceCSPRowController.run_add, SourceCSPRowController.run_add,
    SourceCSPRowController.run_one, hrun]
  rw [SourceCSPRowController.start_table]
  simpa only [hrest, List.append_nil] using htableRun

/-- A successful arbitrary row parse on the shared bank exposes the exact
query bits, truth table, and unread suffix without a typed-row premise. -/
theorem parser_success {q H : Nat} (input cap : List Bool)
    (bank : SourceCSPRowController.Bank q) (rest : List Bool)
    (hparse : SourceCSPRowController.readQueriesFrom (q := q) 0 input
        (fun _ => []) = some (bank, rest))
    (htable : H ≤ rest.length) :
    ∃ t,
      t ≤ q * (2 * input.length + 4) + 2 * H + 3 ∧
      SourceCSPRowQueryFrame.rowRun (q := q) (H := H) t
        (⟨some (.start 0), (none, none),
          SourceCSPRowQueryFrame.initial input cap⟩ :
          TM2.Cfg (fun _ : SourceCSPRowQueryFrame.Stack q => Bool)
            (SourceCSPRowController.Label q H)
            SourceCSPRowController.Control) =
        ⟨none, (none, none),
          SourceCSPRowQueryFrame.parsed
            (SourceCSPRowQueryFrame.initial input cap) bank
            (rest.drop H) [] (true :: rest.take H)⟩ := by
  let before := SourceCSPRowQueryFrame.initial (q := q) input cap
  let localStart := SourceCSPRowController.cfg (q := q) (H := H)
    (some (.start (0 : Fin (q + 1)))) (none, none) (fun _ => []) input [] []
  obtain ⟨t, ht, hr⟩ := parser_success_local input bank rest hparse htable
  have hhalt : (SourceCSPRowController.run t localStart).l = none := by
    rw [hr]
    rfl
  obtain ⟨u, hu, hrun⟩ := BitMachineStackEmbedding.outputs
    SourceCSPRowQueryFrame.rowEmbedding before id id id (fun _ => rfl) none
    (SourceCSPRowController.program q H)
    (SourceCSPRowQueryFrame.rowProgram (q := q) (H := H))
    (fun _ => rfl) localStart t hhalt
  have hstart : BitMachineStackEmbedding.cfg
      SourceCSPRowQueryFrame.rowEmbedding before id id none localStart =
      (⟨some (.start 0), (none, none), before⟩ :
        TM2.Cfg (fun _ : SourceCSPRowQueryFrame.Stack q => Bool)
          (SourceCSPRowController.Label q H)
          SourceCSPRowController.Control) := by
    simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, localStart, SourceCSPRowController.cfg, id_eq]
    congr 1
    apply bank_eq_self
    intro k
    cases k with
    | inl j => rfl
    | inr j => fin_cases j <;> rfl
  refine ⟨u, hu.trans ht, ?_⟩
  change SourceCSPRowQueryFrame.rowRun u
    (BitMachineStackEmbedding.cfg SourceCSPRowQueryFrame.rowEmbedding
      before id id none localStart) =
    BitMachineStackEmbedding.cfg SourceCSPRowQueryFrame.rowEmbedding
      before id id none (SourceCSPRowController.run t localStart) at hrun
  rw [hr, hstart] at hrun
  simpa only [SourceCSPRowQueryFrame.rowRun, before,
    SourceCSPRowQueryFrame.parsed,
    BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, SourceCSPRowController.cfg, id_eq,
    Option.map_none] using hrun

end EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalRowSuccess
