import EthInapproximability.CurrentPaper.SourceCSPRowCodecParser
import EthInapproximability.CurrentPaper.SourceCSPHeaderCheck

/-!
# Successful arbitrary CSP header parser retains the literal bank

The all-input row-controller theorem usually exposes only a success bit.
This conditional strengthening follows its actual query and zero-length
table stages to retain the four parsed words and unconsumed suffix. The
condition is the parser's recursive success, not a promised canonical input.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPHeaderRawBank

open Turing BitMachineEncoding SourceCSPRowController
open BitMachineStackEmbedding

theorem parser_success (input : List Bool)
    (bank : Bank 4) (rest : List Bool)
    (hparse : readQueriesFrom (q := 4) 0 input (fun _ => []) =
      some (bank, rest)) :
    ∃ t, t ≤ 4 * (2 * input.length + 4) + 3 ∧
      run (H := 0) t
        (SourceCSPRowController.cfg (some (.start 0)) (none, none)
          (fun _ => []) input [] []) =
      SourceCSPRowController.cfg (H := 0) none (none, none)
        bank rest [] [true] := by
  obtain ⟨tp, htp, hp⟩ :=
    SourceCSPRowController.queries_total_from (H := 0)
      (0 : Fin 5) input (fun _ => []) (none, none) []
  simp only [Fin.val_zero, Nat.sub_zero] at htp hp
  rw [hparse] at hp
  change ∃ w,
    run (H := 0) tp
      (SourceCSPRowController.cfg (some (.start 0)) (none, none)
        (fun _ => []) input [] []) =
    SourceCSPRowController.cfg (some (.start (Fin.last 4)))
      w bank rest [] [] at hp
  obtain ⟨w, hw⟩ := hp
  obtain ⟨tt, htt, ht⟩ :=
    SourceCSPRowController.table_valid_run (H := 0) bank [] rest [] rfl
  refine ⟨tp + 1 + tt, by omega, ?_⟩
  rw [run_add, run_add, run_one, hw, start_table]
  simpa only [List.nil_append] using ht

theorem parser_framed_success (input : List Bool)
    (bank : Bank 4) (rest : List Bool)
    (hparse : readQueriesFrom (q := 4) 0 input (fun _ => []) =
      some (bank, rest)) :
    ∃ t v S, t ≤ 4 * (2 * input.length + 4) + 3 ∧
      SourceCSPHeaderCheck.parserRun t
        (⟨some (.start 0), (none, none),
          SourceCSPHeaderCheck.parserInitial input⟩ :
          TM2.Cfg (fun _ : SourceCSPHeaderCheck.Stack => Bool)
            (SourceCSPRowController.Label 4 0)
            SourceCSPRowController.Control) =
        ⟨none, v, S⟩ ∧
      (∀ j : Fin 4, S (.inl (.inl j)) = bank j) ∧
      S (.inl (.inr 0)) = rest ∧
      S (.inl (.inr 2)) = [true] ∧
      S (.inr 0) = [] := by
  obtain ⟨tp, htp, hrp⟩ := parser_success input bank rest hparse
  let before := SourceCSPHeaderCheck.parserInitial input
  let localCfg : SourceCSPHeaderParse.Config :=
    SourceCSPRowController.cfg (H := 0) (some (.start 0)) (none, none)
      (fun _ => []) input [] []
  have hhalt : ((run (H := 0) tp localCfg).l) = none := by
    rw [hrp]
    rfl
  obtain ⟨t, ht, hrun⟩ := outputs
    SourceCSPHeaderCheck.parserEmbedding before id id id
    (fun _ => rfl) none (SourceCSPRowController.program 4 0)
    SourceCSPHeaderCheck.parserProgram (fun _ => rfl)
    localCfg tp hhalt
  have hstart : BitMachineStackEmbedding.cfg
      SourceCSPHeaderCheck.parserEmbedding before id id none localCfg =
      (⟨some (.start 0), (none, none), before⟩ :
        TM2.Cfg (fun _ : SourceCSPHeaderCheck.Stack => Bool)
          (SourceCSPRowController.Label 4 0)
          SourceCSPRowController.Control) := by
    simp only [BitMachineStackEmbedding.cfg, stackCfg, BitMachineInline.cfg,
      localCfg, id_eq, SourceCSPRowController.cfg]
    congr 1
    apply bank_eq_self
    intro k
    cases k with
    | inl j => rfl
    | inr j => fin_cases j <;> rfl
  change ((advance (SourceCSPRowController.program 4 0))^[tp])
    localCfg = _ at hrp
  rw [hrp, hstart] at hrun
  let S := BitMachineStackEmbedding.bank
    SourceCSPHeaderCheck.parserEmbedding before
    (SourceCSPRowController.contents bank rest [] [true])
  refine ⟨t, (none, none), S, ht.trans htp, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [SourceCSPHeaderCheck.parserRun, S,
      BitMachineStackEmbedding.cfg, stackCfg,
      BitMachineInline.cfg, SourceCSPRowController.cfg,
      id_eq, Option.map_none] using hrun
  · intro j
    change BitMachineStackEmbedding.bank
      SourceCSPHeaderCheck.parserEmbedding before _
        (SourceCSPHeaderCheck.parserEmbedding (.inl j)) = _
    rw [bank_at]
    rfl
  · change BitMachineStackEmbedding.bank
      SourceCSPHeaderCheck.parserEmbedding before _
        (SourceCSPHeaderCheck.parserEmbedding (.inr 0)) = _
    rw [bank_at]
    rfl
  · change BitMachineStackEmbedding.bank
      SourceCSPHeaderCheck.parserEmbedding before _
        (SourceCSPHeaderCheck.parserEmbedding (.inr 2)) = _
    rw [bank_at]
    rfl
  · apply bank_outside
    rintro ⟨j, hj⟩
    cases hj

end EthInapproximability.CurrentPaper.SourceCSPHeaderRawBank
