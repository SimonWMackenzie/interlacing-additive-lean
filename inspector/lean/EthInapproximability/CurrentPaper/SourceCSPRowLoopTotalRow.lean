import EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalController
import EthInapproximability.CurrentPaper.SourceCSPRowControllerTotal

/-!
# Arbitrary-input row parser on the shared query frame

The source parser's all-input theorem is lifted to the physical shared bank.
Unlike the canonical-row lemma, this statement does not presuppose a decoded
row or a precomputed parser-success flag.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalRow

open Turing BitMachineEncoding BitMachineStackEmbedding

noncomputable def parsedBank {q : Nat} (input cap : List Bool)
    (S : SourceCSPRowController.Stack q → List Bool) :
    SourceCSPRowQueryFrame.Stack q → List Bool :=
  bank SourceCSPRowQueryFrame.rowEmbedding
    (SourceCSPRowQueryFrame.initial input cap) S

theorem parser_total {q H : Nat} (input cap : List Bool) :
    ∃ t v S,
      t ≤ q * (2 * input.length + 4) + 2 * H + 3 ∧
      SourceCSPRowQueryFrame.rowRun (q := q) (H := H) t
        (⟨some (.start 0), (none, none),
          SourceCSPRowQueryFrame.initial input cap⟩ :
          TM2.Cfg (fun _ : SourceCSPRowQueryFrame.Stack q => Bool)
            (SourceCSPRowController.Label q H)
            SourceCSPRowController.Control) =
        ⟨none, v, S⟩ ∧
      S (.inr 2) = SourceCSPRowController.rowResult q H input ∧
      S (.inr 3) = cap ∧ S (.inr 4) = [] ∧
      (∀ j : Fin q, ∀ k : Fin 5, k ≠ 0 → S (.inl (j, k)) = []) := by
  let before := SourceCSPRowQueryFrame.initial (q := q) input cap
  let localStart := SourceCSPRowController.cfg (q := q) (H := H)
    (some (.start (0 : Fin (q + 1)))) (none, none) (fun _ => []) input [] []
  obtain ⟨t, ht, hp⟩ := SourceCSPRowController.controller_total q H input []
  have hhalt : (SourceCSPRowController.run t localStart).l = none := by
    exact hp.1
  obtain ⟨u, hu, hrun⟩ := BitMachineStackEmbedding.outputs
    SourceCSPRowQueryFrame.rowEmbedding before id id id (fun _ => rfl) none
    (SourceCSPRowController.program q H)
    (SourceCSPRowQueryFrame.rowProgram (q := q) (H := H))
    (fun _ => rfl) localStart t hhalt
  let S := parsedBank input cap (SourceCSPRowController.run t localStart).stk
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
  have hstatus : S (.inr 2) = SourceCSPRowController.rowResult q H input := by
    change bank SourceCSPRowQueryFrame.rowEmbedding before
      (SourceCSPRowController.run t localStart).stk
        (SourceCSPRowQueryFrame.rowEmbedding (.inr 2)) = _
    rw [bank_at]
    simpa only [List.append_nil] using hp.2
  have hcap : S (.inr 3) = cap := by
    apply bank_outside
    intro ⟨k, hk⟩
    cases k with
    | inl j => cases hk
    | inr j => fin_cases j <;> simp [SourceCSPRowQueryFrame.rowEmbedding] at hk
  have hqueryStatus : S (.inr 4) = [] := by
    apply bank_outside
    intro ⟨k, hk⟩
    cases k with
    | inl j => cases hk
    | inr j => fin_cases j <;> simp [SourceCSPRowQueryFrame.rowEmbedding] at hk
  have hwork : ∀ j : Fin q, ∀ k : Fin 5, k ≠ 0 → S (.inl (j, k)) = [] := by
    intro j k hk
    apply bank_outside
    intro ⟨r, hr⟩
    cases r with
    | inl u =>
        have hz : (0 : Fin 5) = k := congrArg Prod.snd (Sum.inl.inj hr)
        exact hk hz.symm
    | inr u => cases hr
  refine ⟨u, (SourceCSPRowController.run t localStart).var, S,
    hu.trans ht, ?_, hstatus, hcap, hqueryStatus, hwork⟩
  change SourceCSPRowQueryFrame.rowRun u
    (BitMachineStackEmbedding.cfg SourceCSPRowQueryFrame.rowEmbedding
      before id id none localStart) = _ at hrun
  rw [hstart] at hrun
  change (((advance (SourceCSPRowController.program q H))^[t] localStart).l) = none
    at hhalt
  simpa only [SourceCSPRowQueryFrame.rowRun, S, parsedBank, before,
    BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, id_eq, hhalt, Option.map_none,
    SourceCSPRowController.run] using hrun

end EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalRow
