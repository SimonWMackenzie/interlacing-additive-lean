import EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalRowSuccess

/-!
# All-input query validation with preserved row-parser fields

The query-range checker uses only its selected shared-bank cells. The parser
failure/success marker and the unread source suffix are outside that embedding
and remain literally unchanged, including for malformed query words.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalQuery

open Turing BitMachineEncoding BitMachineStackEmbedding SourceCSPRowQueryFrame

theorem query_run_preserved {q : Nat} (query : Fin q → List Bool)
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
      S (.inr 0) = source ∧ S (.inr 2) = output ∧
      (b = true ↔ ∀ j : Fin q,
        EncodedCommunication.bitsValue (query j) ≤ cap.length) := by
  let before := parsed (initial input cap) query source saved output
  let localCfg : SourceCSPQueryBank.Config q :=
    ⟨some (.start 0), (((none, none), (none, false)), none), checked before⟩
  obtain ⟨t, v, T, b, ht, hr, hstatus, hb⟩ :=
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
  refine ⟨u, v, bank queryEmbedding before T, b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Fin.val_zero, Nat.sub_zero] using hu.trans ht
  · simpa only [queryRun, BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg] using hrun
  · change bank queryEmbedding before T (queryEmbedding (.inr 1)) = _
    rw [bank_at]
    exact hstatus
  · have hout : ¬ ∃ k, queryEmbedding k = (Sum.inr (0 : Fin 5) : Stack q) := by
      rintro ⟨k, hk⟩
      cases k with
      | inl p => cases hk
      | inr j => fin_cases j <;> simp [queryEmbedding] at hk
    rw [bank_outside _ _ _ _ hout]
    change before (.inr 0) = source
    change (parsed (initial input cap) query source saved output) (.inr 0) = source
    change (bank rowEmbedding (initial input cap)
      (SourceCSPRowController.contents query source saved output))
      (rowEmbedding (.inr 0)) = source
    rw [bank_at]
    rfl
  · have hout : ¬ ∃ k, queryEmbedding k = (Sum.inr (2 : Fin 5) : Stack q) := by
      rintro ⟨k, hk⟩
      cases k with
      | inl p => cases hk
      | inr j => fin_cases j <;> simp [queryEmbedding] at hk
    rw [bank_outside _ _ _ _ hout]
    change (parsed (initial input cap) query source saved output) (.inr 2) = output
    change (bank rowEmbedding (initial input cap)
      (SourceCSPRowController.contents query source saved output))
      (rowEmbedding (.inr 2)) = output
    rw [bank_at]
    rfl
  · simpa only [Fin.val_zero, Nat.zero_le, forall_const] using hb

end EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalQuery
