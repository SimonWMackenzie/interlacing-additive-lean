import EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalRow

/-!
# Range-checking any physically parsed row bank

The row parser may have failed. Its output marker is preserved while the
range checker halts on the shared query bank, so the enclosing total
controller can test that marker rather than losing it during reset.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalRawQuery

open Turing BitMachineEncoding BitMachineStackEmbedding SourceCSPRowQueryFrame

theorem raw_ready {q : Nat} (S : Stack q → List Bool) (cap : List Bool)
    (hcap : S (.inr 3) = cap) (hstatus : S (.inr 4) = [])
    (hwork : ∀ j : Fin q, ∀ k : Fin 5, k ≠ 0 → S (.inl (j, k)) = []) :
    SourceCSPQueryBank.RawReady
      (fun j => S (.inl (j, 0))) cap 0 (checked S) := by
  refine ⟨hcap, hstatus, ?_, ?_⟩
  · intro j; rfl
  · intro j hj
    exact ⟨hwork j 1 (by decide), hwork j 2 (by decide),
      hwork j 3 (by decide), hwork j 4 (by decide)⟩

theorem query_total {q : Nat} (S : Stack q → List Bool)
    (cap : List Bool) (L : Nat)
    (hcap : S (.inr 3) = cap) (hstatus : S (.inr 4) = [])
    (hwork : ∀ j : Fin q, ∀ k : Fin 5, k ≠ 0 → S (.inl (j, k)) = [])
    (hword : ∀ j : Fin q, (S (.inl (j, 0))).length ≤ L)
    (hcapLength : cap.length ≤ L) :
    ∃ t v T b,
      t ≤ q * (100 * (L + 1) ^ 2) + 1 ∧
      queryRun t
        (⟨some (.start 0), (((none, none), (none, false)), none), S⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            (SourceCSPQueryBank.Label q) SourceCSPQueryBank.Control) =
        ⟨none, v, T⟩ ∧
      T (.inr 4) = [b] ∧
      T (.inr 0) = S (.inr 0) ∧
      T (.inr 2) = S (.inr 2) ∧
      (b = true ↔ ∀ j : Fin q,
        EncodedCommunication.bitsValue (S (.inl (j, 0))) ≤ cap.length) := by
  let query : Fin q → List Bool := fun j => S (.inl (j, 0))
  let localCfg : SourceCSPQueryBank.Config q :=
    ⟨some (.start 0), (((none, none), (none, false)), none), checked S⟩
  obtain ⟨t, v, U, b, ht, hr, hs, hb⟩ :=
    SourceCSPQueryBank.raw_total_from query cap L hword hcapLength 0
      (checked S) (raw_ready S cap hcap hstatus hwork) _
  have hhalt : (SourceCSPQueryBank.run t localCfg).l = none := by
    exact hr ▸ rfl
  obtain ⟨u, hu, hrun⟩ := BitMachineStackEmbedding.outputs
    queryEmbedding S id id id (fun _ => rfl) none
    SourceCSPQueryBank.program queryProgram (fun _ => rfl)
    localCfg t hhalt
  have hstart : BitMachineStackEmbedding.cfg queryEmbedding S id id none localCfg =
      (⟨some (.start 0), (((none, none), (none, false)), none), S⟩ :
        TM2.Cfg (fun _ : Stack q => Bool)
          (SourceCSPQueryBank.Label q) SourceCSPQueryBank.Control) := by
    simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, localCfg, id_eq]
    congr 1
    apply bank_eq_self
    intro k
    rfl
  change queryRun u (BitMachineStackEmbedding.cfg queryEmbedding S id id none localCfg) =
    BitMachineStackEmbedding.cfg queryEmbedding S id id none
      (SourceCSPQueryBank.run t localCfg) at hrun
  rw [hr, hstart] at hrun
  refine ⟨u, v, bank queryEmbedding S U, b,
    by simpa only [Fin.val_zero, Nat.sub_zero] using hu.trans ht,
    ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [queryRun, BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg] using hrun
  · change bank queryEmbedding S U (queryEmbedding (.inr 1)) = _
    rw [bank_at]
    exact hs
  · have hout : ¬ ∃ k, queryEmbedding k = (Sum.inr (0 : Fin 5) : Stack q) := by
      rintro ⟨k, hk⟩
      cases k with
      | inl p => cases hk
      | inr j => fin_cases j <;> simp [queryEmbedding] at hk
    exact bank_outside _ _ _ _ hout
  · have hout : ¬ ∃ k, queryEmbedding k = (Sum.inr (2 : Fin 5) : Stack q) := by
      rintro ⟨k, hk⟩
      cases k with
      | inl p => cases hk
      | inr j => fin_cases j <;> simp [queryEmbedding] at hk
    exact bank_outside _ _ _ _ hout
  · simpa only [Fin.val_zero, Nat.zero_le, forall_const, query] using hb

end EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalRawQuery
