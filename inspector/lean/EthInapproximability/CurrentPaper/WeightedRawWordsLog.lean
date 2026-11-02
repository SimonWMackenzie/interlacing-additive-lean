import EthInapproximability.CurrentPaper.WeightedRawWordsDepth

/-! # S2b helper: embedded `ETHParameterScaleMachineLogCopy` with output
harvest and a physical clear of its private region

Source cell `w 2` (kept), output copied into `w 3`, all `log` cells cleared.
The log machine's residue is existential; its clear is charged through
`BitMachineStackGrowth.run_growth`. -/

namespace EthInapproximability.CurrentPaper.WeightedRawWords

open Turing BitMachineEncoding BitMachineStackEmbedding

noncomputable section

abbrev LogStack := ETHParameterScaleMachineLogCopy.Stack

def logSource : LogStack := .inl 0

def logSlots : LogStack ↪ Global where
  toFun k := if k = logSource then aux (.w 2) else aux (.log k)
  inj' := by
    intro a b h
    by_cases ha : a = logSource <;> by_cases hb : b = logSource <;>
      simp only [ha, hb, if_true, if_false, aux] at h
    · exact ha.trans hb.symm
    · cases h
    · cases h
    · exact Aux.log.inj (Sum.inr.inj h)

def logProgram := fun l => stackStmt logSlots (ETHParameterScaleMachineLogCopy.program l)

def logOut : LogStack :=
  ETHParameterScaleMachineLogCopy.logStack ETHParameterScaleMachineLogCopy.logMachine.output

theorem logOut_ne : logOut ≠ logSource := by
  simp [logOut, logSource, ETHParameterScaleMachineLogCopy.logStack]

def logBound (m : ℕ) : ℕ :=
  2*m+2 + (UnaryBinaryEncoding.coefficient+6)*(m+1)^2

def logPer : ℕ := BitMachineStackGrowth.perStep ETHParameterScaleMachineLogCopy.program

theorem log_start_stk (q : List Bool) (k : LogStack) :
    (ETHParameterScaleMachineLogCopy.start q).stk k = if k = logSource then q else [] := by
  unfold ETHParameterScaleMachineLogCopy.start
  unfold BitMachineStackEmbedding.cfg
  unfold stackCfg
  dsimp only
  by_cases hr : ∃ i, ETHParameterScaleMachineLogCopy.copyStack i = k
  · obtain ⟨i, rfl⟩ := hr
    rw [bank_at]
    fin_cases i <;>
      simp [ETHParameterScaleMachineLogCopy.copyStack, BitMachineCopy.cfg,
        BitMachineCopy.stackContents, BitMachineInline.cfg, logSource]
  · rw [bank_outside _ _ _ _ hr]
    have hk : k ≠ logSource := by
      rintro rfl
      exact hr ⟨0, rfl⟩
    simp [hk]

theorem log_embedded (m : ℕ) (G : Global → List Bool)
    (hS : G (aux (.w 2)) = List.replicate m true)
    (hL : ∀ k, G (aux (.log k)) = []) :
    ∃ t ≤ logBound m, ∃ (v : ETHParameterScaleMachineLogCopy.Control) (F : LogStack → List Bool),
      ((advance logProgram)^[t])
        (⟨some (.inl .scan), ETHParameterScaleMachineLogCopy.copyControl none, G⟩ :
          TM2.Cfg (fun _ : Global => Bool) ETHParameterScaleMachineLogCopy.Label
            ETHParameterScaleMachineLogCopy.Control) =
        ⟨none, v, bank logSlots G F⟩ ∧
      F logSource = List.replicate m true ∧
      F logOut = List.replicate (Nat.clog 2 m) true ∧
      ∀ k, (F k).length ≤ m + logPer * logBound m := by
  obtain ⟨t, c, ht, hr, hl, ho⟩ := ETHParameterScaleMachineLogCopy.copied_log_run m
  have hr' : ((advance ETHParameterScaleMachineLogCopy.program)^[t])
      (ETHParameterScaleMachineLogCopy.start (List.replicate m true)) =
      ETHParameterScaleMachineLogCopy.afterLog (List.replicate m true) c := hr
  have hlabel : (ETHParameterScaleMachineLogCopy.afterLog (List.replicate m true) c).l = none := by
    simp [ETHParameterScaleMachineLogCopy.afterLog, BitMachineStackEmbedding.cfg,
      stackCfg, BitMachineInline.cfg, hl]
  refine ⟨t, ht, (ETHParameterScaleMachineLogCopy.afterLog (List.replicate m true) c).var,
    (ETHParameterScaleMachineLogCopy.afterLog (List.replicate m true) c).stk, ?_, ?_, ?_, ?_⟩
  · have h := region_run logSlots ETHParameterScaleMachineLogCopy.program _ _ t hr' G
      (by
        intro k
        rw [log_start_stk]
        by_cases hk : k = logSource
        · subst hk; simp [logSlots, hS]
        · simp [logSlots, hk, hL])
    rw [hlabel] at h
    exact h
  · exact ETHParameterScaleMachineLogCopy.afterLog_source m c
  · rw [logOut, ETHParameterScaleMachineLogCopy.afterLog_output]
    exact ho
  · intro k
    have hg := BitMachineStackGrowth.run_growth ETHParameterScaleMachineLogCopy.program
      (ETHParameterScaleMachineLogCopy.start (List.replicate m true)) t k
    rw [hr'] at hg
    have hi : ((ETHParameterScaleMachineLogCopy.start (List.replicate m true)).stk k).length ≤ m := by
      rw [log_start_stk]; split <;> simp
    have hm : logPer * t ≤ logPer * logBound m := Nat.mul_le_mul_left _ ht
    have hg' : ((ETHParameterScaleMachineLogCopy.afterLog (List.replicate m true) c).stk k).length ≤
        ((ETHParameterScaleMachineLogCopy.start (List.replicate m true)).stk k).length +
          logPer * t := hg
    omega

def logCells : Fin (Fintype.card LogStack) → Global :=
  fun i => aux (.log ((Fintype.equivFin LogStack).symm i))

theorem logCells_injective : Function.Injective logCells := by
  intro i j h
  simpa [logCells, aux] using h

def logCard : ℕ := Fintype.card LogStack

def logCopy := copyProg (aux (.log logOut)) (aux (.w 3))
  (by simp [aux]) (by simp [aux]) (by simp [aux])

def logStageProgram :=
  BitMachineRawSequence.program logProgram
    (BitMachineRawSequence.program logCopy (clearProgram logCells) 0 none ((), none))
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (ETHParameterScaleMachineLogCopy.copyControl none) (none, ((), none))

def logStageBound (m : ℕ) : ℕ :=
  logBound m + ((2 * Nat.clog 2 m + 2) + (logCard * (m + logPer * logBound m) + logCard + 2) + 1) + 1

theorem log_stage (m : ℕ) (G : Global → List Bool)
    (hS : G (aux (.w 2)) = List.replicate m true)
    (hL : ∀ k, G (aux (.log k)) = [])
    (h3 : G (aux (.w 3)) = []) (hcs : G (aux .cs) = []) :
    ∃ t ≤ logStageBound m,
      ((advance logStageProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.inl .scan)),
          (ETHParameterScaleMachineLogCopy.copyControl none, (none, ((), none))), G⟩ :
          TM2.Cfg (fun _ : Global => Bool) _ _) =
        ⟨none, (ETHParameterScaleMachineLogCopy.copyControl none, (none, ((), none))),
          Function.update G (aux (.w 3)) (List.replicate (Nat.clog 2 m) true)⟩ := by
  obtain ⟨t1, ht1, v, F, hr1, hsrc, hout, hlen⟩ := log_embedded m G hS hL
  set X := bank logSlots G F with hX
  have hXo : X (aux (.log logOut)) = List.replicate (Nat.clog 2 m) true := by
    have : aux (.log logOut) = logSlots logOut := by simp [logSlots, logOut_ne]
    rw [this, hX, bank_at, hout]
  have hnot : ∀ a : Aux, (∀ k, a ≠ .log k) → a ≠ .w 2 → X (aux a) = G (aux a) := by
    intro a ha h2
    apply bank_outside
    rintro ⟨k, hk⟩
    by_cases h : k = logSource
    · simp [logSlots, h, aux] at hk; exact h2 hk.symm
    · simp [logSlots, h, aux] at hk; exact ha k hk.symm
  have hX3 : X (aux (.w 3)) = [] := by
    rw [hnot _ (by intro k; simp) (by simp)]; exact h3
  have hXcs : X (aux .cs) = [] := by
    rw [hnot _ (by intro k; simp) (by simp)]; exact hcs
  have hc := copy_word (aux (.log logOut)) (aux (.w 3)) (by simp [aux]) (by simp [aux])
    (by simp [aux]) X hX3 hXcs
  rw [hXo] at hc
  set X1 := Function.update X (aux (.w 3)) (List.replicate (Nat.clog 2 m) true) with hX1
  have hcl := clear_run logCells logCells_injective X1
  have hsum : (∑ i, (X1 (logCells i)).length) ≤ logCard * (m + logPer * logBound m) := by
    apply sum_le_mul
    intro i
    have hne : logCells i ≠ aux (.w 3) := by simp [logCells, aux]
    rw [hX1, Function.update_of_ne hne, hX]
    by_cases hr : ∃ k, logSlots k = logCells i
    · obtain ⟨k, hk⟩ := hr
      rw [← hk, bank_at]
      exact hlen k
    · rw [bank_outside logSlots G F _ hr]
      simp [logCells, hL]
  have hfinal : BitMachineClearBank.cleared logCells X1 =
      Function.update G (aux (.w 3)) (List.replicate (Nat.clog 2 m) true) := by
    have hn : ∀ i, logCells i ≠ aux (.w 3) := fun i => by simp [logCells, aux]
    rw [hX1, cleared_update_comm _ _ _ _ hn, hX,
      cleared_bank_eq logCells logSlots G F (fun i => hL _)]
    intro k
    by_cases hk : k = logSource
    · right
      subst hk
      simp [logSlots, hsrc, hS]
    · left
      refine ⟨(Fintype.equivFin LogStack) k, ?_⟩
      simp [logCells, logSlots, hk]
  rw [hfinal] at hcl
  obtain ⟨t2, ht2, h2⟩ := BitMachineRawSequence.runs logCopy (clearProgram logCells)
    BitMachineCopy.Label.scan 0 none none ((), none) ((), none) X X1
    (Function.update G (aux (.w 3)) (List.replicate (Nat.clog 2 m) true)) _ _ hc hcl
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs logProgram _
    (.inl .scan) (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (ETHParameterScaleMachineLogCopy.copyControl none) v
    (none, ((), none)) (none, ((), none)) G X _ t1 t2 hr1 h2
  refine ⟨t, ?_, h⟩
  unfold logStageBound
  simp only [List.length_replicate] at ht2
  unfold logCard at hsum ⊢
  omega

#print axioms log_embedded
#print axioms log_stage

end
end EthInapproximability.CurrentPaper.WeightedRawWords
