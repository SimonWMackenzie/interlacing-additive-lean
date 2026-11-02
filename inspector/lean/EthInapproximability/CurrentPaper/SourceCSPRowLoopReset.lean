import EthInapproximability.CurrentPaper.SourceCSPRowLoopClear
import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-!
# Reinitialising the shared row-query bank

After a row has been exposed to the clause emitter, all query and parser work
cells are cleared. A physical three-stack copy restores the immutable unary
query cap to the shared parser cap cell. The suffix and outer stacks survive.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopReset

open Turing BitMachineEncoding

abbrev Stack (q : Nat) := SourceCSPRowLoopClear.Stack q

def cleared {q : Nat} (S : Stack q → List Bool) : Stack q → List Bool :=
  BitMachineClearBank.cleared (SourceCSPRowLoopClear.scratch q) S

theorem cleared_query {q : Nat} (S : Stack q → List Bool)
    (j : Fin q) (k : Fin 5) : cleared S (.inl (.inl (j, k))) = [] := by
  let i := (SourceCSPRowLoopClear.scratchEquiv q).symm (.inl (j, k))
  have hi : SourceCSPRowLoopClear.scratch q i =
      (.inl (.inl (j, k)) : Stack q) := by
    simp [SourceCSPRowLoopClear.scratch, i, SourceCSPRowLoopClear.scratchSlot]
  rw [← hi]
  exact BitMachineClearBank.cleared_bank _ _ _

theorem cleared_shared {q : Nat} (S : Stack q → List Bool)
    (k : Fin 5) (hk : k ≠ 0) : cleared S (.inl (.inr k)) = [] := by
  let r : Fin 4 := ⟨k.val - 1, by omega⟩
  let i := (SourceCSPRowLoopClear.scratchEquiv q).symm (.inr r)
  have hi : SourceCSPRowLoopClear.scratch q i =
      (.inl (.inr k) : Stack q) := by
    change SourceCSPRowLoopClear.scratchSlot
      ((SourceCSPRowLoopClear.scratchEquiv q)
        ((SourceCSPRowLoopClear.scratchEquiv q).symm (.inr r))) = _
    rw [Equiv.apply_symm_apply]
    change (Sum.inl (Sum.inr (⟨r.val + 1, by omega⟩ : Fin 5)) : Stack q) = _
    congr 2
    apply Fin.ext
    dsimp [r]
    omega
  rw [← hi]
  exact BitMachineClearBank.cleared_bank _ _ _

theorem cleared_source {q : Nat} (S : Stack q → List Bool) :
    cleared S (.inl (.inr 0)) = S (.inl (.inr 0)) := by
  apply BitMachineClearBank.cleared_foreign
  intro i h
  simp only [SourceCSPRowLoopClear.scratch, Function.Embedding.coeFn_mk,
    Function.comp_apply] at h
  cases hx : SourceCSPRowLoopClear.scratchEquiv q i with
  | inl p => simp [hx, SourceCSPRowLoopClear.scratchSlot] at h
  | inr r =>
      simp [hx, SourceCSPRowLoopClear.scratchSlot] at h

theorem cleared_outer {q : Nat} (S : Stack q → List Bool) (k : Fin 4) :
    cleared S (.inr k) = S (.inr k) := by
  apply BitMachineClearBank.cleared_foreign
  intro i h
  simp only [SourceCSPRowLoopClear.scratch, Function.Embedding.coeFn_mk,
    Function.comp_apply] at h
  cases hx : SourceCSPRowLoopClear.scratchEquiv q i with
  | inl p => simp [hx, SourceCSPRowLoopClear.scratchSlot] at h
  | inr r => simp [hx, SourceCSPRowLoopClear.scratchSlot] at h

theorem cleared_initial {q : Nat} (S : Stack q → List Bool) (rest : List Bool)
    (hrest : S (.inl (.inr 0)) = rest) :
    cleared S = Sum.elim (SourceCSPRowQueryFrame.initial rest [])
      (fun k => S (.inr k)) := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inl p => exact (cleared_query S p.1 p.2).trans (by rfl)
      | inr k =>
          fin_cases k
          · simpa [SourceCSPRowQueryFrame.initial] using cleared_source S |>.trans hrest
          all_goals first
            | exact cleared_shared S 1 (by decide)
            | exact cleared_shared S 2 (by decide)
            | exact cleared_shared S 3 (by decide)
            | exact cleared_shared S 4 (by decide)
  | inr k => exact cleared_outer S k

theorem restored_initial {q : Nat} (S : Stack q → List Bool)
    (rest cap : List Bool) (hrest : S (.inl (.inr 0)) = rest) :
    Function.update (cleared S) (.inl (.inr 3)) cap =
      Sum.elim (SourceCSPRowQueryFrame.initial rest cap)
        (fun k => S (.inr k)) := by
  rw [cleared_initial S rest hrest]
  funext k
  cases k with
  | inl k =>
      cases k with
      | inl p => simp [SourceCSPRowQueryFrame.initial]
      | inr k => fin_cases k <;> simp [SourceCSPRowQueryFrame.initial]
  | inr k => simp

def capSlots (q : Nat) : Fin 3 ↪ Stack q :=
  ⟨![.inr 1, .inl (.inr 3), .inr 3], by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp at h ⊢⟩

def copyProgram (q : Nat) (l : BitMachineCopy.Label) :
    TM2.Stmt (fun _ : Stack q => Bool) BitMachineCopy.Label (Option Bool) :=
  BitMachineStackEmbedding.stmt (capSlots q) id id id none
    (BitMachineCopy.program l)

private theorem inlineCfg_id (q : TM2.Cfg (fun _ : Fin 3 => Bool)
    BitMachineCopy.Label (Option Bool)) :
    BitMachineInline.cfg id id none q = q := by
  cases q with
  | mk l v S => cases l <;> rfl

theorem copy_run (q : Nat) (S : Stack q → List Bool) (cap : List Bool)
    (hsource : S (.inr 1) = cap) (htarget : S (.inl (.inr 3)) = [])
    (hscratch : S (.inr 3) = []) :
    ∃ u ≤ 2 * cap.length + 2,
      ((advance (copyProgram q))^[u])
        (⟨some .scan, none, S⟩ : TM2.Cfg (fun _ : Stack q => Bool)
          BitMachineCopy.Label (Option Bool)) =
        ⟨none, none, Function.update S (.inl (.inr 3)) cap⟩ := by
  let ι := capSlots q
  let c := BitMachineCopy.cfg (some .scan) none cap [] []
  have hbank : BitMachineStackEmbedding.bank ι S c.stk = S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    fin_cases k <;> simp [ι, capSlots, c, BitMachineCopy.cfg,
      BitMachineCopy.stackContents, hsource, htarget, hscratch]
  have hr := BitMachineCopy.run_correct none cap []
  have hh : (((advance BitMachineCopy.program)^[2 * cap.length + 2]) c).l = none := by
    change (BitMachineCopy.run (2 * cap.length + 2) c).l = none
    rw [hr]
    rfl
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs ι S
    id id id (by intro v; rfl) none
    BitMachineCopy.program (copyProgram q) (by intro l; rfl)
    c (2 * cap.length + 2) hh
  change ((advance (copyProgram q))^[u])
      (BitMachineStackEmbedding.cfg ι S id id none c) =
      BitMachineStackEmbedding.cfg ι S id id none
        (BitMachineCopy.run (2 * cap.length + 2) c) at he
  rw [hr] at he
  simp only [List.append_nil] at he
  have hf : (BitMachineCopy.cfg none none cap cap []).stk =
      Function.update c.stk 1 cap := by
    funext k
    fin_cases k <;> rfl
  simp only [BitMachineStackEmbedding.cfg, inlineCfg_id] at he
  refine ⟨u, hu, ?_⟩
  simpa only [BitMachineStackEmbedding.stackCfg, hf,
    BitMachineStackEmbedding.bank_update, hbank] using he

abbrev Label (q : Nat) := BitMachineRawSequence.Label
  (SourceCSPRowLoopClear.Label q) BitMachineCopy.Label
abbrev Control := BitMachineRawSequence.Control
  SourceCSPRowLoopClear.Control (Option Bool)

def program (q : Nat) : Label q →
    TM2.Stmt (fun _ : Stack q => Bool) (Label q) Control :=
  BitMachineRawSequence.program (SourceCSPRowLoopClear.program q)
    (copyProgram q) .scan ((), none) none

theorem reset_run (q : Nat) (S : Stack q → List Bool) (rest cap : List Bool)
    (hrest : S (.inl (.inr 0)) = rest) (hcap : S (.inr 1) = cap)
    (hscratch : S (.inr 3) = []) :
    ∃ t ≤ (∑ i : Fin (q * 5 + 4),
        (S (SourceCSPRowLoopClear.scratch q i)).length) +
          (q * 5 + 4) + 2 + (2 * cap.length + 2) + 1,
      ((advance (program q))^[t])
        (⟨some (BitMachineRawSequence.leftLabel 0),
          (((), none), none), S⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) (Label q) Control) =
        ⟨none, (((), none), none),
          Sum.elim (SourceCSPRowQueryFrame.initial rest cap)
            (fun k => S (.inr k))⟩ := by
  have hs := SourceCSPRowLoopClear.run_halt q S
  have hc : cleared S (.inr 1) = cap := (cleared_outer S 1).trans hcap
  have ht : cleared S (.inl (.inr 3)) = [] := cleared_shared S 3 (by decide)
  have hh : cleared S (.inr 3) = [] := (cleared_outer S 3).trans hscratch
  obtain ⟨u, hu, hcopy⟩ := copy_run q (cleared S) cap hc ht hh
  obtain ⟨t, htbound, hrun⟩ := BitMachineRawSequence.runs
    (SourceCSPRowLoopClear.program q) (copyProgram q)
    (0 : SourceCSPRowLoopClear.Label q) .scan
    (((), none) : SourceCSPRowLoopClear.Control) ((), none)
    (none : Option Bool) none S (cleared S)
    (Function.update (cleared S) (.inl (.inr 3)) cap)
    ((∑ i : Fin (q * 5 + 4),
      (S (SourceCSPRowLoopClear.scratch q i)).length) +
      (q * 5 + 4) + 2) u hs hcopy
  refine ⟨t, by omega, ?_⟩
  simpa only [program, restored_initial S rest cap hrest] using hrun

end EthInapproximability.CurrentPaper.SourceCSPRowLoopReset
