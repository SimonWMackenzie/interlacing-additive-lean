import CurrentAdditive.CoordinateClean

namespace CurrentAdditive.FiniteFieldCoordinate

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

def pushBudget {L V : Type*} [Fintype L]
    (P : L → TM2.Stmt (fun _ : Stack => Bool) L V) : ℕ :=
  ∑ l : L, BitMachine.pushBound (P l)

theorem advance_length {L V : Type*} [Fintype L]
    (P : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (c : TM2.Cfg (fun _ : Stack => Bool) L V) (k : Stack) :
    ((advance P c).stk k).length ≤ (c.stk k).length + pushBudget P := by
  rcases c with ⟨l,v,W⟩
  cases l with
  | none => simp [advance, pushBudget]
  | some l =>
      have h := BitMachine.stepAux_length (P l) v W k
      have hb : BitMachine.pushBound (P l) ≤ pushBudget P := by
        unfold pushBudget
        exact Finset.single_le_sum (f := fun j => BitMachine.pushBound (P j))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
      simpa [advance, TM2.step, Option.getD_some] using
        h.trans (Nat.add_le_add_left hb _)

theorem run_length {L V : Type*} [Fintype L]
    (P : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (c : TM2.Cfg (fun _ : Stack => Bool) L V) (k : Stack) (n : ℕ) :
    ((((advance P)^[n]) c).stk k).length ≤
      (c.stk k).length + n * pushBudget P := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hs := advance_length P (((advance P)^[n]) c) k
      simp only [Nat.succ_mul] at ih hs ⊢
      omega

theorem scratchBound_run {L V : Type*} [Fintype L]
    (P : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (c : TM2.Cfg (fun _ : Stack => Bool) L V)
    (n : ℕ) (v' : V) (W : Stack → List Bool)
    (h : ((advance P)^[n]) c = ⟨none, v', W⟩) :
    scratchBound W ≤ scratchBound c.stk + n * pushBudget P := by
  unfold scratchBound
  apply Finset.sup_le
  intro i _
  have hlen := run_length P c (scratchSlots i) n
  rw [h] at hlen
  change (W (scratchSlots i)).length ≤
    (c.stk (scratchSlots i)).length + n * pushBudget P at hlen
  have hinit : (c.stk (scratchSlots i)).length ≤
      Finset.univ.sup (fun j : Fin 32 => (c.stk (scratchSlots j)).length) :=
    Finset.le_sup (s := Finset.univ)
      (f := fun j : Fin 32 => (c.stk (scratchSlots j)).length)
      (Finset.mem_univ i)
  omega

noncomputable def selectorPushBudget : ℕ := pushBudget selectorProgram40
noncomputable def positionPushBudget : ℕ := pushBudget
  (Paper2.YaoPositionFull.program positionSlots)
def widthPushBudget : ℕ := pushBudget widthPush
noncomputable def payloadPushBudget : ℕ := pushBudget payloadProgram40

noncomputable def preclearBound (q H K z g t a vertex α p : ℕ) (body : List Bool)
    (S : Stack → List Bool) : ℕ :=
  scratchBound (staged S) +
  selectorClock q H z g * selectorPushBudget +
  positionClock t a vertex body * positionPushBudget +
  widthPushBudget + payloadClock K α p * payloadPushBudget

end CurrentAdditive.FiniteFieldCoordinate
