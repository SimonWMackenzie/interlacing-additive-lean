import EthInapproximability.CurrentPaper.QGraphJoined
import EthInapproximability.CurrentPaper.BitMachineClearBank

/-! Clear every private q-arithmetic and log-controller stack. The graph
decoder bank is deliberately preserved for subsequent source consumers, and
no weighted-writer cell belongs to this cleanup bank. -/

namespace EthInapproximability.CurrentPaper.QCleanup

open Turing BitMachineEncoding
open scoped BigOperators
noncomputable section

abbrev Stack := QProduct.Stack
abbrev ClearIndex := Fin 10 ⊕ QLog.Local
abbrev count := Fintype.card ClearIndex

def embed : ClearIndex ↪ Stack where
  toFun
    | .inl j => QProduct.temp j
    | .inr k => QProduct.log k
  inj' := by
    intro a b h
    rcases a with a | a <;> rcases b with b | b
    · congr 1; exact Sum.inl_injective (Sum.inr_injective h)
    · cases h
    · cases h
    · congr 1; exact Sum.inr_injective (Sum.inr_injective h)

def enumerate : Fin count ≃ ClearIndex := (Fintype.equivFin ClearIndex).symm
def key (i : Fin count) : Stack := embed (enumerate i)

theorem key_injective : Function.Injective key := by
  intro a b h
  exact enumerate.injective (embed.injective h)

abbrev Label := Fin (count+1) ⊕ Unit
abbrev Control := Unit × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def step (k : Fin (count+1)) :
    TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  if h : k.val < count then
    BitMachineClearBank.clearStep (key ⟨k.val,h⟩) (.inl k)
      (.inl ⟨k.val+1,by omega⟩)
  else BitMachineClearBank.finishStep id (.inr ())

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl k => step k
  | .inr () => .halt

def cleared (S : Stack → List Bool) : Stack → List Bool :=
  BitMachineClearBank.cleared key S

def cost (S : Stack → List Bool) : ℕ :=
  (∑ i : Fin count, (S (key i)).length) + count + 2

theorem step_spec (i : Fin count) :
    program (.inl i.castSucc) =
      BitMachineClearBank.clearStep (key i)
        (.inl i.castSucc) (.inl i.succ) := by
  simp only [program,step]
  split_ifs with hi
  · rfl
  · exact (hi i.isLt).elim

theorem finish_spec :
    program (.inl (Fin.last count)) =
      BitMachineClearBank.finishStep id (.inr ()) := by
  simp [program,step]

theorem run (S : Stack → List Bool) :
    ((advance program)^[cost S])
      (⟨some (.inl (0 : Fin (count+1))),((),none),S⟩ : Config) =
      ⟨none,((),none),cleared S⟩ := by
  have hr := BitMachineClearBank.clear_bank_run program id (.inr ())
    count key key_injective (fun i => (.inl i : Label))
    step_spec finish_spec () S
  have hfinal : advance program
      (⟨some (.inr ()),((),none),cleared S⟩ : Config) =
      ⟨none,((),none),cleared S⟩ := rfl
  change ((advance program)^[(∑ i : Fin count, (S (key i)).length) + count + 1])
      (⟨some (.inl (0 : Fin (count+1))),((),none),S⟩ : Config) =
    ⟨some (.inr ()),((),none),cleared S⟩ at hr
  dsimp only [cost]
  rw [show (∑ i : Fin count, (S (key i)).length) + count + 2 =
    ((∑ i : Fin count, (S (key i)).length) + count + 1) + 1 by omega,
    Function.iterate_succ_apply',hr,hfinal]

theorem cleared_private (S : Stack → List Bool) (j : ClearIndex) :
    cleared S (embed j) = [] := by
  let i := enumerate.symm j
  have h : key i = embed j := by simp [key,i]
  rw [← h]
  exact BitMachineClearBank.cleared_bank key S i

theorem cleared_parser_writer (S : Stack → List Bool)
    (j : GraphCountBridge.Stack) :
    cleared S (.inl j) = S (.inl j) := by
  apply BitMachineClearBank.cleared_foreign
  intro i h
  rcases henum : enumerate i with j | k
  · simp [key,embed,henum,QProduct.temp] at h
  · simp [key,embed,henum,QProduct.log] at h

#print axioms run
#print axioms cleared_private
#print axioms cleared_parser_writer

end
end EthInapproximability.CurrentPaper.QCleanup
