import EthInapproximability.CurrentPaper.BitMachineBankWrapper
import EthInapproximability.CurrentPaper.BankFieldProjection
import EthInapproximability.CurrentPaper.BitMachineComposition
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

/-! A concrete finite-bank run gives a packed-input machine with every
parser, execution, serializer, transfer and final field projection charged.
The finite syntax supplies the uniform stack-growth constant. -/
namespace CurrentAdditive.V39WholeBankPacket
noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
variable {N : Nat} {L V : Type} [Fintype L] [Fintype V]

def machine (P : L → TM2.Stmt (fun _ : Fin N => Bool) L V)
    (start : L) (control : V) (j : Fin N) : BitMachine.Machine :=
  BitMachineComposition.composition (BitMachineBankWrapper.machine P start control)
    (BankFieldProjection.machine j)

def size (P : L → TM2.Stmt (fun _ : Fin N => Bool) L V) (inputLength time : Nat) :=
  2*(N*(inputLength+BitMachineStackGrowth.perStep P*time))+N

def clock (P : L → TM2.Stmt (fun _ : Fin N => Bool) L V) (inputLength time : Nat) :=
  (2*N+1)*(inputLength+1)+time+2*size P inputLength time+4+
    2*size P inputLength time+2+(2*N+4)*(size P inputLength time+1)

theorem output_size (P : L → TM2.Stmt (fun _ : Fin N => Bool) L V)
    (start : L) (control : V) (S : Fin N → List Bool) (t T : Nat)
    (c : TM2.Cfg (fun _ : Fin N => Bool) L V) (ht : t≤T)
    (hr : ((advance P)^[t]) ⟨some start,control,S⟩=c) :
    (BitMachineBankCodec.encode c.stk).length ≤ size P (BitMachineBankCodec.encode S).length T := by
  have hb (j : Fin N) : (c.stk j).length ≤
      (BitMachineBankCodec.encode S).length+BitMachineStackGrowth.perStep P*T := by
    have h := BitMachineStackGrowth.run_growth P ⟨some start,control,S⟩ t j
    rw [hr] at h
    exact h.trans (Nat.add_le_add (BitMachineBankCodec.word_length_le_encode S j)
      (Nat.mul_le_mul_left _ ht))
  rw [BitMachineBankCodec.encode_length]
  unfold size
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_left
  calc
    ∑ j, (c.stk j).length ≤ ∑ _j : Fin N,
        ((BitMachineBankCodec.encode S).length+BitMachineStackGrowth.perStep P*T) :=
      Finset.sum_le_sum (fun j _ => hb j)
    _ = _ := by simp

theorem outputs_of_run (P : L → TM2.Stmt (fun _ : Fin N => Bool) L V)
    (start : L) (control : V) (j : Fin N) (S : Fin N → List Bool)
    (t T : Nat) (c : TM2.Cfg (fun _ : Fin N => Bool) L V) (word : List Bool)
    (ht : t≤T) (hr : ((advance P)^[t]) ⟨some start,control,S⟩=c)
    (hh : c.l=none) (ho : c.stk j=word) :
    (machine P start control j).OutputsWithin (BitMachineBankCodec.encode S) word
      (clock P (BitMachineBankCodec.encode S).length T) := by
  have hs := output_size P start control S t T c ht hr
  have hw := BitMachineBankWrapper.outputs P start control (fun _ => c.stk)
    (BitMachineBankCodec.encode S) T (size P (BitMachineBankCodec.encode S).length T)
    (by
      intro A hA
      have he : A=S := by simpa using hA.symm
      subst A
      exact ⟨t,c,ht,hr,hh,rfl⟩)
    (by intro A hA; exact hs)
  simp only [BitMachineBankWrapper.result,BitMachineBankCodec.decode_encode] at hw
  have hp := BankFieldProjection.outputs j (BitMachineBankCodec.encode c.stk)
  rw [BankFieldProjection.result_encode,ho] at hp
  have h := BitMachineComposition.composition_outputsWithin
    (BitMachineBankWrapper.machine P start control) (BankFieldProjection.machine j) hw hp
  apply BitMachine.outputsWithin_mono _ h
  unfold clock
  gcongr

#print axioms output_size
#print axioms outputs_of_run
end
end CurrentAdditive.V39WholeBankPacket
