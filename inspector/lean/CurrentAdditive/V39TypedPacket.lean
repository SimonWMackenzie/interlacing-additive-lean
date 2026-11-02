import CurrentAdditive.V39WholeBankPacket
import CurrentAdditive.V39ThreePortFrame
import Paper2.HeaderJoin

/-! Three literal input words are physically framed, parsed, executed on a
fixed typed finite bank, serialized, and projected to one chosen output. -/
namespace CurrentAdditive.V39TypedPacket
noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384
open Paper2 Turing EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineStackEmbedding
variable {S L V : Type} [Fintype S] [DecidableEq S] [Fintype L] [Fintype V]
variable (g k tape : S) (hgk : g≠k) (hgt : g≠tape) (hkt : k≠tape)

def number := V39ThreePortFrame.number g k tape hgk hgt hkt
def finiteProgram (P : L → TM2.Stmt (fun _ : S => Bool) L V) :=
  fun l => stackStmt (number g k tape hgk hgt hkt).toEmbedding (P l)

def machine (P : L → TM2.Stmt (fun _ : S => Bool) L V)
    (start : L) (control : V) (output : S) : BitMachine.Machine :=
  BitMachineComposition.composition
    (Unit4Post.Pre.machine (V39ThreePortFrame.workCount g k tape))
    (V39WholeBankPacket.machine (finiteProgram g k tape hgk hgt hkt P) start control
      (number g k tape hgk hgt hkt output))

def framedMachine (P : L → TM2.Stmt (fun _ : S => Bool) L V)
    (start : L) (control : V) (output : S) : BitMachine.Machine :=
  V39WholeBankPacket.machine (finiteProgram g k tape hgk hgt hkt P) start control
    (number g k tape hgk hgt hkt output)

def clock (P : L → TM2.Stmt (fun _ : S => Bool) L V) (inputLength time : Nat) :=
  let a := V39ThreePortFrame.workCount g k tape
  a+1+2*(inputLength+a)+2+
    V39WholeBankPacket.clock (finiteProgram g k tape hgk hgt hkt P) (inputLength+a) time

theorem bank_equiv (W : Fin (V39ThreePortFrame.workCount g k tape+3) → List Bool)
    (F : S → List Bool) :
    bank (number g k tape hgk hgt hkt).toEmbedding W F=
      fun i => F ((number g k tape hgk hgt hkt).symm i) := by
  funext i
  obtain ⟨j,rfl⟩ := (number g k tape hgk hgt hkt).surjective i
  rw [Equiv.symm_apply_apply]
  exact bank_at _ _ _ j

theorem framed_outputs_of_run (P : L → TM2.Stmt (fun _ : S => Bool) L V)
    (start : L) (control : V) (output : S) (A : S → List Bool)
    (t T : Nat) (c : TM2.Cfg (fun _ : S => Bool) L V) (word : List Bool)
    (ht : t≤T) (hr : ((advance P)^[t]) ⟨some start,control,A⟩=c)
    (hh : c.l=none) (ho : c.stk output=word) :
    let e := number g k tape hgk hgt hkt
    let input := BitMachineBankCodec.encode (fun i => A (e.symm i))
    (framedMachine g k tape hgk hgt hkt P start control output).OutputsWithin input word
      (V39WholeBankPacket.clock (finiteProgram g k tape hgk hgt hkt P) input.length T) := by
  intro e input
  let AF := fun i => A (e.symm i)
  let CF := fun i => c.stk (e.symm i)
  have hlift := HeaderJoin.liftG e.toEmbedding P AF A c.stk
    (by intro j; simp [AF]) start control c.var t (by
      rw [hr]
      exact congrArg (fun l => (⟨l,c.var,c.stk⟩ : TM2.Cfg (fun _ : S => Bool) L V)) hh)
  rw [bank_equiv] at hlift
  exact V39WholeBankPacket.outputs_of_run
    (finiteProgram g k tape hgk hgt hkt P) start control (e output) AF t T
    ⟨none,c.var,CF⟩ word ht hlift rfl (by simpa [CF] using ho)

theorem outputs_of_run (P : L → TM2.Stmt (fun _ : S => Bool) L V)
    (start : L) (control : V) (output : S) (gw kw tw : List Bool)
    (t T : Nat) (c : TM2.Cfg (fun _ : S => Bool) L V) (word : List Bool)
    (ht : t≤T) (hr : ((advance P)^[t])
      ⟨some start,control,V39ThreePortFrame.inputBank g k tape gw kw tw⟩=c)
    (hh : c.l=none) (ho : c.stk output=word) :
    (machine g k tape hgk hgt hkt P start control output).OutputsWithin
      (BitMachineBankCodec.encode ![gw,kw,tw]) word
      (clock g k tape hgk hgt hkt P (BitMachineBankCodec.encode ![gw,kw,tw]).length T) := by
  let e := number g k tape hgk hgt hkt
  let A := V39ThreePortFrame.inputBank g k tape gw kw tw
  let AF := fun i => A (e.symm i)
  let CF := fun i => c.stk (e.symm i)
  have hlift := HeaderJoin.liftG e.toEmbedding P AF A c.stk
    (by intro j; simp [AF]) start control c.var t (by
      rw [hr]
      exact congrArg (fun l => (⟨l,c.var,c.stk⟩ : TM2.Cfg (fun _ : S => Bool) L V)) hh)
  rw [bank_equiv] at hlift
  have hw := V39WholeBankPacket.outputs_of_run
    (finiteProgram g k tape hgk hgt hkt P) start control (e output) AF t T
    ⟨none,c.var,CF⟩ word ht hlift rfl (by simpa [CF] using ho)
  have hf := V39ThreePortFrame.frame_outputs g k tape hgk hgt hkt gw kw tw
  change (Unit4Post.Pre.machine (V39ThreePortFrame.workCount g k tape)).OutputsWithin
    (BitMachineBankCodec.encode ![gw,kw,tw]) (BitMachineBankCodec.encode AF)
    (V39ThreePortFrame.workCount g k tape+1) at hf
  have hlen : (BitMachineBankCodec.encode AF).length=
      (BitMachineBankCodec.encode ![gw,kw,tw]).length+V39ThreePortFrame.workCount g k tape := by
    rw [show AF=(fun i => V39ThreePortFrame.inputBank g k tape gw kw tw
      ((V39ThreePortFrame.number g k tape hgk hgt hkt).symm i)) from rfl,
      V39ThreePortFrame.inputBank_widen,Paper2.A3Assembly.Wrap.encode_widen,List.length_append,List.length_replicate]
    omega
  have h := BitMachineComposition.composition_outputsWithin
    (Unit4Post.Pre.machine (V39ThreePortFrame.workCount g k tape))
    (V39WholeBankPacket.machine (finiteProgram g k tape hgk hgt hkt P) start control (e output)) hf hw
  simpa only [machine,clock,hlen] using h

#print axioms bank_equiv
#print axioms framed_outputs_of_run
#print axioms outputs_of_run
end
end CurrentAdditive.V39TypedPacket
