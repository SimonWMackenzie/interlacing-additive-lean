import CurrentAdditive.D22PostSearchPacket
import CurrentAdditive.PhysicalConcatLocal
import EthInapproximability.CurrentPaper.SourceFieldWriter

/-! Existing physical word extraction/framing/concatenation are used here
with explicit local clocks. Arithmetic is called only after the three raw
unary fields have actually been encoded as its ordinary input. -/
namespace D22PacketPrimitives
open EthInapproximability.CurrentPaper BitMachineComposition
open CurrentAdditive
open D22PolynomialExpression
abbrev Producer := PhysicalConcatLocal.Producer
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

def project {q : ℕ} (j : Fin q) : Producer :=
  ⟨BankFieldProjection.machine j,BankFieldProjection.result j,fun x => (2*q+4)*(x.length+1)⟩
def frame (A : Producer) : Producer :=
  ⟨composition A.machine SourceFieldWriter.fieldMachine,
    fun x => EncodedCommunication.field (A.result x),
    fun x => A.clock x+6*(A.result x).length+6⟩
def append (A B : Producer) : Producer :=
  ⟨PhysicalConcatLocal.machine (A:=A) (B:=B),fun x => A.result x++B.result x,
    PhysicalConcatLocal.clock (A:=A) (B:=B)⟩
theorem project_outputs {q : ℕ} (j : Fin q) (x : List Bool) :
    (project j).machine.OutputsWithin x ((project j).result x) ((project j).clock x) :=
  BankFieldProjection.outputs j x
theorem frame_outputs (A : Producer) (x : List Bool)
    (h : A.machine.OutputsWithin x (A.result x) (A.clock x)) :
    (frame A).machine.OutputsWithin x ((frame A).result x) ((frame A).clock x) := by
  have hh := composition_outputsWithin A.machine SourceFieldWriter.fieldMachine h
    (SourceFieldWriter.field_outputs (A.result x))
  apply BitMachine.outputsWithin_mono _ hh
  dsimp only [frame]
  omega
theorem append_outputs (A B : Producer) (x : List Bool)
    (ha : A.machine.OutputsWithin x (A.result x) (A.clock x))
    (hb : B.machine.OutputsWithin x (B.result x) (B.clock x)) :
    (append A B).machine.OutputsWithin x ((append A B).result x) ((append A B).clock x) :=
  PhysicalConcatLocal.outputs x (hA:=ha) (hB:=hb)

def framer {q : ℕ} (a b c : Fin q) : Producer :=
  append (frame (project a)) (append (frame (project b)) (frame (project c)))
theorem framer_outputs {q : ℕ} (a b c : Fin q) (x : List Bool) :
    (framer a b c).machine.OutputsWithin x ((framer a b c).result x) ((framer a b c).clock x) :=
  append_outputs _ _ x (frame_outputs _ x (project_outputs a x))
    (append_outputs _ _ x (frame_outputs _ x (project_outputs b x)) (frame_outputs _ x (project_outputs c x)))
theorem framer_result {q : ℕ} (a b c : Fin q) (x : List Bool) (n m L : ℕ)
    (ha : BankFieldProjection.result a x=List.replicate n true)
    (hb : BankFieldProjection.result b x=List.replicate m true)
    (hc : BankFieldProjection.result c x=List.replicate L true) :
    (framer a b c).result x=D22NatExpression.input n m L := by
  simp only [framer,append,frame,project,ha,hb,hc]
  simp [D22NatExpression.input,D22NatExpression.values,BitMachineBankCodec.encode_eq_list,
    List.ofFn_succ,List.append_assoc]
theorem framer_clock {q : ℕ} (a b c : Fin q) (x : List Bool) :
    (framer a b c).clock x≤100*(q+1)*(x.length+1) := by
  have ha := BankFieldProjection.result_length a x
  have hb := BankFieldProjection.result_length b x
  have hc := BankFieldProjection.result_length c x
  simp only [framer,append,PhysicalConcatLocal.clock,frame,project,List.length_append,
    EncodedCommunication.field_length]
  nlinarith
theorem framer_length {q : ℕ} (a b c : Fin q) (x : List Bool) :
    ((framer a b c).result x).length≤9*(x.length+1) := by
  have ha := BankFieldProjection.result_length a x
  have hb := BankFieldProjection.result_length b x
  have hc := BankFieldProjection.result_length c x
  simp only [framer,append,frame,project,List.length_append,EncodedCommunication.field_length]
  omega

def scalar {q : ℕ} (a b c : Fin q) (t : Term) : Producer :=
  let F := framer a b c
  ⟨composition F.machine t.expr.machine,
    fun x => List.replicate (t.eval (BankFieldProjection.result a x).length
      (BankFieldProjection.result b x).length (BankFieldProjection.result c x).length) true,
    fun x => F.clock x+2*(F.result x).length+2+t.expr.clock
      (BankFieldProjection.result a x).length (BankFieldProjection.result b x).length
      (BankFieldProjection.result c x).length⟩
theorem scalar_outputs {q : ℕ} (a b c : Fin q) (t : Term) (x : List Bool) (n m L : ℕ)
    (ha : BankFieldProjection.result a x=List.replicate n true)
    (hb : BankFieldProjection.result b x=List.replicate m true)
    (hc : BankFieldProjection.result c x=List.replicate L true) :
    (scalar a b c t).machine.OutputsWithin x ((scalar a b c t).result x) ((scalar a b c t).clock x) := by
  have hF := framer_outputs a b c x
  have h := t.expr.outputs n m L
  rw [←framer_result a b c x n m L ha hb hc] at h
  have hcomp := composition_outputsWithin (framer a b c).machine t.expr.machine hF h
  simpa only [scalar,ha,hb,hc,List.length_replicate,Term.eval] using hcomp

/-- Generic physical three-field adapter. Its execution premise is a local
implementation interface to be discharged by the concrete callback theorem. -/
def invoke {q : ℕ} (a b c : Fin q) (M : BitMachine.Machine)
    (result : ℕ → ℕ → ℕ → List Bool) (clock : ℕ → ℕ → ℕ → ℕ) : Producer :=
  let F := framer a b c
  ⟨composition F.machine M,
    fun x => result (BankFieldProjection.result a x).length (BankFieldProjection.result b x).length
      (BankFieldProjection.result c x).length,
    fun x => F.clock x+2*(F.result x).length+2+clock
      (BankFieldProjection.result a x).length (BankFieldProjection.result b x).length
      (BankFieldProjection.result c x).length⟩
theorem invoke_outputs {q : ℕ} (a b c : Fin q) (M : BitMachine.Machine)
    (result : ℕ → ℕ → ℕ → List Bool) (clock : ℕ → ℕ → ℕ → ℕ)
    (x : List Bool) (n m L : ℕ)
    (ha : BankFieldProjection.result a x=List.replicate n true)
    (hb : BankFieldProjection.result b x=List.replicate m true)
    (hc : BankFieldProjection.result c x=List.replicate L true)
    (hM : M.OutputsWithin (D22NatExpression.input n m L) (result n m L) (clock n m L)) :
    (invoke a b c M result clock).machine.OutputsWithin x
      ((invoke a b c M result clock).result x) ((invoke a b c M result clock).clock x) := by
  rw [←framer_result a b c x n m L ha hb hc] at hM
  have h := composition_outputsWithin (framer a b c).machine M (framer_outputs a b c x) hM
  simpa only [invoke,ha,hb,hc,List.length_replicate] using h

#print axioms scalar_outputs
#print axioms invoke_outputs
end
end D22PacketPrimitives
