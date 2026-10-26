import CurrentAdditive.PhysicalConcatLocal
import CurrentAdditive.PhysicalProducer
import EthInapproximability.CurrentPaper.BitMachineBankCodec

/-! Two fixed ordinary machines run on physical copies of one raw input.
Their answers are framed and serialized as the literal canonical two-field bank.
Only the two child executions on the given input are premises of the run theorem. -/
namespace CurrentAdditive.OrdinaryBankFork

open EthInapproximability.CurrentPaper

noncomputable section

/-- Dummy result and clock fields do not occur in the physical concatenator's
program. They make the compiled machine independent of successful-run witnesses. -/
def branch (F : BitMachine.Machine) : PhysicalConcatLocal.Producer where
  machine := BitMachineComposition.composition F SourceFieldWriter.fieldMachine
  result := fun _ => []
  clock := fun _ => 0

def machine (F G : BitMachine.Machine) : BitMachine.Machine :=
  PhysicalConcatLocal.machine (A := branch F) (B := branch G)

def packet (f g : List Bool) : List Bool :=
  BitMachineBankCodec.encode (![f,g] : Fin 2 → List Bool)

theorem packet_eq (f g : List Bool) :
    packet f g = EncodedCommunication.field f ++ EncodedCommunication.field g := by
  simp [packet, BitMachineBankCodec.encode_eq_list, List.ofFn_succ]

def exactClock (n tf tg u v : Nat) : Nat :=
  2*n+tf+tg+10*u+10*v+25

/-- This cap includes answer lengths through actual physical output growth. -/
def clock (F G : BitMachine.Machine) (n tf tg : Nat) : Nat :=
  22*n+(1+10*F.pushBound)*tf+(1+10*G.pushBound)*tg+25

theorem outputsWithin_exact (F G : BitMachine.Machine)
    {x f g : List Bool} {tf tg : Nat}
    (hF : F.OutputsWithin x f tf) (hG : G.OutputsWithin x g tg) :
    (machine F G).OutputsWithin x (packet f g)
      (exactClock x.length tf tg f.length g.length) := by
  let A : PhysicalConcatLocal.Producer :=
    ⟨BitMachineComposition.composition F SourceFieldWriter.fieldMachine,
      fun _ => EncodedCommunication.field f, fun _ => tf+6*f.length+6⟩
  let B : PhysicalConcatLocal.Producer :=
    ⟨BitMachineComposition.composition G SourceFieldWriter.fieldMachine,
      fun _ => EncodedCommunication.field g, fun _ => tg+6*g.length+6⟩
  have hA : A.machine.OutputsWithin x (A.result x) (A.clock x) := by
    have h := BitMachineComposition.composition_outputsWithin F
      SourceFieldWriter.fieldMachine hF (SourceFieldWriter.field_outputs f)
    convert h using 1 <;> dsimp [A] <;> omega
  have hB : B.machine.OutputsWithin x (B.result x) (B.clock x) := by
    have h := BitMachineComposition.composition_outputsWithin G
      SourceFieldWriter.fieldMachine hG (SourceFieldWriter.field_outputs g)
    convert h using 1 <;> dsimp [B] <;> omega
  have h := PhysicalConcatLocal.outputs (A := A) (B := B) x (hA := hA) (hB := hB)
  have hm : PhysicalConcatLocal.machine (A := A) (B := B) = machine F G := by
    unfold machine branch PhysicalConcatLocal.machine
    congr 1
    funext l
    cases l with
    | inl l => cases l <;> rfl
    | inr l => cases l <;> rfl
  rw [hm] at h
  rw [packet_eq]
  convert h using 1
  dsimp [PhysicalConcatLocal.clock, A, B, exactClock]
  rw [EncodedCommunication.field_length, EncodedCommunication.field_length]
  omega

theorem outputsWithin (F G : BitMachine.Machine)
    {x f g : List Bool} {tf tg : Nat}
    (hF : F.OutputsWithin x f tf) (hG : G.OutputsWithin x g tg) :
    (machine F G).OutputsWithin x (packet f g) (clock F G x.length tf tg) := by
  apply BitMachine.outputsWithin_mono _ (outputsWithin_exact F G hF hG)
  have hf := BitMachine.output_length_bound F hF
  have hg := BitMachine.output_length_bound G hG
  dsimp [exactClock, clock]
  nlinarith

def coefficient (F G : BitMachine.Machine) (a b : Nat) : Nat :=
  47+(1+10*F.pushBound)*a+(1+10*G.pushBound)*b

def degree (d e : Nat) : Nat := d+e+1

theorem clock_le_polynomial (F G : BitMachine.Machine) (n a d b e : Nat) :
    clock F G n (a*(n+1)^d) (b*(n+1)^e) ≤
      coefficient F G a b*(n+1)^degree d e := by
  let p := (n+1)^(d+e+1)
  have hb : 1 ≤ n+1 := by omega
  have hp : 1 ≤ p := Nat.one_le_pow _ _ hb
  have hd : (n+1)^d ≤ p := Nat.pow_le_pow_right hb (by omega)
  have he : (n+1)^e ≤ p := Nat.pow_le_pow_right hb (by omega)
  have hn : n+1 ≤ p := by
    simpa only [pow_one] using Nat.pow_le_pow_right hb (show 1 ≤ d+e+1 by omega)
  have hda := Nat.mul_le_mul_left ((1+10*F.pushBound)*a) hd
  have heb := Nat.mul_le_mul_left ((1+10*G.pushBound)*b) he
  change 22*n+(1+10*F.pushBound)*(a*(n+1)^d)+
    (1+10*G.pushBound)*(b*(n+1)^e)+25 ≤
    (47+(1+10*F.pushBound)*a+(1+10*G.pushBound)*b)*p
  nlinarith

theorem outputs_polynomial (F G : BitMachine.Machine)
    (f g : List Bool → List Bool) (a d b e : Nat)
    (hF : ∀ x, F.OutputsWithin x (f x) (a*(x.length+1)^d))
    (hG : ∀ x, G.OutputsWithin x (g x) (b*(x.length+1)^e)) (x : List Bool) :
    (machine F G).OutputsWithin x (packet (f x) (g x))
      (coefficient F G a b*(x.length+1)^degree d e) := by
  exact BitMachine.outputsWithin_mono _ (outputsWithin F G (hF x) (hG x))
    (clock_le_polynomial F G x.length a d b e)

/-- The accepted producer API can use the same fixed fork machine directly. -/
def producer (A B : PhysicalProducer.Producer) : PhysicalProducer.Producer where
  machine := machine A.machine B.machine
  result := fun x => packet (A.result x) (B.result x)
  coefficient := coefficient A.machine B.machine A.coefficient B.coefficient
  degree := degree A.degree B.degree
  outputs := outputs_polynomial A.machine B.machine A.result B.result
    A.coefficient A.degree B.coefficient B.degree A.outputs B.outputs

theorem polytime (A B : PhysicalProducer.Producer) :
    BitMachine.Polytime (fun x => packet (A.result x) (B.result x)) :=
  (producer A B).polytime

#print axioms outputsWithin_exact
#print axioms outputsWithin
#print axioms clock_le_polynomial
#print axioms outputs_polynomial
#print axioms producer
#print axioms polytime

end
end CurrentAdditive.OrdinaryBankFork
