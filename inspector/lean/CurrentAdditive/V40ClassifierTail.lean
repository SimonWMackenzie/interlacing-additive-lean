import Paper2.SelectedTape
import Paper2.A4PairMap
import EthInapproximability.CurrentPaper.BitMachineComposition

noncomputable section
namespace CurrentAdditive.V40ClassifierTail
open Paper2 Turing EthInapproximability.CurrentPaper
open EncodedComplexity

/-- The concrete one-step identity machine supplies the request to the
physical unary counter and tape cutter. -/
def identity : BitMachine.Machine := ComplexityReductionClosure.identityMachine

theorem identity_runs : identity.ComputesWithin id (fun n => 1*(n+1)^0) := by
  intro input
  refine ⟨1,by simp,?_,?_⟩ <;>
    simp [identity,BitMachine.Machine.run,BitMachine.Machine.step,BitMachine.Machine.init,
      ComplexityReductionClosure.identityMachine,TM2.step,TM2.stepAux]

def prefixFn (t : List Bool) (r : Nat) (h : r ≤ t.length) : Fin r → Bool :=
  fun i => (t.take r)[i.val]'(by rw [List.length_take,Nat.min_eq_left h]; exact i.isLt)
theorem prefix_word (t : List Bool) (r : Nat) (h : r ≤ t.length) :
    List.ofFn (prefixFn t r h)=t.take r := by
  apply List.ext_getElem
  · simp [h]
  · intro i hi hj
    simp [prefixFn]

def cutter (C : SelectedTape.Algorithm) : BitMachine.Machine :=
  NPOwner1.Trunc.machine identity C.cR C.dR

def machine (C : SelectedTape.Algorithm) : BitMachine.Machine :=
  BitMachineComposition.composition (cutter C) C.machine

def cap (C : SelectedTape.Algorithm) (N : Nat) : Nat :=
  NPOwner1.Trunc.timeBound C.cR C.dR 1 0 identity.pushBound N+
    2*N+2+C.cT*(N+1)^C.dT

theorem cap_poly (C : SelectedTape.Algorithm) :
    Paper2.Unit4Shell.Poly.PolyIn id (cap C) := by
  unfold cap NPOwner1.Trunc.timeBound
  repeat (first
    | exact Paper2.Unit4Shell.Poly.self
    | exact Paper2.Unit4Shell.Poly.const _
    | apply Paper2.Unit4Shell.Poly.add
    | apply Paper2.Unit4Shell.Poly.mul
    | apply Paper2.Unit4Shell.Poly.pow)

/-- Every sufficiently long independent block is physically cut to the
classifier's exact request-dependent tape length before that machine runs. -/
theorem outputs (C : SelectedTape.Algorithm) (x t : List Bool)
    (ht : C.tapeLength x ≤ t.length) :
    (machine C).OutputsWithin (pair x t)
      (C.output x (t.take (C.tapeLength x))) (cap C (pair x t).length) := by
  have hcut := NPOwner1.Trunc.machine_outputs identity C.cR C.dR id 1 0 identity_runs
    (pair x t)
  rw [NPOwner1.Trunc.result_pair] at hcut
  have hprefix := prefix_word t (C.tapeLength x) ht
  have hrun : C.machine.OutputsWithin (pair x (t.take (C.tapeLength x)))
      (C.output x (t.take (C.tapeLength x))) (C.cT*(x.length+1)^C.dT) := by
    rw [← hprefix]
    exact C.runs x (prefixFn t (C.tapeLength x) ht)
  have h := BitMachineComposition.composition_outputsWithin _ _ hcut hrun
  apply BitMachine.outputsWithin_mono _ h
  have hmiddle : (pair x (t.take (C.tapeLength x))).length ≤ (pair x t).length := by
    simp only [pair_length,List.length_take]
    omega
  have hsource : x.length ≤ (pair x t).length := by rw [pair_length]; omega
  unfold cap
  calc
    _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hmiddle) _) 2) _
    _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_left C.cT (Nat.pow_le_pow_left (by omega) _)) _

/-- The computed output does not depend on any bits after its selected prefix. -/
theorem output_suffix (C : SelectedTape.Algorithm) (x first suffix : List Bool)
    (hf : first.length=C.tapeLength x) :
    C.output x ((first++suffix).take (C.tapeLength x))=C.output x first := by
  rw [← hf,List.take_left]

/-- Preserve the independent classifier block during the actual first-field
request computation, then run the physical request-dependent cutter and classifier. -/
def after (requester : BitMachine.Machine) (C : SelectedTape.Algorithm) : BitMachine.Machine :=
  BitMachineComposition.composition (Unit4Shell.PairMap.machine requester) (machine C)

def afterClock (C : SelectedTape.Algorithm) (input request tape : List Bool) (T : Nat) :=
  2*input.length+T+2*request.length+6+2*(pair request tape).length+2+
    cap C (pair request tape).length

theorem outputs_after (requester : BitMachine.Machine) (C : SelectedTape.Algorithm)
    (input request tape : List Bool) (T : Nat)
    (hr : requester.OutputsWithin input request T)
    (ht : C.tapeLength request ≤ tape.length) :
    (after requester C).OutputsWithin (pair input tape)
      (C.output request (tape.take (C.tapeLength request)))
      (afterClock C input request tape T) := by
  exact BitMachineComposition.composition_outputsWithin _ _
    (Unit4Shell.PairMap.machine_outputs requester input request tape T hr)
    (outputs C request tape ht)

#print axioms identity_runs
#print axioms outputs
#print axioms cap_poly
#print axioms outputs_after
end CurrentAdditive.V40ClassifierTail
