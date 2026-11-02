import CurrentV43.Parametric.Carrier

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768
namespace CurrentV43.ParametricSource
noncomputable section
open Paper2 Turing EthInapproximability.CurrentPaper CurrentAdditive
open EncodedETHSource EncodedETHSourceComposition
open Unit4Shell Unit4Shell.T10Finite V42RuntimeSchedule
local instance : DecidableEq V42RawMidpointRequest.Raw := Classical.decEq _

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
local instance sourceNonzero (Φ : ValidFormula) : NeZero (t10Graph D B Φ).vertices :=
  ⟨(t10_vertices_pos D B Φ).ne'⟩

def sampledBits (S : Schedule) (Φ : ValidFormula) (tape : List Bool) :=
  V40SourceBlockView.bits (V42RawSamplerJoin.precision (t10Graph D B Φ).vertices (S.gap Φ.val.variables))
    (V42RawSamplerJoin.reservation (t10Graph D B Φ).vertices (S.gap Φ.val.variables)) tape

def residual (S : Schedule) (Φ : ValidFormula) (tape : List Bool) :=
  tape.drop (V42RawSamplerJoin.precision (t10Graph D B Φ).vertices (S.gap Φ.val.variables)*
    V42RawSamplerJoin.reservation (t10Graph D B Φ).vertices (S.gap Φ.val.variables))

def request (S : Schedule) (Φ : ValidFormula) (cc δv ζ : ℚ)
    (ht : FullTests cc (Nat.clog 2 (t10Graph D B Φ).vertices) (t10Graph D B Φ).edges.length δv ζ)
    (tape : List Bool) :=
  V42RawRequestPacket.request (t10Graph D B Φ) (t10Graph_valid D B Φ) (S.gap Φ.val.variables)
    cc δv ζ ht (sampledBits D B S Φ tape)

def output (C : SelectedTape.Algorithm) (S : Schedule) (Φ : ValidFormula) (cc δv ζ : ℚ)
    (ht : FullTests cc (Nat.clog 2 (t10Graph D B Φ).vertices) (t10Graph D B Φ).edges.length δv ζ)
    (tape classifierTape : List Bool) :=
  C.output (request D B S Φ cc δv ζ ht tape)
    (classifierTape.take (C.tapeLength (request D B S Φ cc δv ζ ht tape)))

/-- The single machine depends on the fixed programs, not the source
formula, the value of the gap, or the random tapes. -/
def machine (C : SelectedTape.Algorithm) (S : Schedule) :=
  BitMachineComposition.composition (frontMachine D B S) (V42RawRequestPacket.classifiedMachine C)

def size (S : Schedule) (Φ : ValidFormula) (tape classifierTape : List Bool) :=
  (sourceWord D B S Φ tape).length+V42WRaw.clock (t10Graph D B Φ) (S.gap Φ.val.variables)+
    sampleSide (Nat.clog 2 (t10Graph D B Φ).vertices) (S.gap Φ.val.variables)^2+
    classifierTape.length+1

def clock (C : SelectedTape.Algorithm) (S : Schedule) (Φ : ValidFormula)
    (tape classifierTape : List Bool) :=
  frontClock D B S Φ tape+2*(frontWord D B S Φ tape classifierTape).length+2+
    V42RawClassifierClock.cap C (size D B S Φ tape classifierTape)

theorem sourceWord_eq (S : Schedule) (Φ : ValidFormula) (tape : List Bool)
    (hfirst : V42RawSamplerJoin.precision (t10Graph D B Φ).vertices (S.gap Φ.val.variables)*
      V42RawSamplerJoin.reservation (t10Graph D B Φ).vertices (S.gap Φ.val.variables)≤tape.length) :
    sourceWord D B S Φ tape = V42RawRequestPacket.inputWord (t10Graph D B Φ)
      (S.gap Φ.val.variables) (sampledBits D B S Φ tape) (residual D B S Φ tape) := by
  have hv := V40SourceBlockView.word_view _ _ tape hfirst
  unfold sourceWord V42RawRequestPacket.inputWord V39TypedPacket.number
  rw [V39ThreePortFrame.inputBank_widen,V39ThreePortFrame.inputBank_widen]
  exact congrArg (fun tw : List Bool => BitMachineBankCodec.encode
    (A3Assembly.Wrap.widen (V39ThreePortFrame.workCount gPort kPort tPort)
      ![EncodedGraph.encode (t10Graph D B Φ),List.replicate (S.gap Φ.val.variables) true,tw])) hv.symm

/-- Full source-to-classifier execution.  The only tape premises are the
literal amount of sampler randomness and independent classifier prefix.
The graph and unary schedule value are computed by the fixed front. -/
theorem runs (C : SelectedTape.Algorithm) (S : Schedule) (Φ : ValidFormula) (cc δv ζ : ℚ)
    (ht : FullTests cc (Nat.clog 2 (t10Graph D B Φ).vertices) (t10Graph D B Φ).edges.length δv ζ)
    (tape classifierTape : List Bool)
    (hfirst : V42RawSamplerJoin.precision (t10Graph D B Φ).vertices (S.gap Φ.val.variables)*
      V42RawSamplerJoin.reservation (t10Graph D B Φ).vertices (S.gap Φ.val.variables)≤tape.length)
    (hc : C.tapeLength (request D B S Φ cc δv ζ ht tape)≤classifierTape.length) :
    (machine D B C S).OutputsWithin
      (EncodedComplexity.pair (EncodedComplexity.pair (EncodedCNF.encode Φ.val) tape) classifierTape)
      (output D B C S Φ cc δv ζ ht tape classifierTape)
      (clock D B C S Φ tape classifierTape) := by
  have he := sourceWord_eq D B S Φ tape hfirst
  have hr := V42RawRequestPacket.classified_outputs C (t10Graph D B Φ) (t10Graph_valid D B Φ)
    (S.gap Φ.val.variables) cc δv ζ ht (sampledBits D B S Φ tape)
    (residual D B S Φ tape) classifierTape hc
  have hclock := V42RawClassifierClock.classified_clock_le C (t10Graph D B Φ) (t10Graph_valid D B Φ)
    (S.gap Φ.val.variables) cc δv ζ ht (sampledBits D B S Φ tape)
    (residual D B S Φ tape) classifierTape
  rw [←he] at hr hclock
  have hc' := BitMachine.outputsWithin_mono _ hr hclock
  exact BitMachineComposition.composition_outputsWithin _ _
    (front_outputs D B S Φ tape classifierTape) hc'

/-- Actual finite random-tape machine, using the physically computed
carrier and the fixed two-block cut. -/
def randomMachine (C : SelectedTape.Algorithm) (S : Schedule) (R : PhysicalConcat.Producer) :=
  BitMachineComposition.composition (splitMachine R) (machine D B C S)

def randomOutput (C : SelectedTape.Algorithm) (S : Schedule) (R : PhysicalConcat.Producer)
    (Φ : ValidFormula) (cc δv ζ : ℚ)
    (ht : FullTests cc (Nat.clog 2 (t10Graph D B Φ).vertices) (t10Graph D B Φ).edges.length δv ζ)
    (tape : List Bool) :=
  let w := EncodedCNF.encode Φ.val
  output D B C S Φ cc δv ζ ht (tape.take (blockLength R w))
    ((tape.take (carrierLength R w)).drop (blockLength R w))

def randomClock (C : SelectedTape.Algorithm) (S : Schedule) (R : PhysicalConcat.Producer)
    (Φ : ValidFormula) (tape : List Bool) :=
  let w := EncodedCNF.encode Φ.val
  splitClock R w+2*(splitWord R w tape).length+2+
    clock D B C S Φ (tape.take (blockLength R w))
      ((tape.take (carrierLength R w)).drop (blockLength R w))

/-- One fixed machine runs on every fair-bit carrier tape.  All input
parameters and both blocks are physically generated or cut by that machine. -/
theorem random_runs (C : SelectedTape.Algorithm) (S : Schedule) (R : PhysicalConcat.Producer)
    (Φ : ValidFormula) (cc δv ζ : ℚ)
    (ht : FullTests cc (Nat.clog 2 (t10Graph D B Φ).vertices) (t10Graph D B Φ).edges.length δv ζ)
    (hfirst : V42RawSamplerJoin.precision (t10Graph D B Φ).vertices (S.gap Φ.val.variables)*
      V42RawSamplerJoin.reservation (t10Graph D B Φ).vertices (S.gap Φ.val.variables)≤
        blockLength R (EncodedCNF.encode Φ.val))
    (hclass : ∀ tape, C.tapeLength (request D B S Φ cc δv ζ ht tape)≤
      blockLength R (EncodedCNF.encode Φ.val))
    (tape : Fin (carrierLength R (EncodedCNF.encode Φ.val))→Bool) :
    (randomMachine D B C S R).OutputsWithin
      (EncodedComplexity.pair (EncodedCNF.encode Φ.val) (List.ofFn tape))
      (randomOutput D B C S R Φ cc δv ζ ht (List.ofFn tape))
      (randomClock D B C S R Φ (List.ofFn tape)) := by
  let w := EncodedCNF.encode Φ.val
  let L := blockLength R w
  have hL : L≤(List.ofFn tape).length := by
    simp only [List.length_ofFn]
    dsimp only [carrierLength,L,w]
    omega
  have hlen : ((List.ofFn tape).take L).length=L := by
    rw [List.length_take,Nat.min_eq_left hL]
  have hlen2 : (((List.ofFn tape).take (carrierLength R w)).drop L).length=L := by
    rw [List.length_drop,List.length_take,List.length_ofFn,Nat.min_self]
    unfold carrierLength
    dsimp [L]
    omega
  have hr := runs D B C S Φ cc δv ζ ht ((List.ofFn tape).take L)
    (((List.ofFn tape).take (carrierLength R w)).drop L)
    (by rw [hlen]; exact hfirst) (by rw [hlen2]; exact hclass _)
  exact BitMachineComposition.composition_outputsWithin _ _ (split_outputs R w (List.ofFn tape)) hr

#print axioms runs
#print axioms random_runs
end
end CurrentV43.ParametricSource

