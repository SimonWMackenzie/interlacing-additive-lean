import CurrentV43.Parametric.Caller
import CurrentAdditive.V42RawRequestSemantics

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768
namespace CurrentV43.ParametricSource
noncomputable section
open Paper2 Turing EthInapproximability.CurrentPaper CurrentAdditive
open EncodedETHSource EncodedETHSourceComposition
open Unit4Shell Unit4Shell.T10Finite V42RuntimeSchedule
open V39ActualOutputMajority

private theorem bits_take (b N L : ℕ) (word : List Bool) (h : b*N≤L) :
    V40SourceBlockView.bits b N (word.take L)=V40SourceBlockView.bits b N (word.take (b*N)) := by
  unfold V40SourceBlockView.bits
  congr 1
  funext i
  simp only [V40SourceBlockView.prefixBits,List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt (lt_of_lt_of_le i.isLt h),List.getElem?_take_of_lt i.isLt]

private theorem bits_word (b N : ℕ) (bits : RoundedDraw.BitBlocks b N) :
    V40SourceBlockView.bits b N (RoundedCodeLoop.tapeWord b N bits)=bits := by
  apply V40BlockTapeLaw.tapeWord_injective b N
  rw [V40SourceBlockView.bits_word b N _ (by simp [RoundedCodeLoop.tapeWord_length])]
  exact List.take_of_length_le (by simp [RoundedCodeLoop.tapeWord_length])

private theorem cut_classifier (L P s : ℕ) (word : List Bool) (h : L+s≤P) :
    ((word.take P).drop L).take s=(word.drop L).take s := by
  rw [List.drop_take,List.take_take,Nat.min_eq_left (show s≤P-L by omega)]

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
local instance probabilitySourceNonzero (Φ : ValidFormula) : NeZero (t10Graph D B Φ).vertices :=
  ⟨(t10_vertices_pos D B Φ).ne'⟩

/-- Every event of the actual fixed-machine output has precisely the law
of the same rounded sampler bits and an independent classifier tape.  No
assumed output law or desired success probability enters this identity. -/
theorem output_probability (E : ActualEstimator) (S : Schedule) (R : PhysicalConcat.Producer)
    (Φ : ValidFormula) (cc δv ζ : ℚ)
    (ht : FullTests cc (Nat.clog 2 (t10Graph D B Φ).vertices) (t10Graph D B Φ).edges.length δv ζ)
    (hfirst : V42RawSamplerJoin.precision (t10Graph D B Φ).vertices (S.gap Φ.val.variables)*
      V42RawSamplerJoin.reservation (t10Graph D B Φ).vertices (S.gap Φ.val.variables)≤
        blockLength R (EncodedCNF.encode Φ.val))
    (hclass : V42JointEstimatorLaw.classifierLength E
      (Nat.clog 2 (t10Graph D B Φ).vertices) (S.gap Φ.val.variables)≤
        blockLength R (EncodedCNF.encode Φ.val))
    (event : List Bool→Prop) :
    (Unit4Shell.Definitions.uniformTape (carrierLength R (EncodedCNF.encode Φ.val))).prob
      (fun tape => event (randomOutput D B E.classifier S R Φ cc δv ζ ht (List.ofFn tape))) =
    (V42JointEstimatorLaw.independentLaw
      (RoundedDraw.bitBlocksLaw
        (V42RawSamplerJoin.precision (t10Graph D B Φ).vertices (S.gap Φ.val.variables))
        (V42RawSamplerJoin.reservation (t10Graph D B Φ).vertices (S.gap Φ.val.variables))) E
      (Nat.clog 2 (t10Graph D B Φ).vertices) (S.gap Φ.val.variables)).prob
        (fun z => event (E.classifier.output
          (V42RawRequestPacket.request (t10Graph D B Φ) (t10Graph_valid D B Φ)
            (S.gap Φ.val.variables) cc δv ζ ht z.1) (List.ofFn z.2))) := by
  let bv := V42RawSamplerJoin.precision (t10Graph D B Φ).vertices (S.gap Φ.val.variables)
  let Nv := V42RawSamplerJoin.reservation (t10Graph D B Φ).vertices (S.gap Φ.val.variables)
  let L := blockLength R (EncodedCNF.encode Φ.val)
  let P := carrierLength R (EncodedCNF.encode Φ.val)
  let s := V42JointEstimatorLaw.classifierLength E
    (Nat.clog 2 (t10Graph D B Φ).vertices) (S.gap Φ.val.variables)
  let req := fun bits : RoundedDraw.BitBlocks bv Nv =>
    V42RawRequestPacket.request (t10Graph D B Φ) (t10Graph_valid D B Φ)
      (S.gap Φ.val.variables) cc δv ζ ht bits
  have hcl (bits : RoundedDraw.BitBlocks bv Nv) : E.classifier.tapeLength (req bits)=s :=
    V42RawRequestSemantics.classifier_length _ _ _ _ _ _ _ E bits
  have hsecond : L+s≤P := by
    dsimp [P,carrierLength]
    change L+s≤2*L
    change s≤L at hclass
    omega
  change bv*Nv≤L at hfirst
  have hprob := V40BlockTapeLaw.uniform_twoCut (b:=bv) (N:=Nv) hfirst hsecond
    (fun a t => event (E.classifier.output (req (V40SourceBlockView.bits bv Nv a)) t))
  have houtput (t : Fin P→Bool) :
      randomOutput D B E.classifier S R Φ cc δv ζ ht (List.ofFn t)=
        E.classifier.output (req (V40SourceBlockView.bits bv Nv ((List.ofFn t).take (bv*Nv))))
          (((List.ofFn t).drop L).take s) := by
    change E.classifier.output (req (V40SourceBlockView.bits bv Nv ((List.ofFn t).take L)))
      ((((List.ofFn t).take P).drop L).take (E.classifier.tapeLength
        (req (V40SourceBlockView.bits bv Nv ((List.ofFn t).take L))))) = _
    rw [hcl,bits_take bv Nv L _ hfirst,cut_classifier L P s _ hsecond]
  have hevent := congrArg (fun F : (Fin P→Bool)→List Bool =>
    (Unit4Shell.Definitions.uniformTape P).prob (fun t => event (F t))) (funext houtput)
  apply hevent.trans
  apply hprob.trans
  simp_rw [bits_word]
  rfl

/-- The exact event consumed by the estimator-to-SAT accuracy argument,
for the very table printed by the all-round sampler. -/
theorem acceptance_probability (E : ActualEstimator) (S : Schedule) (R : PhysicalConcat.Producer)
    (Φ : ValidFormula) (cc δv ζ : ℚ)
    (ht : FullTests cc (Nat.clog 2 (t10Graph D B Φ).vertices) (t10Graph D B Φ).edges.length δv ζ)
    (hfirst : V42RawSamplerJoin.precision (t10Graph D B Φ).vertices (S.gap Φ.val.variables)*
      V42RawSamplerJoin.reservation (t10Graph D B Φ).vertices (S.gap Φ.val.variables)≤
        blockLength R (EncodedCNF.encode Φ.val))
    (hclass : V42JointEstimatorLaw.classifierLength E
      (Nat.clog 2 (t10Graph D B Φ).vertices) (S.gap Φ.val.variables)≤
        blockLength R (EncodedCNF.encode Φ.val)) :
    (Unit4Shell.Definitions.uniformTape (carrierLength R (EncodedCNF.encode Φ.val))).prob
      (fun tape => randomOutput D B E.classifier S R Φ cc δv ζ ht (List.ofFn tape)=[true]) =
    (V42JointEstimatorLaw.independentLaw
      (RoundedDraw.bitBlocksLaw
        (V42RawSamplerJoin.precision (t10Graph D B Φ).vertices (S.gap Φ.val.variables))
        (V42RawSamplerJoin.reservation (t10Graph D B Φ).vertices (S.gap Φ.val.variables))) E
      (Nat.clog 2 (t10Graph D B Φ).vertices) (S.gap Φ.val.variables)).prob
        (fun z => V42JointEstimatorLaw.accepts E (Nat.clog 2 (t10Graph D B Φ).vertices)
          (S.gap Φ.val.variables) (V42RawRequestPacket.matrix (t10Graph D B Φ) (t10Graph_valid D B Φ)
            (S.gap Φ.val.variables) cc δv ζ ht z.1) z.2) :=
  output_probability D B E S R Φ cc δv ζ ht hfirst hclass (·=[true])

#print axioms output_probability
#print axioms acceptance_probability
end
end CurrentV43.ParametricSource




