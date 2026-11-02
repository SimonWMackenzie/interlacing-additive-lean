import CurrentAdditive.V42RandomizedSourceData
import CurrentAdditive.V42RawRequestSemantics
import CurrentAdditive.V42SourceClassifierRun

/-! The single physical random tape has exactly the construction-block and
independent classifier law used by the actual request semantics. -/
namespace CurrentAdditive.V42RandomizedETHEndpoint
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition
open Unit4Shell.T10Finite Unit4Shell.Asymptotics
open V42RuntimeSchedule V39ActualOutputMajority
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768

private theorem bits_take (b N L : ℕ) (word : List Bool) (h : b*N ≤ L) :
    V40SourceBlockView.bits b N (word.take L)=
      V40SourceBlockView.bits b N (word.take (b*N)) := by
  unfold V40SourceBlockView.bits
  congr 1
  funext i
  simp only [V40SourceBlockView.prefixBits,List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt (lt_of_lt_of_le i.isLt h),
    List.getElem?_take_of_lt i.isLt]

private theorem bits_word (b N : ℕ) (bits : RoundedDraw.BitBlocks b N) :
    V40SourceBlockView.bits b N (RoundedCodeLoop.tapeWord b N bits)=bits := by
  apply V40BlockTapeLaw.tapeWord_injective b N
  rw [V40SourceBlockView.bits_word b N _ (by simp [RoundedCodeLoop.tapeWord_length])]
  exact List.take_of_length_le (by simp [RoundedCodeLoop.tapeWord_length])

private theorem cut_classifier (L P s : ℕ) (word : List Bool) (h : L+s ≤ P) :
    ((word.take P).drop L).take s=(word.drop L).take s := by
  rw [List.drop_take,List.take_take,Nat.min_eq_left (show s ≤ P-L by omega)]

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- Exact event identity for the actual all-input caller output. The fixed
cutoff supplies the literal full reservation and independent-block fit. -/
theorem machine_probability (E : ActualEstimator) (cs cutoff : ℕ) (hcut : 1 ≤ cutoff)
    (hmin : V42SourceClassifier.minimum D B E.classifier cs ≤ cutoff) (w : List Bool) :
    (Unit4Shell.Definitions.uniformTape
      (V42SourceClassifier.carrier E.classifier cutoff w.length)).prob
      (fun t => V42SourceClassifier.output D B E.classifier cs cutoff hcut hmin w
        (List.ofFn t)=[true]) =
    (sourceLaw D B E (V42SourceClassifier.routed cs cutoff hcut w)).prob
      (fun z => sourceAccepts D B (V42SourceClassifier.routed cs cutoff hcut w)
        (V42SourceClassifier.tests D B E.classifier cs cutoff hcut hmin w) E z.1 z.2) := by
  let b := V42SourceClassifier.precision D B cs cutoff hcut w
  let N := V42SourceClassifier.reservation D B cs cutoff hcut w
  let L := V42SourceClassifier.blockLength cs cutoff w
  let P := 2^(classifierBlockExponent E.classifier)*L
  let R := V42SourceClassifier.carrier E.classifier cutoff w.length
  let s := V42JointEstimatorLaw.classifierLength E
    (Nat.clog 2 (V42SourceClassifier.graph D B cs cutoff hcut w).vertices)
    (V42SourceClassifier.gap cs cutoff hcut w)
  let req := V42SourceClassifier.request D B E.classifier cs cutoff hcut hmin w
  have hcl (bits : RoundedDraw.BitBlocks b N) : E.classifier.tapeLength (req bits)=s := by
    exact V42RawRequestSemantics.classifier_length _ _ _ _ _ _ _ E bits
  have hs := V42SourceClassifier.resources D B E.classifier cs cutoff hcut hmin w
  have hfirst : b*N ≤ L := hs.1
  have hsecond : L+s ≤ P := by
    have h := hs.2 (V40SourceBlockView.bits b N [])
    rw [hcl] at h
    exact h
  have hcarrier : P ≤ R := V42SourceClassifier.carrier_fit E.classifier cs cutoff hcut w
  have hprob := V40BlockTapeLaw.uniform_twoCut hfirst (hsecond.trans hcarrier)
    (fun a t => E.classifier.output (req (V40SourceBlockView.bits b N a)) t=[true])
  have houtput (t : Fin R → Bool) :
      V42SourceClassifier.output D B E.classifier cs cutoff hcut hmin w (List.ofFn t)=
      E.classifier.output
        (req (V40SourceBlockView.bits b N ((List.ofFn t).take (b*N))))
        (((List.ofFn t).drop L).take s) := by
    change E.classifier.output
      (req (V40SourceBlockView.bits b N ((List.ofFn t).take L)))
      (((List.ofFn t).take P).drop L |>.take (E.classifier.tapeLength
        (req (V40SourceBlockView.bits b N ((List.ofFn t).take L))))) = _
    rw [hcl,bits_take b N L _ hfirst,cut_classifier L P s _ hsecond]
  simp_rw [houtput]
  apply hprob.trans
  simp_rw [bits_word]
  rfl

#print axioms machine_probability
end
end CurrentAdditive.V42RandomizedETHEndpoint

