import CurrentAdditive.V40RandomizedRoutedLaw
import CurrentAdditive.V40SourceClassifierRun

/-! The single physical random tape has exactly the construction-block and
independent classifier law used by the actual request semantics. -/
namespace CurrentAdditive.V40RandomizedETHEndpoint
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition
open Unit4Shell.T10Finite Unit4Shell.Asymptotics
open V38Schedule V39PublicSchedule V39ActualOutputMajority
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
    (hmin : V40SourceClassifier.minimum D B E.classifier cs ≤ cutoff) (w : List Bool) :
    (Unit4Shell.Definitions.uniformTape
      (V40SourceClassifier.carrier E.classifier cutoff w.length)).prob
      (fun t => V40SourceClassifier.output D B E.classifier cs cutoff hcut hmin w
        (List.ofFn t)=[true]) =
    (sourceLaw D B E (routedSource cs cutoff hcut w)).prob
      (fun z => sourceAccepts D B (routedSource cs cutoff hcut w)
        (V40SourceClassifier.tests D B E.classifier cs cutoff hcut hmin w) E z.1 z.2) := by
  let b := V40SourceClassifier.precision D B cs cutoff hcut w
  let N := V40SourceClassifier.reservation D B cs cutoff hcut w
  let L := V40SourceClassifier.blockLength cs cutoff w
  let P := 2^(classifierBlockExponent E.classifier)*L
  let R := V40SourceClassifier.carrier E.classifier cutoff w.length
  let s := V40JointEstimatorLaw.classifierLength E
    (Nat.clog 2 (V40SourceClassifier.graph D B cs cutoff hcut w).vertices)
    (V40SourceClassifier.gap cs cutoff hcut w)
  let req := V40SourceClassifier.request D B E.classifier cs cutoff hcut hmin w
  have hcl (bits : RoundedDraw.BitBlocks b N) : E.classifier.tapeLength (req bits)=s := by
    exact V40RawRequestSemantics.classifier_length _ _ _ _ _ _ _ E bits
  have hs := V40SourceClassifier.resources D B E.classifier cs cutoff hcut hmin w
  have hfirst : b*N ≤ L := hs.1
  have hsecond : L+s ≤ P := by
    have h := hs.2 (V40SourceBlockView.bits b N [])
    rw [hcl] at h
    exact h
  have hcarrier : P ≤ R := V40SourceClassifier.carrier_fit E.classifier cs cutoff hcut w
  have hprob := V40BlockTapeLaw.uniform_twoCut hfirst (hsecond.trans hcarrier)
    (fun a t => E.classifier.output (req (V40SourceBlockView.bits b N a)) t=[true])
  have houtput (t : Fin R → Bool) :
      V40SourceClassifier.output D B E.classifier cs cutoff hcut hmin w (List.ofFn t)=
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
end CurrentAdditive.V40RandomizedETHEndpoint
