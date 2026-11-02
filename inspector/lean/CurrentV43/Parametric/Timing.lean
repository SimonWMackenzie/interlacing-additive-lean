import CurrentV43.Parametric.Caller

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

theorem sourceWord_length (S : Schedule) (Φ : ValidFormula) (tape : List Bool) :
    (sourceWord D B S Φ tape).length = V39ThreePortFrame.workCount gPort kPort tPort+
      2*((EncodedGraph.encode (t10Graph D B Φ)).length+S.gap Φ.val.variables+tape.length)+3 := by
  unfold sourceWord V39TypedPacket.number
  rw [V39ThreePortFrame.inputBank_widen,A3Assembly.Wrap.encode_widen]
  rw [List.length_append,List.length_replicate,BitMachineBankCodec.encode_length]
  simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,
    Nat.add_zero,List.length_replicate]
  omega

theorem sourceClock_length_eq (S : Schedule) (Φ : ValidFormula) (tape tape' : List Bool)
    (hlen : tape.length=tape'.length) :
    sourceClock D B S Φ tape=sourceClock D B S Φ tape' := by
  simp only [sourceClock,kFrontClock,EncodedComplexity.pair_length,
    BitMachineBankCodec.encode_length,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,Nat.add_zero,List.length_replicate,hlen]

theorem clock_length_eq (C : SelectedTape.Algorithm) (S : Schedule) (Φ : ValidFormula)
    (tape classifierTape tape' classifierTape' : List Bool)
    (hlen : tape.length=tape'.length) (hclass : classifierTape.length=classifierTape'.length) :
    clock D B C S Φ tape classifierTape=clock D B C S Φ tape' classifierTape' := by
  simp only [clock,frontClock,frontWord,size,EncodedComplexity.pair_length,sourceWord_length,
    sourceClock_length_eq D B S Φ tape tape' hlen,hlen,hclass]

/-- One source-only clock for every bit vector in the actual finite
carrier.  The clock does not depend on outcomes of any random choice. -/
def uniformClock (C : SelectedTape.Algorithm) (S : Schedule) (R : PhysicalConcat.Producer)
    (Φ : ValidFormula) :=
  randomClock D B C S R Φ (List.replicate (carrierLength R (EncodedCNF.encode Φ.val)) false)

theorem randomClock_eq (C : SelectedTape.Algorithm) (S : Schedule) (R : PhysicalConcat.Producer)
    (Φ : ValidFormula) (tape : List Bool)
    (hlen : carrierLength R (EncodedCNF.encode Φ.val)≤tape.length) :
    randomClock D B C S R Φ tape=uniformClock D B C S R Φ := by
  let w := EncodedCNF.encode Φ.val
  let L := blockLength R w
  let T := carrierLength R w
  let zeroTape := List.replicate T false
  have hLT : L≤T := by dsimp [L,T,carrierLength]; omega
  have htake : (tape.take L).length=(zeroTape.take L).length := by
    simp only [List.length_take]
    dsimp [zeroTape]
    rw [List.length_replicate,Nat.min_eq_left (hLT.trans hlen),Nat.min_eq_left hLT]
  have hdrop : ((tape.take T).drop L).length=((zeroTape.take T).drop L).length := by
    simp only [List.length_drop,List.length_take]
    dsimp [zeroTape]
    rw [List.length_replicate,Nat.min_eq_left hlen,Nat.min_self]
  have hc := clock_length_eq D B C S Φ (tape.take L) ((tape.take T).drop L)
    (zeroTape.take L) ((zeroTape.take T).drop L) htake hdrop
  change splitClock R w+2*(splitWord R w tape).length+2+
    clock D B C S Φ (tape.take L) ((tape.take T).drop L) =
      splitClock R w+2*(splitWord R w zeroTape).length+2+
        clock D B C S Φ (zeroTape.take L) ((zeroTape.take T).drop L)
  rw [hc]
  simp only [splitWord,EncodedComplexity.pair_length]
  change _+2*(2*(2*w.length+1+(tape.take L).length)+1+((tape.take T).drop L).length)+2+_=
    _+2*(2*(2*w.length+1+(zeroTape.take L).length)+1+((zeroTape.take T).drop L).length)+2+_
  rw [htake,hdrop]

theorem random_runs_uniform (C : SelectedTape.Algorithm) (S : Schedule) (R : PhysicalConcat.Producer)
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
      (uniformClock D B C S R Φ) := by
  have h:=random_runs D B C S R Φ cc δv ζ ht hfirst hclass tape
  rw [randomClock_eq D B C S R Φ (List.ofFn tape) (by simp only [List.length_ofFn]; exact le_rfl)] at h
  exact h

#print axioms sourceWord_length
#print axioms clock_length_eq
#print axioms randomClock_eq
#print axioms random_runs_uniform
end
end CurrentV43.ParametricSource

