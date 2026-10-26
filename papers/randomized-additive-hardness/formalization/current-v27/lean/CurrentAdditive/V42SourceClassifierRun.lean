import CurrentAdditive.V42SourceClassifierMachine

set_option autoImplicit false
set_option maxHeartbeats 20000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768
namespace CurrentAdditive.V42SourceClassifier
noncomputable section
open Paper2 Turing EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition
open Unit4Shell.T10Finite Unit4Shell.Asymptotics
open V42RuntimeSchedule
local instance : DecidableEq V42RawMidpointRequest.Raw := Classical.decEq _

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

theorem bankWord_length_le (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff) (w tape : List Bool) :
    (bankWord D B density cutoff hcutoff w tape).length ≤ bankInputCap D B density cutoff hcutoff w := by
  unfold bankWord V39TypedPacket.number
  rw [V39ThreePortFrame.inputBank_widen,A3Assembly.Wrap.encode_widen]
  rw [List.length_append,List.length_replicate,BitMachineBankCodec.encode_length]
  simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,
    Nat.add_zero,List.length_replicate]
  have ht := List.length_take_le (blockLength density cutoff w) tape
  unfold bankInputCap bankWidth
  omega

theorem classifierBlock_length_le (C : SelectedTape.Algorithm) (density cutoff : ℕ)
    (w tape : List Bool) : (classifierBlock C density cutoff w tape).length ≤
    2^(V42RandomizedETHEndpoint.classifierBlockExponent C)*blockLength density cutoff w := by
  unfold classifierBlock
  rw [List.length_drop,List.length_take]
  omega

theorem frontWord_length_le (C : SelectedTape.Algorithm) (density cutoff : ℕ)
    (hcutoff : 1 ≤ cutoff) (w tape : List Bool) :
    (frontWord D B C density cutoff hcutoff w tape).length ≤
      frontWordCap D B C density cutoff hcutoff w := by
  have hb := bankWord_length_le D B density cutoff hcutoff w tape
  have hc := classifierBlock_length_le C density cutoff w tape
  unfold frontWord frontWordCap
  rw [EncodedComplexity.pair_length]
  omega

theorem bankWord_eq (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff) (w tape : List Bool)
    (hfirst : precision D B density cutoff hcutoff w*reservation D B density cutoff hcutoff w ≤
      (tape.take (blockLength density cutoff w)).length) :
    bankWord D B density cutoff hcutoff w tape =
      V42RawRequestPacket.inputWord (graph D B density cutoff hcutoff w) (gap density cutoff hcutoff w)
        (sampledBits D B density cutoff hcutoff w tape) (residual D B density cutoff hcutoff w tape) := by
  have hv := V40SourceBlockView.word_view _ _ _ hfirst
  exact congrArg (fun tw : List Bool => BitMachineBankCodec.encode (fun i =>
    V39ThreePortFrame.inputBank gPort kPort tPort
      (EncodedGraph.encode (graph D B density cutoff hcutoff w))
      (List.replicate (gap density cutoff hcutoff w) true) tw
      ((V39TypedPacket.number gPort kPort tPort hgk hgt hkt).symm i))) hv.symm

theorem caller_cap_mono (C : SelectedTape.Algorithm) {a b : ℕ} (h : a ≤ b) :
    V42RawClassifierClock.cap C a ≤ V42RawClassifierClock.cap C b := by
  unfold V42RawClassifierClock.cap V40MidpointRequest.cap V40MidpointRequest.invokeCap
    V40ClassifierTail.cap NPOwner1.Trunc.timeBound
  gcongr

/-- One fixed actual machine handles every raw formula and every carrier
with the prescribed bounded prefix. All numerical caller conditions follow
from the fixed source cutoff; no completed execution is a premise. -/
theorem runs (C : SelectedTape.Algorithm) (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (hmin : minimum D B C density ≤ cutoff) (w tape : List Bool)
    (hTape : 2^(V42RandomizedETHEndpoint.classifierBlockExponent C)*blockLength density cutoff w ≤ tape.length) :
    (machine D B C density cutoff hcutoff).OutputsWithin (EncodedComplexity.pair w tape)
      (output D B C density cutoff hcutoff hmin w tape) (time D B C density cutoff hcutoff w) := by
  have hs := resources D B C density cutoff hcutoff hmin w
  have hL : blockLength density cutoff w ≤ tape.length :=
    (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)).trans hTape
  have hfirst : precision D B density cutoff hcutoff w*reservation D B density cutoff hcutoff w ≤
      (tape.take (blockLength density cutoff w)).length := by
    rw [List.length_take,Nat.min_eq_left hL]
    exact hs.1
  have hinput := bankWord_eq D B density cutoff hcutoff w tape hfirst
  have hsecond := hs.2 (sampledBits D B density cutoff hcutoff w tape)
  have hclass : C.tapeLength (request D B C density cutoff hcutoff hmin w
      (sampledBits D B density cutoff hcutoff w tape)) ≤ (classifierBlock C density cutoff w tape).length := by
    unfold classifierBlock
    rw [List.length_drop,List.length_take,Nat.min_eq_left hTape]
    omega
  have hr := V42RawRequestPacket.classified_outputs C
    (graph D B density cutoff hcutoff w) (graph_valid D B density cutoff hcutoff w)
    (gap density cutoff hcutoff w) (coefficient D B density cutoff hcutoff w)
    (deltaV D B density cutoff hcutoff w) (V38Schedule.sourceZeta (sourceGap D B))
    (tests D B C density cutoff hcutoff hmin w) (sampledBits D B density cutoff hcutoff w tape)
    (residual D B density cutoff hcutoff w tape) (classifierBlock C density cutoff w tape) hclass
  have hc := V42RawClassifierClock.classified_clock_le C
    (graph D B density cutoff hcutoff w) (graph_valid D B density cutoff hcutoff w)
    (gap density cutoff hcutoff w) (coefficient D B density cutoff hcutoff w)
    (deltaV D B density cutoff hcutoff w) (V38Schedule.sourceZeta (sourceGap D B))
    (tests D B C density cutoff hcutoff hmin w) (sampledBits D B density cutoff hcutoff w tape)
    (residual D B density cutoff hcutoff w tape) (classifierBlock C density cutoff w tape)
  rw [←hinput] at hr hc
  have hX : (bankWord D B density cutoff hcutoff w tape).length+
      V42WRaw.clock (graph D B density cutoff hcutoff w) (gap density cutoff hcutoff w)+
      sampleSide (Nat.clog 2 (graph D B density cutoff hcutoff w).vertices) (gap density cutoff hcutoff w)^2+
      (classifierBlock C density cutoff w tape).length+1 ≤ sizeCap D B C density cutoff hcutoff w := by
    have hb := bankWord_length_le D B density cutoff hcutoff w tape
    have ht := classifierBlock_length_le C density cutoff w tape
    unfold sizeCap
    omega
  have hc' := hc.trans (caller_cap_mono C hX)
  have hf := front_runs D B C density cutoff hcutoff w tape
  have hrun := BitMachineComposition.composition_outputsWithin _ _ hf hr
  apply BitMachine.outputsWithin_mono _ hrun
  have hl := frontWord_length_le D B C density cutoff hcutoff w tape
  unfold time
  omega

/-- Appending any unused suffix changes neither the actual sampled bits
nor the independent classifier prefix and hence never changes the output. -/
theorem output_append (C : SelectedTape.Algorithm) (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (hmin : minimum D B C density ≤ cutoff) (w tape suffix : List Bool)
    (hTape : 2^(V42RandomizedETHEndpoint.classifierBlockExponent C)*blockLength density cutoff w ≤ tape.length) :
    output D B C density cutoff hcutoff hmin w (tape++suffix) =
      output D B C density cutoff hcutoff hmin w tape := by
  have hL : blockLength density cutoff w ≤ tape.length :=
    (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)).trans hTape
  have he1 := List.take_append_of_le_length (l₂:=suffix) hL
  have he2 := List.take_append_of_le_length (l₂:=suffix) hTape
  simp only [output,sampledBits,classifierBlock,he1,he2]

def carrier (C : SelectedTape.Algorithm) (cutoff m : ℕ) :=
  AEth4.tapeCA (AEth4.phiLen cutoff) (7+V42RandomizedETHEndpoint.classifierBlockExponent C) m

theorem carrier_fit (C : SelectedTape.Algorithm) (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff) (w : List Bool) :
    2^(V42RandomizedETHEndpoint.classifierBlockExponent C)*blockLength density cutoff w ≤
      carrier C cutoff w.length :=
  V39SourceFront.cut_fits_carrier (density+2) cutoff _ hcutoff w

theorem runs_carrier (C : SelectedTape.Algorithm) (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (hmin : minimum D B C density ≤ cutoff) (w : List Bool) (tape : Fin (carrier C cutoff w.length) → Bool) :
    (machine D B C density cutoff hcutoff).OutputsWithin (EncodedComplexity.pair w (List.ofFn tape))
      (output D B C density cutoff hcutoff hmin w (List.ofFn tape)) (time D B C density cutoff hcutoff w) := by
  apply runs D B C density cutoff hcutoff hmin
  simpa only [List.length_ofFn] using carrier_fit C density cutoff hcutoff w

/-- The effective tape carrier's extension law is an actual execution,
including a globally unused appended suffix. -/
theorem extend (C : SelectedTape.Algorithm) (density cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (hmin : minimum D B C density ≤ cutoff) (w tape suffix : List Bool)
    (hlen : tape.length = carrier C cutoff w.length) :
    (machine D B C density cutoff hcutoff).OutputsWithin (EncodedComplexity.pair w (tape++suffix))
      (output D B C density cutoff hcutoff hmin w tape) (time D B C density cutoff hcutoff w) := by
  have ht : 2^(V42RandomizedETHEndpoint.classifierBlockExponent C)*blockLength density cutoff w ≤ tape.length := by
    rw [hlen]
    exact carrier_fit C density cutoff hcutoff w
  have hrun := runs D B C density cutoff hcutoff hmin w (tape++suffix)
    (ht.trans (by simp only [List.length_append]; omega))
  rw [output_append D B C density cutoff hcutoff hmin w tape suffix ht] at hrun
  exact hrun

/-- The exact source-and-cut component is subexponential in the original
variable count on every promised sparse formula above its finite cutoff. -/
theorem sourceClock_sparse (C : SelectedTape.Algorithm) (density cutoff : ℕ)
    (hcutoff : 1 ≤ cutoff) (ε : ℝ) (hε : 0 < ε) :
    ∃ A d N₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ density*Φ.val.variables → N₀ ≤ Φ.val.variables →
      sourceClock (frontA D B C density cutoff hcutoff) (frontE D B C density cutoff hcutoff)
        (frontP D B C density cutoff hcutoff) C density cutoff (EncodedCNF.encode Φ.val) ≤
      A*⌈(2:ℝ)^(ε*Φ.val.variables)⌉₊*((EncodedCNF.encode Φ.val).length+1)^d := by
  obtain ⟨A,d,N₀,h⟩ := V39SourceFront.cut_clock_sparse D B (density+2) cutoff
    (V42RandomizedETHEndpoint.classifierBlockExponent C)
    (frontA D B C density cutoff hcutoff) (frontE D B C density cutoff hcutoff)
    (frontP D B C density cutoff hcutoff) ε hε
  refine ⟨A,d,N₀,?_⟩
  intro Φ hsp hN
  apply h Φ _ hN
  exact hsp.trans (Nat.mul_le_mul_right _ (show density ≤ density+2 by omega))

end
end CurrentAdditive.V42SourceClassifier
#print axioms CurrentAdditive.V42SourceClassifier.runs
#print axioms CurrentAdditive.V42SourceClassifier.runs_carrier
#print axioms CurrentAdditive.V42SourceClassifier.output_append

