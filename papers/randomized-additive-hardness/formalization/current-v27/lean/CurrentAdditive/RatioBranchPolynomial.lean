import CurrentAdditive.RatioBranchRun

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 100
noncomputable section
namespace CurrentAdditive.RatioBranchPolynomial
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open MinimumRatioCallbackLayout MinimumRatioContext RatioCanonicalRequests
open RatioListClockBounds RatioListClockCaps RatioUpdaterItemPolynomial EntryClockPoly
open RatioBranchLayout RatioBranchRun

def inputSize {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ) :=
  inputLength (records source) (coeffWords coeff) []

theorem pair_packet_bound {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ) :
    (packet source coeff).length ≤ outputCap (inputSize source coeff) := by
  have h := pair_prefix_bound (records source) (coeffWords coeff) (records source)
    (fun _ h => h) (le_rfl)
  rw [RatioPairListSpec.outputAt_all] at h
  exact h

theorem scalar_bound {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ)
    (lambda : ℚ) (hsize : coeff.size=source.size)
    (hmin : SequentialCode.minimumRatio (source.map Prod.snd) coeff = some lambda) :
    (ratWord lambda).length ≤ outputCap (inputSize source coeff)+
      minCoefficient*(outputCap (inputSize source coeff)+1)^minExponent*MinM.pushBound := by
  have hM := minimum_outputs (RatioPairListSpec.pairs (records source) (coeffWords coeff))
  have hfold : (RatioPairListSpec.pairs (records source) (coeffWords coeff)).foldl
      MinimumRatioStepSpec.step [] = MinimumRatioStepSpec.bestPacket (some lambda) := by
    rw [RatioCanonicalPairs.pairs_exact source coeff hsize,RatioMinimumMachine.canonical_fold,hmin]
  rw [hfold] at hM
  have ho := BitMachine.output_length_bound MinM hM
  have hp := pair_packet_bound source coeff
  have hl : (ratWord lambda).length ≤ (MinimumRatioStepSpec.bestPacket (some lambda)).length := by
    simp [ratWord,MinimumRatioStepSpec.bestPacket,CodeDCanonicalSourceV2.rawOfRat,CodeDCanonicalSource.rawOfRat]
  apply hl.trans (ho.trans ?_)
  change (packet source coeff).length+
      minCoefficient*((packet source coeff).length+1)^minExponent*MinM.pushBound ≤ _
  gcongr

theorem uniform_clock : ∃ C d : Nat,
    ∀ {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ) (lambda : ℚ)
      (hsize : coeff.size=source.size),
      SequentialCode.minimumRatio (source.map Prod.snd) coeff = some lambda →
      clock source coeff lambda hsize ≤ C*(inputSize source coeff+1)^d := by
  obtain ⟨Cu,du,hu⟩ := RatioRequestUpdatePolynomial.uniform_clock
  let pcap := outputCap
  let tm (n : Nat) := minCoefficient*(pcap n+1)^minExponent
  let lcap (n : Nat) := pcap n+tm n*MinM.pushBound
  let ucap (n : Nat) := Cu*(n+lcap n+1)^du
  let cap (n : Nat) := RatioListPolynomial.fullCap n+
    invokeCap MinM (pcap n) (tm n)+2*pcap n+2*n+9+ucap n+3
  have hp : PolyIn (fun n : Nat => n) pcap := by unfold pcap outputCap; solve_update_poly
  have ht : PolyIn (fun n : Nat => n) tm :=
    (PolyIn.const minCoefficient).mul ((hp.add (PolyIn.const 1)).pow minExponent)
  have hl : PolyIn (fun n : Nat => n) lcap := hp.add (ht.mul (PolyIn.const MinM.pushBound))
  have huPoly : PolyIn (fun n : Nat => n) ucap :=
    (PolyIn.const Cu).mul (((PolyIn.self.add hl).add (PolyIn.const 1)).pow du)
  have hi := invoke_poly (fun n : Nat => n) MinM pcap tm hp ht
  have hcap : PolyIn (fun n : Nat => n) cap :=
    ((((((RatioListPolynomial.fullCap_poly.add hi).add ((PolyIn.const 2).mul hp)).add
      ((PolyIn.const 2).mul PolyIn.self)).add (PolyIn.const 9)).add huPoly).add (PolyIn.const 3))
  obtain ⟨C,d,hC⟩ := hcap
  refine ⟨C,d,?_⟩
  intro q source coeff lambda hsize hmin
  let L := inputSize source coeff
  have hpair : pairClock source coeff hsize ≤ RatioListPolynomial.fullCap L := by
    have hp := RatioListPolynomial.prepare_le (records source) (coeffWords coeff) []
    have hl := RatioListPolynomial.pair_clock_le (records source) (coeffWords coeff)
      (by simpa [records,coeffWords] using hsize)
    unfold pairClock RatioListPolynomial.fullCap
    dsimp only [L,inputSize] at *
    omega
  have hpkt := pair_packet_bound source coeff
  have hminclock : minClock source coeff ≤ invokeCap MinM (pcap L) (tm L) :=
    invoke_le MinM (packet source coeff)
      (minCoefficient*((packet source coeff).length+1)^minExponent)
      (pcap L) (tm L) hpkt (by dsimp only [tm,pcap]; gcongr)
  have hn : source.size ≤ L := by
    have hs := GaussRowCount.rows_le_input (records source)
    have hcount : (records source).length = source.size := by
      simp [records]
    rw [hcount] at hs
    dsimp only [L,inputSize,inputLength]
    omega
  have hreset : resetClock source coeff ≤ 2*pcap L+2*L+9 := by
    have hpktL : (packet source coeff).length ≤ pcap L := hpkt
    unfold resetClock
    omega
  have hscalar : (ratWord lambda).length ≤ lcap L := scalar_bound source coeff lambda hsize hmin
  have hinput : RatioRequestUpdatePolynomial.inputSize source coeff lambda ≤ L+lcap L := by
    dsimp only [RatioRequestUpdatePolynomial.inputSize,L,inputSize,inputLength]
    simpa using Nat.add_le_add_left hscalar
      ((SourceListEncoding.encode (records source)).length+(SourceListEncoding.encode (coeffWords coeff)).length)
  have hupdate : updateClock source coeff lambda hsize ≤ ucap L := by
    apply (hu source coeff lambda hsize).trans
    dsimp only [ucap]
    gcongr
  exact (show clock source coeff lambda hsize ≤ cap L by unfold clock; dsimp only [cap]; omega).trans (hC L)

/-- A complete physical dependence-elimination branch. Its stored inputs are
only the original indexed source and the actual Gauss coefficient vector.
The minimum and scalar are computed internally. A single polynomial bounds
the same program through all list preparation, comparisons and updates. -/
theorem uniform_run : ∃ C d : Nat,
    ∀ {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ) (lambda : ℚ)
      (hsize : coeff.size=source.size)
      (hmin : SequentialCode.minimumRatio (source.map Prod.snd) coeff = some lambda)
      (hnonneg : (CodeDUpdatedArithmeticABI.candidateWeights source coeff lambda).all
        (fun w => decide (0 ≤ w)) = true),
    ∃ t ≤ C*(inputSize source coeff+1)^d,
      let result := ((advance program)^[t])
        (⟨some start,control,frame (initialBank source coeff)⟩ : TM2.Cfg (fun _ : BigStack => Bool) _ _)
      result.l = none ∧ result.stk (core (low 24)) =
        CodeDCanonicalSourceV2.encodedSource (CodeDCompactSequentialBridge.retainedSource source
          (CodeDUpdatedArithmeticABI.candidateWeights source coeff lambda)) := by
  obtain ⟨C,d,hC⟩ := uniform_clock
  refine ⟨C,d,?_⟩
  intro q source coeff lambda hsize hmin hnonneg
  obtain ⟨t,ht,v,hr⟩ := branch_run source coeff lambda hsize hmin hnonneg
  refine ⟨t,ht.trans (hC source coeff lambda hsize hmin),?_,?_⟩
  · exact congrArg TM2.Cfg.l hr
  · have hout := congrArg (fun c => c.stk (core (low 24))) hr
    simpa only [Function.update_self] using hout

#print axioms uniform_clock
#print axioms uniform_run
end CurrentAdditive.RatioBranchPolynomial
