import CurrentAdditive.RatioUpdaterPolynomial
import CurrentAdditive.RatioRequestUpdateRun

set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 100
noncomputable section
namespace CurrentAdditive.RatioRequestUpdatePolynomial
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open RatioCanonicalRequests RatioListClockBounds RatioListClockCaps RatioUpdaterItemPolynomial EntryClockPoly

def inputSize {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ) (lambda : ℚ) : Nat :=
  inputLength (records source) (coeffWords coeff) (ratWord lambda)

theorem request_packet_bound {q : Nat} (source : Array ((Fin q → Nat) × ℚ))
    (coeff : Array ℚ) (lambda : ℚ) (hsize : coeff.size=source.size) :
    (CodeDUpdateRequestABI.requestPacketList source coeff lambda).length ≤
      outputCap (inputSize source coeff lambda) := by
  have h := request_prefix_bound (records source) (coeffWords coeff) (records source)
    (ratWord lambda) (fun _ h => h) (le_rfl)
  rw [RatioRequestListSpec.outputAt_all,RatioCanonicalRequests.requests_exact source coeff lambda hsize] at h
  exact h

theorem uniform_clock : ∃ C d : Nat,
    ∀ {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ) (lambda : ℚ)
      (hsize : coeff.size=source.size),
    RatioListPreparation.clock (records source)+
      RatioRequestList.clock (records source) (coeffWords coeff) (ratWord lambda)
        (by simpa [records,coeffWords] using hsize)+1+
      MinimumRatioContext.MachineInvokeFull.uniformBound CodeDUpdateFullPipeline.machine
        (CodeDUpdateRequestABI.requestPacketList source coeff lambda)
        (CodeDUpdateFullPipeline.clock source coeff lambda)+1 ≤
      C*(inputSize source coeff lambda+1)^d := by
  obtain ⟨Cu,du,hu⟩ := RatioUpdaterPolynomial.uniform_update_clock
  let cap (n : Nat) := RatioListPolynomial.fullCap n+
    invokeCap CodeDUpdateFullPipeline.machine (outputCap n) (Cu*(outputCap n+1)^du)+1
  have hp : PolyIn (fun n : Nat => n) cap := by
    have hfull := RatioListPolynomial.fullCap_poly
    have ho : PolyIn (fun n : Nat => n) outputCap := by
      unfold outputCap
      solve_update_poly
    have ht : PolyIn (fun n : Nat => n) (fun n => Cu*(outputCap n+1)^du) := by
      solve_update_poly
    exact (hfull.add (invoke_poly _ CodeDUpdateFullPipeline.machine _ _ ho ht)).add (PolyIn.const 1)
  obtain ⟨C,d,hC⟩ := hp
  refine ⟨C,d,?_⟩
  intro q source coeff lambda hsize
  let L := inputSize source coeff lambda
  have hpacket := request_packet_bound source coeff lambda hsize
  have hupdate := hu source coeff lambda
  have htime : CodeDUpdateFullPipeline.clock source coeff lambda ≤ Cu*(outputCap L+1)^du :=
    hupdate.trans (by gcongr)
  have hinvoke := invoke_le CodeDUpdateFullPipeline.machine
    (CodeDUpdateRequestABI.requestPacketList source coeff lambda)
    (CodeDUpdateFullPipeline.clock source coeff lambda) (outputCap L)
    (Cu*(outputCap L+1)^du) hpacket htime
  have hprep := RatioListPolynomial.prepare_le (records source) (coeffWords coeff) (ratWord lambda)
  have hloop := RatioListPolynomial.request_clock_le (records source) (coeffWords coeff)
    (ratWord lambda) (by simpa [records,coeffWords] using hsize)
  have hfull : RatioListPreparation.clock (records source)+
      RatioRequestList.clock (records source) (coeffWords coeff) (ratWord lambda)
        (by simpa [records,coeffWords] using hsize)+1 ≤ RatioListPolynomial.fullCap L := by
    unfold RatioListPolynomial.fullCap
    dsimp only [L,inputSize] at *
    omega
  exact (show _ ≤ cap L by dsimp only [cap]; omega).trans (hC L)

/-- The same fixed request/update program now has an input-byte polynomial
clock through physical arithmetic, entry rewriting and zero deletion. The
minimum scalar and Gauss vector remain explicit stored inputs. -/
theorem uniform_run : ∃ C d : Nat,
    ∀ {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ) (lambda : ℚ)
      (hsize : coeff.size=source.size)
      (hnonneg : (CodeDUpdatedArithmeticABI.candidateWeights source coeff lambda).all
        (fun w => decide (0 ≤ w)) = true),
    let initial := RatioRequestUpdateRun.frame (RatioRequestFrame.boundary
      (SourceListEncoding.encode (records source)) []
      (SourceListEncoding.encode (coeffWords coeff)) (ratWord lambda) 0 0)
    ∃ t ≤ C*(inputSize source coeff lambda+1)^d,
      let result := ((advance RatioRequestUpdateRun.program)^[t])
        (⟨some RatioRequestUpdateRun.start,RatioRequestUpdateRun.control,initial⟩ :
          TM2.Cfg (fun _ : RatioRequestUpdateRun.WideStack => Bool) _ _)
      result.l = none ∧ result.stk RatioRequestUpdateRun.slots.target =
        CodeDCanonicalSourceV2.encodedSource (CodeDCompactSequentialBridge.retainedSource source
          (CodeDUpdatedArithmeticABI.candidateWeights source coeff lambda)) := by
  obtain ⟨C,d,hC⟩ := uniform_clock
  refine ⟨C,d,?_⟩
  intro q source coeff lambda hsize hnonneg
  dsimp only
  obtain ⟨t,ht,v,hr⟩ := RatioRequestUpdateRun.requests_update source coeff lambda hsize hnonneg
  refine ⟨t,ht.trans (hC source coeff lambda hsize),?_,?_⟩
  · exact congrArg TM2.Cfg.l hr
  · have hout := congrArg (fun c => c.stk RatioRequestUpdateRun.slots.target) hr
    simpa only [Function.update_self] using hout

#print axioms uniform_clock
#print axioms uniform_run
end CurrentAdditive.RatioRequestUpdatePolynomial
