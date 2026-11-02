import CurrentAdditive.QuarticFrontCutCap

/-! Eliminate the cutter's internal bank witnesses from the machine clock by
charging each intermediate encoded bank to physical stack growth. -/

namespace Paper2.CurrentAdditive.QuarticOuterUniform

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2 Paper2.A3Assembly
open Paper2.CurrentAdditive.QuarticFrontLift
open Paper2.CurrentAdditive.QuarticOuterOutput
open Paper2.CurrentAdditive.QuarticOuterEncodedCap
open Paper2.CurrentAdditive.QuarticNumericFront

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 65536

def frontCutCap (g : EncodedGraph.Graph) (Δ : ℕ) (γ : ℚ)
    (k : ℕ) (raw : List Bool) (Z : ℕ) : ℕ :=
  QuarticFrontCapTransfer.timeCoefficient Δ γ * Z +
    QuarticRawPrefixCutter.clock g.vertices g.edges.length
      (Nat.clog 2 g.vertices) Δ γ k raw + 1

def outerInputSize (g : EncodedGraph.Graph) (k : ℕ) (raw : List Bool) : ℕ :=
  (BitMachineBankCodec.encode
    (Wrap.widen (Lift.a FS + 3) (FullFront.X0 g k raw))).length

def outerSizeCap (g : EncodedGraph.Graph) (Δ : ℕ) (γ : ℚ)
    (k : ℕ) (raw : List Bool) (Z : ℕ) : ℕ :=
  frontSizeCap (QuarticOuterRun.lifted Δ γ)
    (outerInputSize g k raw) (frontCutCap g Δ γ k raw Z)

def localCap (g : EncodedGraph.Graph) (Δ : ℕ) (γ : ℚ)
    (k : ℕ) (raw : List Bool) (Z : ℕ) : ℕ :=
  frontCutCap g Δ γ k raw Z +
    copyTimeCap (outerSizeCap g Δ γ k raw Z) +
    (Lift.a FS + 3) *
      (copySizeCap (outerSizeCap g Δ γ k raw Z) + 1) + 3

theorem cut_machine_outputs_uniform (g : EncodedGraph.Graph) (hg : g.Valid)
    (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hn : 0 < g.vertices) (hm : 0 < g.edges.length)
    (k : ℕ) (raw : List Bool) (Z : ℕ) (hZ : 1 ≤ Z)
    (hP : (BitMachineBankCodec.encode (FullFront.X0 g k raw)).length ≤ Z)
    (hRaw : Raw27.clock g Δ γ k raw ≤ Z) :
    let X := FullFront.X0 g k raw
    let Y := QuarticCutOutputCopies.outPacket g k
      (raw.take (QuarticCutCount.count27 g.vertices g.edges.length
        (Nat.clog 2 g.vertices) Δ γ k))
    (QuarticOuterMachine.cutMachine Δ γ).OutputsWithin
        (BitMachineBankCodec.encode X) (BitMachineBankCodec.encode Y)
        (QuarticOuterMachine.cutClock X Y (localCap g Δ γ k raw Z)) := by
  intro X Y
  obtain ⟨tF, B, H, htF, hrF, hCut, hScratch⟩ :=
    QuarticFrontCutCap.physical_front_cut_with_cap g hg Δ γ hγ hΔ hn hm
      k raw Z hZ hP hRaw
  let S := QuarticCutOutputCopies.postBank g Δ γ k raw B H
  have hrF' := BitMachineStackRun.run inC
    (outerBank (Wrap.widen (Lift.a FS) X))
    (QuarticFrontCutRun.program Δ γ)
    (⟨some (.inl (QuarticFrontLift.startLabel Δ γ)),
      (QuarticFrontLift.initialControl,
        (((SamplerParameterJoin.startControl, (false, false)),
          (none, ())), ((), none))),
      Wrap.widen (Lift.a FS) X⟩ : TM2.Cfg (fun _ : K => Bool) _ _) tF
  rw [hrF] at hrF'
  simp only [stackCfg, outer_pull] at hrF'
  rw [outer_start] at hrF'
  have hSrc : ∀ i : Fin 3, S (QuarticCutOutputCopies.srcC i) = Y i := by
    intro i
    exact QuarticCutOutputCopies.post_sources g Δ γ k raw B H hCut i
  have hScratch' : S QuarticCutOutputCopies.scratchC = [] :=
    QuarticCutOutputCopies.post_scratch g Δ γ k raw B H hScratch
  obtain ⟨tC, htC, vC, hrC⟩ := QuarticOuterOutput.copy_run S hScratch'
  obtain ⟨tL, htL, vL, hrL⟩ := QuarticOuterOutput.clear_run S
  rw [cleared_output S Y hSrc] at hrL
  obtain ⟨tTail, htTail, hrTail⟩ := BitMachineRawSequence.runs
    (CopyAll.prog copies) (ClearAll.prog clearCells)
    (.inl (⟨0, by omega⟩ : Fin (3 + 1)))
    (⟨0, by omega⟩ : Fin (Lift.a FS + 3 + 1))
    none vC none vL (outerBank S)
    (CopyAll.done copies 3 (outerBank S)) (outputBank Y)
    tC tL hrC hrL
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (QuarticOuterRun.lifted Δ γ) QuarticOuterRun.tail
    (.inl (QuarticFrontLift.startLabel Δ γ))
    (.inl (.inl (⟨0, by omega⟩ : Fin (3 + 1))))
    (QuarticFrontLift.initialControl,
      (((SamplerParameterJoin.startControl, (false, false)),
        (none, ())), ((), none)))
    ((QuarticFrontLift.firstCtl, (none : Option Bool)),
      (((SamplerParameterJoin.finalControl, (false, false)),
        (none, ())), ((), none)))
    (none, none) (none, vL)
    (Wrap.widen (Lift.a FS + 3) X) (outerBank S) (outputBank Y)
    tF tTail hrF' (by simpa only [QuarticOuterRun.tail] using hrTail)
  have hSize := outer_and_copied_encoded_le
    (QuarticOuterRun.lifted Δ γ)
    (⟨some (.inl (QuarticFrontLift.startLabel Δ γ)),
      (QuarticFrontLift.initialControl,
        (((SamplerParameterJoin.startControl, (false, false)),
          (none, ())), ((), none))),
      Wrap.widen (Lift.a FS + 3) X⟩ : TM2.Cfg (fun _ : J => Bool) _ _)
    S tF (frontCutCap g Δ γ k raw Z) (outerInputSize g k raw) tC
    (by simpa only [QuarticOuterRun.lifted, S,
        QuarticCutOutputCopies.postBank] using congrArg TM2.Cfg.stk hrF')
    (by simpa only [frontCutCap, X] using htF)
    (by rfl)
    (by simpa only [copyTimeCap] using htC)
    (congrArg TM2.Cfg.stk hrC)
  have hBudget : t ≤ localCap g Δ γ k raw Z := by
    obtain ⟨hPost, hCopied⟩ := hSize
    change tL ≤ (Lift.a FS + 3) *
      ((BitMachineBankCodec.encode (CopyAll.done copies 3 (outerBank S))).length + 1) + 1
      at htL
    have hClear := Nat.mul_le_mul_left (Lift.a FS + 3) (Nat.add_le_add_right hCopied 1)
    dsimp [localCap, outerSizeCap, frontCutCap, copyTimeCap] at *
    omega
  apply QuarticOuterMachine.machine_outputs_given_run Δ γ X Y (localCap g Δ γ k raw Z)
  exact ⟨t, hBudget, _, by
    simpa only [QuarticOuterMachine.cutQ, QuarticOuterMachine.cutStart,
      QuarticOuterMachine.cutCtl0, QuarticOuterRun.outerProgram,
      QuarticOuterRun.lifted] using hr⟩

#print axioms cut_machine_outputs_uniform

end
end Paper2.CurrentAdditive.QuarticOuterUniform
