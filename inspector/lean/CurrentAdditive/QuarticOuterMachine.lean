import CurrentAdditive.QuarticOuterRun
import EthInapproximability.CurrentPaper.BitMachineBankWrapper
import Paper2.BrFin

/-! The fixed outer stack program as a one-tape bit machine. -/

namespace Paper2.CurrentAdditive.QuarticOuterMachine

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2 Paper2.A3Assembly
open Paper2.CurrentAdditive.QuarticFrontLift
open Paper2.CurrentAdditive.QuarticOuterOutput

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
set_option synthInstance.maxSize 65536
set_option synthInstance.maxHeartbeats 4000000

def cutQ (Δ : ℕ) (γ : ℚ) := QuarticOuterRun.outerProgram Δ γ
def cutStart (Δ : ℕ) (γ : ℚ) : Paper2.ABridge.labelT (cutQ Δ γ) :=
  .inl (.inl (QuarticFrontLift.startLabel Δ γ))
def cutCtl0 (Δ : ℕ) (γ : ℚ) : Paper2.ABridge.ctlT (cutQ Δ γ) :=
  ((QuarticFrontLift.initialControl,
    (((SamplerParameterJoin.startControl, (false, false)),
      (none, ())), ((), none))), (none, none))

set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 4000000 in
instance instCutLabel (Δ : ℕ) (γ : ℚ) :
    Fintype (Paper2.ABridge.labelT (cutQ Δ γ)) := by
  unfold Paper2.ABridge.labelT; infer_instance

set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 4000000 in
instance instCutCtl (Δ : ℕ) (γ : ℚ) :
    Fintype (Paper2.ABridge.ctlT (cutQ Δ γ)) := by
  unfold Paper2.ABridge.ctlT; infer_instance

def cutWrapper (Δ : ℕ) (γ : ℚ) : BitMachine.Machine :=
  @BitMachineBankWrapper.machine ((Lift.a FS + 3) + 3) _ _
    (instCutLabel Δ γ) (instCutCtl Δ γ)
    (cutQ Δ γ) (cutStart Δ γ) (cutCtl0 Δ γ)

def cutMachine (Δ : ℕ) (γ : ℚ) : BitMachine.Machine :=
  BitMachineComposition.composition (Unit4Post.Pre.machine (Lift.a FS + 3))
    (BitMachineComposition.composition (cutWrapper Δ γ)
      (Unit4Post.Drop.machine (Lift.a FS + 3)))

def cutClock (X Y : Fin 3 → List Bool) (budget : ℕ) : ℕ :=
  (Lift.a FS + 3 + 1) +
    2 * (Lift.a FS + 3 + (BitMachineBankCodec.encode X).length) + 2 +
    (((2 * ((Lift.a FS + 3) + 3) + 1) *
        ((Lift.a FS + 3 + (BitMachineBankCodec.encode X).length) + 1) +
      budget +
      2 * ((BitMachineBankCodec.encode Y).length + (Lift.a FS + 3)) + 4) +
     2 * ((BitMachineBankCodec.encode Y).length + (Lift.a FS + 3)) + 2 +
     (2 * (BitMachineBankCodec.encode Y).length + 2 * (Lift.a FS + 3) + 3))

theorem machine_outputs_given_run (Δ : ℕ) (γ : ℚ)
    (X Y : Fin 3 → List Bool) (budget : ℕ)
    (hRun : ∃ t ≤ budget, ∃ v,
      ((advance (cutQ Δ γ))^[t])
        (⟨some (cutStart Δ γ), cutCtl0 Δ γ,
          Wrap.widen (Lift.a FS + 3) X⟩ : TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, v, outputBank Y⟩) :
    (cutMachine Δ γ).OutputsWithin
      (BitMachineBankCodec.encode X) (BitMachineBankCodec.encode Y)
      (cutClock X Y budget) := by
  obtain ⟨t, ht, v, hr⟩ := hRun
  have hpre := Unit4Post.Pre.outputs (Lift.a FS + 3) (BitMachineBankCodec.encode X)
  rw [← Wrap.encode_widen] at hpre
  have hwrap := @BitMachineBankWrapper.outputs ((Lift.a FS + 3) + 3) _ _
    (instCutLabel Δ γ) (instCutCtl Δ γ)
    (cutQ Δ γ) (cutStart Δ γ) (cutCtl0 Δ γ)
    (fun _ => outputBank Y)
    (BitMachineBankCodec.encode (Wrap.widen (Lift.a FS + 3) X))
    budget ((BitMachineBankCodec.encode Y).length + (Lift.a FS + 3))
    (by
      intro S hd
      rw [BitMachineBankCodec.decode_encode] at hd
      cases Option.some.inj hd
      exact ⟨t, _, ht, hr, rfl, rfl⟩)
    (by
      intro S _
      rw [encode_outputBank, List.length_append, List.length_replicate])
  have hres : BitMachineBankWrapper.result (fun _ => outputBank Y)
      (BitMachineBankCodec.encode (Wrap.widen (Lift.a FS + 3) X)) =
      BitMachineBankCodec.encode Y ++ List.replicate (Lift.a FS + 3) false := by
    simp only [BitMachineBankWrapper.result, BitMachineBankCodec.decode_encode,
      encode_outputBank]
  rw [hres] at hwrap
  have hdrop := Unit4Post.Drop.outputs (Lift.a FS + 3)
    (BitMachineBankCodec.encode Y)
  have h23 := BitMachineComposition.composition_outputsWithin _ _ hwrap hdrop
  have h123 := BitMachineComposition.composition_outputsWithin _ _ hpre h23
  apply BitMachine.outputsWithin_mono _ h123
  have hlen : (BitMachineBankCodec.encode
      (Wrap.widen (Lift.a FS + 3) X)).length =
      Lift.a FS + 3 + (BitMachineBankCodec.encode X).length := by
    rw [Wrap.encode_widen, List.length_append, List.length_replicate]
  rw [hlen, List.length_append, List.length_replicate]
  unfold cutClock
  omega

def localBudget (g : EncodedGraph.Graph) (Δ : ℕ) (γ : ℚ)
    (k : ℕ) (raw : List Bool) (B : FS → List Bool)
    (H : SamplerParameterBank.Stack → List Bool) : ℕ :=
  QuarticFrontLift.clock g Δ γ k (FullFront.X0 g k raw) B +
    QuarticRawPrefixCutter.clock g.vertices g.edges.length
      (Nat.clog 2 g.vertices) Δ γ k raw + 1 +
    3 * (2 * (BitMachineBankCodec.encode
      (outerBank (QuarticCutOutputCopies.postBank g Δ γ k raw B H))).length + 3) + 1 +
    (Lift.a FS + 3) * ((BitMachineBankCodec.encode
      (CopyAll.done copies 3 (outerBank
        (QuarticCutOutputCopies.postBank g Δ γ k raw B H)))).length + 1) + 1 + 2

theorem cut_machine_outputs (g : EncodedGraph.Graph) (hg : g.Valid)
    (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hn : 0 < g.vertices) (hm : 0 < g.edges.length)
    (k : ℕ) (raw : List Bool) :
    let X := FullFront.X0 g k raw
    let Y := QuarticCutOutputCopies.outPacket g k
      (raw.take (QuarticCutCount.count27 g.vertices g.edges.length
        (Nat.clog 2 g.vertices) Δ γ k))
    ∃ B : FS → List Bool, ∃ H : SamplerParameterBank.Stack → List Bool,
      (cutMachine Δ γ).OutputsWithin
        (BitMachineBankCodec.encode X) (BitMachineBankCodec.encode Y)
        (cutClock X Y (localBudget g Δ γ k raw B H)) := by
  intro X Y
  obtain ⟨t, B, H, ht, v, hr⟩ :=
    QuarticOuterRun.local_run g hg Δ γ hγ hΔ hn hm k raw
  refine ⟨B, H, ?_⟩
  apply machine_outputs_given_run Δ γ X Y (localBudget g Δ γ k raw B H)
  exact ⟨t, by simpa only [localBudget] using ht, v, by
    simpa only [cutQ, cutStart, cutCtl0] using hr⟩

#print axioms machine_outputs_given_run
#print axioms cut_machine_outputs

end
end Paper2.CurrentAdditive.QuarticOuterMachine
