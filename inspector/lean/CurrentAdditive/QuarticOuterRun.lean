import CurrentAdditive.QuarticOuterOutput

/-! Lift the fixed v27 numeric front and raw cutter into a bank with three
output cells, then copy the result and clear the work cells. -/

namespace Paper2.CurrentAdditive.QuarticOuterRun

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2 Paper2.A3Assembly
open Paper2.CurrentAdditive.QuarticFrontLift
open Paper2.CurrentAdditive.QuarticFrontWord
open Paper2.CurrentAdditive.QuarticOuterOutput

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

def lifted (Δ : ℕ) (γ : ℚ) :=
  fun l => stackStmt inC (QuarticFrontCutRun.program Δ γ l)

def tail := BitMachineRawSequence.program (CopyAll.prog copies)
  (ClearAll.prog clearCells) (⟨0, by omega⟩ : Fin (Lift.a FS + 3 + 1))
  none none

def outerProgram (Δ : ℕ) (γ : ℚ) :=
  BitMachineRawSequence.program (lifted Δ γ) tail
    (.inl (.inl (⟨0, by omega⟩ : Fin (3 + 1))))
    (QuarticFrontLift.initialControl,
      (((SamplerParameterJoin.startControl, (false, false)), (none, ())), ((), none)))
    (none, none)

theorem local_run (g : EncodedGraph.Graph) (hg : g.Valid)
    (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hn : 0 < g.vertices) (hm : 0 < g.edges.length)
    (k : ℕ) (raw : List Bool) :
    let P := FullFront.X0 g k raw
    let Y := QuarticCutOutputCopies.outPacket g k
      (raw.take (QuarticCutCount.count27 g.vertices g.edges.length
        (Nat.clog 2 g.vertices) Δ γ k))
    ∃ t, ∃ B : FS → List Bool, ∃ H : SamplerParameterBank.Stack → List Bool,
      t ≤ QuarticFrontLift.clock g Δ γ k P B +
        QuarticRawPrefixCutter.clock g.vertices g.edges.length
          (Nat.clog 2 g.vertices) Δ γ k raw + 1 +
        3 * (2 * (BitMachineBankCodec.encode
          (outerBank (QuarticCutOutputCopies.postBank g Δ γ k raw B H))).length + 3) + 1 +
        (Lift.a FS + 3) * ((BitMachineBankCodec.encode
          (CopyAll.done copies 3 (outerBank
            (QuarticCutOutputCopies.postBank g Δ γ k raw B H)))).length + 1) + 1 + 2 ∧
      ∃ v,
      ((advance (outerProgram Δ γ))^[t])
        (⟨some (.inl (.inl (QuarticFrontLift.startLabel Δ γ))),
          ((QuarticFrontLift.initialControl,
            (((SamplerParameterJoin.startControl, (false, false)),
              (none, ())), ((), none))), (none, none)),
          Wrap.widen (Lift.a FS + 3) P⟩ :
          TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, v, outputBank Y⟩ := by
  intro P Y
  obtain ⟨tF, B, H, htF, hrF, hCut, hScratch⟩ :=
    QuarticFrontCutRun.physical_front_cut_run g hg Δ γ hγ hΔ hn hm k raw
  let S := QuarticCutOutputCopies.postBank g Δ γ k raw B H
  have hrF' := BitMachineStackRun.run inC (outerBank (Wrap.widen (Lift.a FS) P))
    (QuarticFrontCutRun.program Δ γ)
    (⟨some (.inl (QuarticFrontLift.startLabel Δ γ)),
      (QuarticFrontLift.initialControl,
        (((SamplerParameterJoin.startControl, (false, false)),
          (none, ())), ((), none))),
      Wrap.widen (Lift.a FS) P⟩ : TM2.Cfg (fun _ : K => Bool) _ _) tF
  rw [hrF] at hrF'
  simp only [stackCfg, outer_pull] at hrF'
  rw [outer_start] at hrF'
  have hSrc : ∀ i : Fin 3, S (QuarticCutOutputCopies.srcC i) = Y i := by
    intro i
    exact QuarticCutOutputCopies.post_sources g Δ γ k raw B H hCut i
  have hScratch' : S QuarticCutOutputCopies.scratchC = [] :=
    QuarticCutOutputCopies.post_scratch g Δ γ k raw B H hScratch
  obtain ⟨tC, htC, vC, hrC⟩ := copy_run S hScratch'
  obtain ⟨tL, htL, vL, hrL⟩ := clear_run S
  rw [cleared_output S Y hSrc] at hrL
  obtain ⟨tTail, htTail, hrTail⟩ := BitMachineRawSequence.runs
    (CopyAll.prog copies) (ClearAll.prog clearCells)
    (.inl (⟨0, by omega⟩ : Fin (3 + 1)))
    (⟨0, by omega⟩ : Fin (Lift.a FS + 3 + 1))
    none vC none vL (outerBank S)
    (CopyAll.done copies 3 (outerBank S)) (outputBank Y)
    tC tL hrC hrL
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (lifted Δ γ) tail
    (.inl (QuarticFrontLift.startLabel Δ γ))
    (.inl (.inl (⟨0, by omega⟩ : Fin (3 + 1))))
    (QuarticFrontLift.initialControl,
      (((SamplerParameterJoin.startControl, (false, false)),
        (none, ())), ((), none)))
    ((QuarticFrontLift.firstCtl, (none : Option Bool)),
      (((SamplerParameterJoin.finalControl, (false, false)),
        (none, ())), ((), none)))
    (none, none) (none, vL)
    (Wrap.widen (Lift.a FS + 3) P) (outerBank S) (outputBank Y)
    tF tTail hrF' (by simpa only [tail] using hrTail)
  refine ⟨t, B, H, ?_, ?_⟩
  · dsimp [S] at htC htL
    change tF ≤ QuarticFrontLift.clock g Δ γ k P B +
      QuarticRawPrefixCutter.clock g.vertices g.edges.length
        (Nat.clog 2 g.vertices) Δ γ k raw + 1 at htF
    omega
  · exact ⟨_, by simpa only [outerProgram, lifted] using hr⟩

#print axioms local_run

end
end Paper2.CurrentAdditive.QuarticOuterRun
