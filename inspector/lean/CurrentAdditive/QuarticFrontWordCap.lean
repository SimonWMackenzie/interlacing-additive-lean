import CurrentAdditive.QuarticFrontCapTransfer
import CurrentAdditive.QuarticFrontWord

namespace Paper2.CurrentAdditive.QuarticFrontWordCap

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.A3Assembly
open Paper2.CurrentAdditive.QuarticFrontLift
open Paper2.CurrentAdditive.QuarticFrontSizeTransfer
open Paper2.CurrentAdditive.QuarticFrontClockArithmetic
open Paper2.CurrentAdditive.QuarticFrontCapTransfer
open Paper2.CurrentAdditive.QuarticFrontWord
open Paper2.CurrentAdditive.QuarticNumericFront

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 65536

theorem physical_word_with_cap (g : EncodedGraph.Graph) (hg : g.Valid)
    (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hn : 0 < g.vertices) (hm : 0 < g.edges.length) (k : ℕ)
    (raw : List Bool)
    (Z : ℕ) (hZ : 1 ≤ Z)
    (hP : (BitMachineBankCodec.encode
      (FullFront.X0 g k raw)).length ≤ Z)
    (hRaw : Raw27.clock g Δ γ k
      raw ≤ Z) :
    let P := FullFront.X0 g k raw
    ∃ T, ∃ v, ∃ B : FS → List Bool,
      T ≤ timeCoefficient Δ γ * Z ∧
      ((advance (program Δ γ))^[T])
        (⟨some (startLabel Δ γ), initialControl,
          Wrap.widen (Lift.a FS) P⟩ :
          TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, v,
          afterMaster P B (startWordBank g Δ γ k raw)⟩ ∧
      B Packet27.scratch = [] := by
  intro P
  obtain ⟨tP, htP, vP, hrP⟩ := packet_copy_run P
  rw [packet_loaded P] at hrP
  obtain ⟨tR, htR, vR, B, hrR, hmaster, hsB⟩ :=
    raw_lift_word g hg Δ γ hγ hΔ hn hm k raw
  obtain ⟨tS, htS, vS, hrS⟩ := so_copy_run P B hsB
  rw [so_done_layout P B _ hmaster] at hrS
  obtain ⟨tPR, htPR, hrPR⟩ := BitMachineRawSequence.runs
    (CopyAll.prog packetCopies) (rawProg Δ γ)
    (.inl ⟨0, by omega⟩) (Raw27.startLabel Δ γ)
    (none : Option Bool) vP Raw27.initialControl
    (Packet27.initialControl, (Tail27.ctlBC, vR))
    (Wrap.widen (Lift.a FS) P) (loaded P) (afterRaw P B)
    tP tR hrP hrR
  obtain ⟨T, hT, hr⟩ := BitMachineRawSequence.runs
    (firstProg Δ γ) (CopyAll.prog soCopies)
    (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩ : CopyAll.Lab 3))
    (.inl ⟨0, by omega⟩)
    firstCtl ((none : Option Bool), (Packet27.initialControl, (Tail27.ctlBC, vR)))
    (none : Option Bool) vS
    (Wrap.widen (Lift.a FS) P) (afterRaw P B)
    (afterMaster P B (startWordBank g Δ γ k raw))
    tPR tS hrPR hrS
  have htPZ : tP ≤ 16 * Z := by
    change tP ≤ 3 * (2 * (BitMachineBankCodec.encode P).length + 3) + 1 at htP
    change (BitMachineBankCodec.encode P).length ≤ Z at hP
    omega
  have hWiden : (BitMachineBankCodec.encode (Wrap.widen (Lift.a FS) P)).length ≤
      (Lift.a FS + 1) * Z := by
    rw [Wrap.encode_widen, List.length_append, List.length_replicate]
    have hFS : Lift.a FS ≤ Lift.a FS * Z := Nat.le_mul_of_pos_right _ hZ
    have h := Nat.add_le_add hFS hP
    simpa [add_mul] using h
  have hLoaded := loaded_size P tP vP hrP
  have hCopyGrowth :
      2 * (Lift.a FS + 3) *
        (BitMachineStackGrowth.perStep (CopyAll.prog packetCopies) * tP) ≤
      (32 * (Lift.a FS + 3) *
        BitMachineStackGrowth.perStep (CopyAll.prog packetCopies)) * Z := by
    calc
      _ = (2 * (Lift.a FS + 3) *
          BitMachineStackGrowth.perStep (CopyAll.prog packetCopies)) * tP := by ring
      _ ≤ (2 * (Lift.a FS + 3) *
          BitMachineStackGrowth.perStep (CopyAll.prog packetCopies)) * (16 * Z) :=
            Nat.mul_le_mul_left _ htPZ
      _ = (32 * (Lift.a FS + 3) *
          BitMachineStackGrowth.perStep (CopyAll.prog packetCopies)) * Z := by ring
  have hLoadedZ : (BitMachineBankCodec.encode (loaded P)).length ≤
      loadCoefficient * Z := by
    calc
      _ ≤ (BitMachineBankCodec.encode (Wrap.widen (Lift.a FS) P)).length +
          2 * (Lift.a FS + 3) *
            (BitMachineStackGrowth.perStep (CopyAll.prog packetCopies) * tP) := hLoaded
      _ ≤ (Lift.a FS + 1) * Z +
          (32 * (Lift.a FS + 3) *
            BitMachineStackGrowth.perStep (CopyAll.prog packetCopies)) * Z :=
              Nat.add_le_add hWiden hCopyGrowth
      _ = loadCoefficient * Z := by unfold loadCoefficient; ring
  have hRawSize := after_raw_size Δ γ P B tR (congrArg TM2.Cfg.stk hrR)
  have htRZ : tR ≤ Z := htR.trans hRaw
  have hRawGrowth :
      2 * (Lift.a FS + 3) *
        (BitMachineStackGrowth.perStep (rawProg Δ γ) * tR) ≤
      (2 * (Lift.a FS + 3) *
        BitMachineStackGrowth.perStep (rawProg Δ γ)) * Z := by
    calc
      _ = (2 * (Lift.a FS + 3) *
          BitMachineStackGrowth.perStep (rawProg Δ γ)) * tR := by ring
      _ ≤ (2 * (Lift.a FS + 3) *
          BitMachineStackGrowth.perStep (rawProg Δ γ)) * Z :=
            Nat.mul_le_mul_left _ htRZ
  have hAfterZ : (BitMachineBankCodec.encode (afterRaw P B)).length ≤
      afterCoefficient Δ γ * Z := by
    calc
      _ ≤ (BitMachineBankCodec.encode (loaded P)).length +
          2 * (Lift.a FS + 3) *
            (BitMachineStackGrowth.perStep (rawProg Δ γ) * tR) := hRawSize
      _ ≤ loadCoefficient * Z +
          (2 * (Lift.a FS + 3) *
            BitMachineStackGrowth.perStep (rawProg Δ γ)) * Z :=
              Nat.add_le_add hLoadedZ hRawGrowth
      _ = afterCoefficient Δ γ * Z := by unfold afterCoefficient; ring
  have hCoeff : 1 ≤ afterCoefficient Δ γ := by
    unfold afterCoefficient loadCoefficient
    omega
  have hZ' : 1 ≤ afterCoefficient Δ γ * Z := by
    exact Nat.mul_pos hCoeff hZ
  have hP' : (BitMachineBankCodec.encode P).length ≤
      afterCoefficient Δ γ * Z :=
    hP.trans (Nat.le_mul_of_pos_left Z hCoeff)
  have hRaw' : Raw27.clock g Δ γ k (P 2) ≤
      afterCoefficient Δ γ * Z :=
    hRaw.trans (Nat.le_mul_of_pos_left Z hCoeff)
  have hClock := front_clock_linear g Δ γ k P B
    (afterCoefficient Δ γ * Z) hZ' hP' hRaw' hAfterZ
  refine ⟨T, (firstCtl, vS), B, ?_, ?_, hsB⟩
  · have hTime : T ≤ clock g Δ γ k P B := by
      change tR ≤ Raw27.clock g Δ γ k (P 2) at htR
      unfold clock copyPacketClock copyMasterClock
      omega
    calc
      T ≤ clock g Δ γ k P B := hTime
      _ ≤ (20 + 5 * Fintype.card SuccessOrient.Stack) *
        (afterCoefficient Δ γ * Z) := hClock
      _ = timeCoefficient Δ γ * Z := by
        unfold timeCoefficient
        ring
  · simpa only [QuarticFrontLift.program, startLabel,
      FullFront.labelOfP, initialControl] using hr


#print axioms physical_word_with_cap

end
end Paper2.CurrentAdditive.QuarticFrontWordCap
