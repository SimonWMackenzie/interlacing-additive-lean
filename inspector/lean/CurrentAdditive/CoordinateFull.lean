import CurrentAdditive.CoordinateClock
import CurrentAdditive.SmallBiasCanonicalSource

namespace CurrentAdditive.FiniteFieldCoordinate

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable
open Paper2.YaoLookup Paper2.YaoSourceCodec
open Paper2.UnaryFieldListParserScratch

/-- The physical address base is exactly the canonical least power of two. -/
theorem paddedEdgeCount_eq_exactAddress (e : ℕ) :
    paddedEdgeCount e = 2 ^ CurrentAdditive.SmallBias.exactAddressBits e := rfl

noncomputable def stageProgram :=
  EthInapproximability.CurrentPaper.MultiMove.program
    (jobs.map EthInapproximability.CurrentPaper.CopyFill.toJob) 36

def stageStart :=
  EthInapproximability.CurrentPaper.MultiMove.startLabel
    (jobs.map EthInapproximability.CurrentPaper.CopyFill.toJob)

noncomputable def posProgram := Paper2.YaoPositionFull.program positionSlots

noncomputable def payloadClearProgram :=
  BitMachineRawSequence.program payloadProgram40 clearProgram 0
    (false, (none : Option Bool)) ((), (none : Option Bool))

noncomputable def widthPayloadClearProgram :=
  BitMachineRawSequence.program widthPush payloadClearProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel MatrixUnaryArithmetic.Label.outer)) ()
    ((false, (none : Option Bool)), ((), (none : Option Bool)))

noncomputable def positionWidthPayloadClearProgram :=
  BitMachineRawSequence.program posProgram widthPayloadClearProgram
    (BitMachineRawSequence.leftLabel ()) Paper2.YaoPositionFull.startControl
    ((), ((false, (none : Option Bool)), ((), (none : Option Bool))))

noncomputable def selectPositionWidthPayloadClearProgram :=
  BitMachineRawSequence.program selectorProgram40 positionWidthPayloadClearProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    ((none, (false, false)), (false, false))
    (Paper2.YaoPositionFull.startControl,
      ((), ((false, (none : Option Bool)), ((), (none : Option Bool)))))

/-- One literal fixed forty-stack program. The only input-dependent data are
the seven source words; its transition table and all stack locations are fixed. -/
noncomputable def payloadCoordProgram :=
  BitMachineRawSequence.program stageProgram selectPositionWidthPayloadClearProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel ())))
    EthInapproximability.CurrentPaper.MultiMove.initial
    ((((none : Option Bool), (false, false)), (false, false)),
      (Paper2.YaoPositionFull.startControl,
        ((), ((false, (none : Option Bool)), ((), (none : Option Bool))))))

abbrev PosControl := Option Bool ×
  (Option Bool × (Option Bool × (Bool × (Option Bool × Option Bool))))
abbrev SelectorControl := (Option Bool × (Bool × Bool)) × (Bool × Bool)
abbrev CoordControl :=
  EthInapproximability.CurrentPaper.MultiMove.Control ×
    (SelectorControl ×
      (PosControl ×
        (Unit × ((Bool × Option Bool) × (Unit × Option Bool)))))

def payloadControl : CoordControl :=
  (EthInapproximability.CurrentPaper.MultiMove.initial,
    (((none, (false, false)), (false, false)),
      (Paper2.YaoPositionFull.startControl,
        ((), ((false, none), ((), none))))))

theorem physical_payload_coord {v e t : ℕ}
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (z : Fin ((paddedEdgeCount e) ^ (2 ^ (t - 1))))
    (g : Fin (2 ^ (t - 1))) (a : Fin (paddedEdgeCount e))
    (vertex : Fin v) (S : Stack → List Bool)
    (hz : S 0 = List.replicate z.val true)
    (hg : S 1 = List.replicate g.val true)
    (hH : S 2 = List.replicate (paddedEdgeCount e) true)
    (ha : S 3 = List.replicate a.val true)
    (hv : S 4 = List.replicate vertex.val true)
    (hbody : S 5 = tokens (List.ofFn (flatten edges)))
    (hK : S 6 = List.replicate (2 ^ t * 2 ^ t) true)
    (hblank : ∀ k : Stack, 7 ≤ k.val → S k = []) :
    ∃ steps ≤ EthInapproximability.CurrentPaper.CopyFill.fillCost jobs S + 1 +
          selectorClock (2 ^ (t - 1)) (paddedEdgeCount e) z.val g.val +
          positionClock t a.val vertex.val (tokens (List.ofFn (flatten edges))) +
          1 + payloadClock (2 ^ t * 2 ^ t)
            (selector (2 ^ (t - 1)) (paddedEdgeCount e) z g).val
            (position (le_paddedEdgeCount e) edges a vertex).val +
          (32 * preclearBound (2 ^ (t - 1)) (paddedEdgeCount e)
            (2 ^ t * 2 ^ t) z.val g.val t a.val vertex.val
            (selector (2 ^ (t - 1)) (paddedEdgeCount e) z g).val
            (position (le_paddedEdgeCount e) edges a vertex).val
            (tokens (List.ofFn (flatten edges))) S + 34) + 5,
        ((advance payloadCoordProgram)^[steps])
          (⟨some (BitMachineRawSequence.leftLabel stageStart), payloadControl, S⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none, payloadControl,
            Function.update S 7 (List.replicate
              ((selector (2 ^ (t - 1)) (paddedEdgeCount e) z g).val *
                ((2 ^ t * 2 ^ t) + 1) +
                (position (le_paddedEdgeCount e) edges a vertex).val) true)⟩ := by
  let H := paddedEdgeCount e
  let q := 2 ^ (t - 1)
  let K := 2 ^ t * 2 ^ t
  let α := selector q H z g
  let p := position (le_paddedEdgeCount e) edges a vertex
  obtain ⟨ts,hts,hs⟩ := selector_run40 q H z g S hz hg hH hblank
  obtain ⟨F,hsel,hα⟩ := hs
  obtain ⟨tp,htp,c',hpos⟩ := position_run40 edges a vertex S F
    ha hv hbody hK hblank
  have hwidth := width_input S F p.val K hK
  have hw := width_run S F p.val K hwidth
  obtain ⟨tm,htm,hm⟩ := payload_run40 H K α p S F hα hblank
  obtain ⟨tc,htc,hc⟩ := clear_run (payloadOutput H K α p S F)
  have hbSel : scratchBound (selected S F) ≤
      scratchBound (staged S) + ts * selectorPushBudget := by
    simpa only [selectorPushBudget] using
      (scratchBound_run selectorProgram40
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel ())),
          ((none, (false, false)), (false, false)), staged S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) ts
        ((none, (false, false)), (false, false)) (selected S F) hsel)
  have hbPos : scratchBound (positioned S F p.val) ≤
      scratchBound (selected S F) + tp * positionPushBudget := by
    simpa only [positionPushBudget, posProgram, positioned] using
      (scratchBound_run (Paper2.YaoPositionFull.program positionSlots)
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          Paper2.YaoPositionFull.startControl, selected S F⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) tp c'
        (positioned S F p.val) (by simpa only [positioned] using hpos))
  have hbWidth : scratchBound (widthReady S F p.val K) ≤
      scratchBound (positioned S F p.val) + widthPushBudget := by
    simpa only [widthPushBudget, Function.iterate_one, Nat.one_mul] using
      (scratchBound_run widthPush
        (⟨some (), (), positioned S F p.val⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Unit Unit) 1 ()
        (widthReady S F p.val K) (by simpa only [Function.iterate_one] using hw))
  have hbPay : scratchBound (payloadOutput H K α p S F) ≤
      scratchBound (widthReady S F p.val K) + tm * payloadPushBudget := by
    simpa only [payloadPushBudget] using
      (scratchBound_run payloadProgram40
        (⟨some (BitMachineRawSequence.leftLabel
          MatrixUnaryArithmetic.Label.outer), (false, none),
          widthReady S F p.val K⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _)
        tm (false, none) (payloadOutput H K α p S F) hm)
  have hpre : scratchBound (payloadOutput H K α p S F) ≤
      preclearBound q H K z.val g.val t a.val vertex.val α.val p.val
        (tokens (List.ofFn (flatten edges))) S := by
    unfold preclearBound
    have hselMul := Nat.mul_le_mul_right selectorPushBudget hts
    have hposMul := Nat.mul_le_mul_right positionPushBudget htp
    have hpayMul := Nat.mul_le_mul_right payloadPushBudget htm
    omega
  -- Compose from the last physical phase to the first. Each handoff is a
  -- literal transition of BitMachineRawSequence, already charged by `runs`.
  obtain ⟨t56,ht56,h56⟩ := BitMachineRawSequence.runs payloadProgram40 clearProgram
    (BitMachineRawSequence.leftLabel MatrixUnaryArithmetic.Label.outer) 0
    (false, none) (false, none) ((), none) ((), none)
    (widthReady S F p.val K) (payloadOutput H K α p S F)
    (BitMachineClearBank.cleared scratchSlots (payloadOutput H K α p S F))
    tm tc hm hc
  obtain ⟨t456,ht456,h456⟩ := BitMachineRawSequence.runs widthPush payloadClearProgram
    () (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel MatrixUnaryArithmetic.Label.outer))
    () () ((false, none), ((), none)) ((false, none), ((), none))
    (positioned S F p.val) (widthReady S F p.val K)
    (BitMachineClearBank.cleared scratchSlots (payloadOutput H K α p S F))
    1 t56 hw (by simpa only [payloadClearProgram] using h56)
  obtain ⟨t3456,ht3456,h3456⟩ := BitMachineRawSequence.runs posProgram widthPayloadClearProgram
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) (BitMachineRawSequence.leftLabel ())
    Paper2.YaoPositionFull.startControl c'
    ((), ((false, none), ((), none)))
    ((), ((false, none), ((), none)))
    (selected S F) (positioned S F p.val)
    (BitMachineClearBank.cleared scratchSlots (payloadOutput H K α p S F))
    tp t456 (by simpa only [posProgram, positionSlots, positioned] using hpos)
      (by simpa only [widthPayloadClearProgram] using h456)
  obtain ⟨t23456,ht23456,h23456⟩ := BitMachineRawSequence.runs
    selectorProgram40 positionWidthPayloadClearProgram
     (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel ()))
     (BitMachineRawSequence.leftLabel
       (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    ((none, (false, false)), (false, false))
    ((none, (false, false)), (false, false))
    (Paper2.YaoPositionFull.startControl,
      ((), ((false, none), ((), none))))
    (Paper2.YaoPositionFull.startControl,
      ((), ((false, none), ((), none))))
    (staged S) (selected S F)
    (BitMachineClearBank.cleared scratchSlots (payloadOutput H K α p S F))
    ts t3456 (by simpa only [selected] using hsel)
      (by simpa only [positionWidthPayloadClearProgram] using h3456)
  obtain ⟨steps,hsteps,hrun⟩ := BitMachineRawSequence.runs
    stageProgram selectPositionWidthPayloadClearProgram
    stageStart (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel ())))
    EthInapproximability.CurrentPaper.MultiMove.initial
    EthInapproximability.CurrentPaper.MultiMove.initial
    (((none, (false, false)), (false, false)),
      (Paper2.YaoPositionFull.startControl,
        ((), ((false, none), ((), none)))))
    (((none, (false, false)), (false, false)),
      (Paper2.YaoPositionFull.startControl,
        ((), ((false, none), ((), none)))))
    S (staged S)
    (BitMachineClearBank.cleared scratchSlots (payloadOutput H K α p S F))
    (EthInapproximability.CurrentPaper.CopyFill.fillCost jobs S + 1) t23456
    (by simpa only [stageProgram] using stage_run S hblank)
    (by simpa only [selectPositionWidthPayloadClearProgram] using h23456)
  refine ⟨steps, ?_, ?_⟩
  · have hclock : steps ≤
        EthInapproximability.CurrentPaper.CopyFill.fillCost jobs S + 1 +
        selectorClock q H z.val g.val +
        positionClock t a.val vertex.val (tokens (List.ofFn (flatten edges))) +
        1 + payloadClock K α.val p.val +
        (32 * preclearBound q H K z.val g.val t a.val vertex.val α.val p.val
          (tokens (List.ofFn (flatten edges))) S + 34) + 5 := by
        have hB := Nat.mul_le_mul_left 32 hpre
        omega
    simpa only [H, q, K, α, p] using hclock
  · simpa only [payloadCoordProgram, payloadControl,
      clear_payload H K α p S F hblank] using hrun

end CurrentAdditive.FiniteFieldCoordinate
