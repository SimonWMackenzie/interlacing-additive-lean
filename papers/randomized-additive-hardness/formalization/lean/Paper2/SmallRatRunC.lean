import Paper2.SmallRatRunB

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384

namespace SmallRatProg

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open BitMachineRawSequence (leftLabel)

/-- The 19-part arithmetic program has one actual run, including all 18 handoff steps. -/
theorem rat_run (n a am bd b6 s w L Q : ℕ) :
    ∃ t ≤ ratBd n a am bd b6 s w L Q,
      ((advance ratProg)^[t])
        (⟨some ratStart, ratCtl, B0 n a am bd b6 s w L Q⟩ : TM2.Cfg (fun _ : AK => Bool) _ _) =
      ⟨none, ratCtl, B19 n a am bd b6 s w L Q⟩ := by
  obtain ⟨u12, hu12, g12⟩ := run12 n a am bd b6 s w L Q
  have h13 : ((advance P13)^[1])
      (⟨some (), false, B12 n a am bd b6 s w L Q⟩ : TM2.Cfg (fun _ : AK => Bool) _ _) =
      ⟨none, false, B13 n a am bd b6 s w L Q⟩ :=
    pushS (Sum.inr 12 : AK) 1 (B12 n a am bd b6 s w L Q) false (by bsimp)
  obtain ⟨t14, ht14, h14⟩ := powS c14 hc14 (B13 n a am bd b6 s w L Q) L
    (by bsimp) (by bsimp) (by bsimp) (by bsimp)
  change ((advance P14)^[t14])
      (⟨some (Sum.inr false : MatrixUnaryPower.Label),
        (((false, false), none) : MatrixUnaryPower.Control), B13 n a am bd b6 s w L Q⟩ :
        TM2.Cfg (fun _ : AK => Bool) _ _) =
      ⟨none, (((false, false), none) : MatrixUnaryPower.Control),
        B14 n a am bd b6 s w L Q⟩ at h14
  have h15 : ((advance P15)^[1])
      (⟨some (), false, B14 n a am bd b6 s w L Q⟩ : TM2.Cfg (fun _ : AK => Bool) _ _) =
      ⟨none, false, B15 n a am bd b6 s w L Q⟩ :=
    pushS (Sum.inr 14 : AK) 10 (B14 n a am bd b6 s w L Q) false (by bsimp)
  have h16 : ((advance P16)^[MatrixAddressMachine.exactTime 10 L 0])
      (⟨some MatrixAddressMachine.Label.outer, false, B15 n a am bd b6 s w L Q⟩ :
        TM2.Cfg (fun _ : AK => Bool) _ _) =
      ⟨none, false, B16 n a am bd b6 s w L Q⟩ :=
    mulS c16 hc16 (B15 n a am bd b6 s w L Q) 10 L
      (by bsimp) (by bsimp) (by bsimp) (by bsimp) (by bsimp) (by bsimp)
  obtain ⟨t17, ht17, h17⟩ := powS c17 hc17 (B16 n a am bd b6 s w L Q) (10 * L)
    (by bsimp) (by bsimp) (by bsimp) (by bsimp)
  change ((advance P17)^[t17])
      (⟨some (Sum.inr false : MatrixUnaryPower.Label),
        (((false, false), none) : MatrixUnaryPower.Control), B16 n a am bd b6 s w L Q⟩ :
        TM2.Cfg (fun _ : AK => Bool) _ _) =
      ⟨none, (((false, false), none) : MatrixUnaryPower.Control),
        B17 n a am bd b6 s w L Q⟩ at h17
  have h18 : ((advance P18)^[1])
      (⟨some (), false, B17 n a am bd b6 s w L Q⟩ : TM2.Cfg (fun _ : AK => Bool) _ _) =
      ⟨none, false, B18 n a am bd b6 s w L Q⟩ :=
    pushS (Sum.inr 17 : AK) 320 (B17 n a am bd b6 s w L Q) false (by bsimp)
  have h19 : ((advance P19)^[MatrixAddressMachine.exactTime 320 Q 0])
      (⟨some MatrixAddressMachine.Label.outer, false, B18 n a am bd b6 s w L Q⟩ :
        TM2.Cfg (fun _ : AK => Bool) _ _) =
      ⟨none, false, B19 n a am bd b6 s w L Q⟩ :=
    mulS c19 hc19 (B18 n a am bd b6 s w L Q) 320 Q
      (by bsimp) (by bsimp) (by bsimp) (by bsimp) (by bsimp) (by bsimp)
  obtain ⟨u13, hu13, g13⟩ := BitMachineRawSequence.runs T12 P13
    start12 () K12 K12 false false
    (B0 n a am bd b6 s w L Q) (B12 n a am bd b6 s w L Q)
    (B13 n a am bd b6 s w L Q) u12 1 g12 h13
  obtain ⟨u14, hu14, g14⟩ := BitMachineRawSequence.runs T13 P14
    (leftLabel start12) (Sum.inr false : MatrixUnaryPower.Label) K13 K13
    (((false, false), none) : MatrixUnaryPower.Control)
    (((false, false), none) : MatrixUnaryPower.Control)
    (B0 n a am bd b6 s w L Q) (B13 n a am bd b6 s w L Q)
    (B14 n a am bd b6 s w L Q) u13 t14 g13 h14
  obtain ⟨u15, hu15, g15⟩ := BitMachineRawSequence.runs T14 P15
    (leftLabel (leftLabel start12)) () K14 K14 false false
    (B0 n a am bd b6 s w L Q) (B14 n a am bd b6 s w L Q)
    (B15 n a am bd b6 s w L Q) u14 1 g14 h15
  obtain ⟨u16, hu16, g16⟩ := BitMachineRawSequence.runs T15 P16
    (leftLabel (leftLabel (leftLabel start12))) MatrixAddressMachine.Label.outer
    K15 K15 false false
    (B0 n a am bd b6 s w L Q) (B15 n a am bd b6 s w L Q)
    (B16 n a am bd b6 s w L Q) u15 _ g15 h16
  obtain ⟨u17, hu17, g17⟩ := BitMachineRawSequence.runs T16 P17
    (leftLabel (leftLabel (leftLabel (leftLabel start12))))
    (Sum.inr false : MatrixUnaryPower.Label) K16 K16
    (((false, false), none) : MatrixUnaryPower.Control)
    (((false, false), none) : MatrixUnaryPower.Control)
    (B0 n a am bd b6 s w L Q) (B16 n a am bd b6 s w L Q)
    (B17 n a am bd b6 s w L Q) u16 t17 g16 h17
  obtain ⟨u18, hu18, g18⟩ := BitMachineRawSequence.runs T17 P18
    (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel start12))))) () K17 K17 false false
    (B0 n a am bd b6 s w L Q) (B17 n a am bd b6 s w L Q)
    (B18 n a am bd b6 s w L Q) u17 1 g17 h18
  obtain ⟨u19, hu19, g19⟩ := BitMachineRawSequence.runs T18 P19
    (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel start12))))))
    MatrixAddressMachine.Label.outer K18 K18 false false
    (B0 n a am bd b6 s w L Q) (B18 n a am bd b6 s w L Q)
    (B19 n a am bd b6 s w L Q) u18 _ g18 h19
  refine ⟨u19, ?_, g19⟩
  unfold ratBd clock12 clock6 at *
  omega

end SmallRatProg

#print axioms SmallRatProg.rat_run
