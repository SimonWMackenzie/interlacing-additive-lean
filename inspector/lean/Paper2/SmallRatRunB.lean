import Paper2.SmallRatRunA

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384

namespace SmallRatProg

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open BitMachineRawSequence (leftLabel)

def clock12 (n a am bd b6 s w L Q : ℕ) : ℕ :=
  clock6 n a am bd b6 s w L Q + 1 +
  MatrixAddressMachine.exactTime 65536 s 0 +
  MatrixAddressMachine.exactTime (65536 * s)
    (max (max (a * am) (a * (bd * n))) (b6 * am)) 0 + 1 +
  MatrixAddressMachine.exactTime 16 w 0 +
  MatrixAddressMachine.exactTime
    (65536 * s * max (max (a * am) (a * (bd * n))) (b6 * am)) (16 * w) 0 + 6

def start12 := labelOfP T12
  (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel
    (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel MatrixAddressMachine.Label.outer)))))))))))

theorem run12 (n a am bd b6 s w L Q : ℕ) :
    ∃ t ≤ clock12 n a am bd b6 s w L Q,
      ((advance T12)^[t])
        (⟨some start12, K12, B0 n a am bd b6 s w L Q⟩ : TM2.Cfg (fun _ : AK => Bool) _ _) =
      ⟨none, K12, B12 n a am bd b6 s w L Q⟩ := by
  obtain ⟨u6, hu6, g6⟩ := run6 n a am bd b6 s w L Q
  have h7 : ((advance P7)^[1])
      (⟨some (), false, B6 n a am bd b6 s w L Q⟩ : TM2.Cfg (fun _ : AK => Bool) _ _) =
      ⟨none, false, B7 n a am bd b6 s w L Q⟩ :=
    pushS (Sum.inr 6 : AK) 65536 (B6 n a am bd b6 s w L Q) false (by bsimp)
  have h8 : ((advance P8)^[MatrixAddressMachine.exactTime 65536 s 0])
      (⟨some MatrixAddressMachine.Label.outer, false, B7 n a am bd b6 s w L Q⟩ :
        TM2.Cfg (fun _ : AK => Bool) _ _) =
      ⟨none, false, B8 n a am bd b6 s w L Q⟩ :=
    mulS c8 hc8 (B7 n a am bd b6 s w L Q) 65536 s
      (by bsimp) (by bsimp) (by bsimp) (by bsimp) (by bsimp) (by bsimp)
  have h9 : ((advance P9)^[MatrixAddressMachine.exactTime (65536 * s)
      (max (max (a * am) (a * (bd * n))) (b6 * am)) 0])
      (⟨some MatrixAddressMachine.Label.outer, false, B8 n a am bd b6 s w L Q⟩ :
        TM2.Cfg (fun _ : AK => Bool) _ _) =
      ⟨none, false, B9 n a am bd b6 s w L Q⟩ :=
    mulS c9 hc9 (B8 n a am bd b6 s w L Q) (65536 * s)
      (max (max (a * am) (a * (bd * n))) (b6 * am))
      (by bsimp) (by bsimp) (by bsimp) (by bsimp) (by bsimp) (by bsimp)
  have h10 : ((advance P10)^[1])
      (⟨some (), false, B9 n a am bd b6 s w L Q⟩ : TM2.Cfg (fun _ : AK => Bool) _ _) =
      ⟨none, false, B10 n a am bd b6 s w L Q⟩ :=
    pushS (Sum.inr 9 : AK) 16 (B9 n a am bd b6 s w L Q) false (by bsimp)
  have h11 : ((advance P11)^[MatrixAddressMachine.exactTime 16 w 0])
      (⟨some MatrixAddressMachine.Label.outer, false, B10 n a am bd b6 s w L Q⟩ :
        TM2.Cfg (fun _ : AK => Bool) _ _) =
      ⟨none, false, B11 n a am bd b6 s w L Q⟩ :=
    mulS c11 hc11 (B10 n a am bd b6 s w L Q) 16 w
      (by bsimp) (by bsimp) (by bsimp) (by bsimp) (by bsimp) (by bsimp)
  have h12 : ((advance P12)^[MatrixAddressMachine.exactTime
      (65536 * s * max (max (a * am) (a * (bd * n))) (b6 * am)) (16 * w) 0])
      (⟨some MatrixAddressMachine.Label.outer, false, B11 n a am bd b6 s w L Q⟩ :
        TM2.Cfg (fun _ : AK => Bool) _ _) =
      ⟨none, false, B12 n a am bd b6 s w L Q⟩ :=
    mulS c12 hc12 (B11 n a am bd b6 s w L Q)
      (65536 * s * max (max (a * am) (a * (bd * n))) (b6 * am)) (16 * w)
      (by bsimp) (by bsimp) (by bsimp) (by bsimp) (by bsimp) (by bsimp)
  obtain ⟨u7, hu7, g7⟩ := BitMachineRawSequence.runs T6 P7 start6 () K6 K6 false false
    (B0 n a am bd b6 s w L Q) (B6 n a am bd b6 s w L Q)
    (B7 n a am bd b6 s w L Q) u6 1 g6 h7
  obtain ⟨u8, hu8, g8⟩ := BitMachineRawSequence.runs T7 P8
    (leftLabel start6) MatrixAddressMachine.Label.outer K7 K7 false false
    (B0 n a am bd b6 s w L Q) (B7 n a am bd b6 s w L Q)
    (B8 n a am bd b6 s w L Q) u7 _ g7 h8
  obtain ⟨u9, hu9, g9⟩ := BitMachineRawSequence.runs T8 P9
    (leftLabel (leftLabel start6)) MatrixAddressMachine.Label.outer K8 K8 false false
    (B0 n a am bd b6 s w L Q) (B8 n a am bd b6 s w L Q)
    (B9 n a am bd b6 s w L Q) u8 _ g8 h9
  obtain ⟨u10, hu10, g10⟩ := BitMachineRawSequence.runs T9 P10
    (leftLabel (leftLabel (leftLabel start6))) () K9 K9 false false
    (B0 n a am bd b6 s w L Q) (B9 n a am bd b6 s w L Q)
    (B10 n a am bd b6 s w L Q) u9 1 g9 h10
  obtain ⟨u11, hu11, g11⟩ := BitMachineRawSequence.runs T10 P11
    (leftLabel (leftLabel (leftLabel (leftLabel start6))))
    MatrixAddressMachine.Label.outer K10 K10 false false
    (B0 n a am bd b6 s w L Q) (B10 n a am bd b6 s w L Q)
    (B11 n a am bd b6 s w L Q) u10 _ g10 h11
  obtain ⟨u12, hu12, g12⟩ := BitMachineRawSequence.runs T11 P12
    (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel start6)))))
    MatrixAddressMachine.Label.outer K11 K11 false false
    (B0 n a am bd b6 s w L Q) (B11 n a am bd b6 s w L Q)
    (B12 n a am bd b6 s w L Q) u11 _ g11 h12
  refine ⟨u12, ?_, g12⟩
  unfold clock12
  omega

end SmallRatProg

#print axioms SmallRatProg.run12
