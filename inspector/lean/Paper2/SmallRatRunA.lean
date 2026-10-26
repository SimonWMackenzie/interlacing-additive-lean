import Paper2.SmallRatProg

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384

namespace SmallRatProg

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open BitMachineRawSequence (leftLabel)

def clock6 (n a am bd b6 s w L Q : ℕ) : ℕ :=
  MatrixAddressMachine.exactTime a am 0 +
  MatrixAddressMachine.exactTime bd n 0 +
  MatrixAddressMachine.exactTime a (bd * n) 0 +
  MatrixAddressMachine.exactTime b6 am 0 +
  (max (a * am) (a * (bd * n)) + a * am + a * (bd * n) + 3) +
  (max (max (a * am) (a * (bd * n))) (b6 * am) +
    max (a * am) (a * (bd * n)) + b6 * am + 3) + 5

def start6 := labelOfP T6
  (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel MatrixAddressMachine.Label.outer)))))

theorem run6 (n a am bd b6 s w L Q : ℕ) :
    ∃ t ≤ clock6 n a am bd b6 s w L Q,
      ((advance T6)^[t])
        (⟨some start6, K6, B0 n a am bd b6 s w L Q⟩ : TM2.Cfg (fun _ : AK => Bool) _ _) =
      ⟨none, K6, B6 n a am bd b6 s w L Q⟩ := by
  have h1 : ((advance P1)^[MatrixAddressMachine.exactTime a am 0])
      (⟨some MatrixAddressMachine.Label.outer, false, B0 n a am bd b6 s w L Q⟩ :
        TM2.Cfg (fun _ : AK => Bool) _ _) =
      ⟨none, false, B1 n a am bd b6 s w L Q⟩ :=
    mulS c1 hc1 (B0 n a am bd b6 s w L Q) a am
      (by bsimp) (by bsimp) (by bsimp) (by bsimp) (by bsimp) (by bsimp)
  have h2 : ((advance P2)^[MatrixAddressMachine.exactTime bd n 0])
      (⟨some MatrixAddressMachine.Label.outer, false, B1 n a am bd b6 s w L Q⟩ :
        TM2.Cfg (fun _ : AK => Bool) _ _) =
      ⟨none, false, B2 n a am bd b6 s w L Q⟩ :=
    mulS c2 hc2 (B1 n a am bd b6 s w L Q) bd n
      (by bsimp) (by bsimp) (by bsimp) (by bsimp) (by bsimp) (by bsimp)
  have h3 : ((advance P3)^[MatrixAddressMachine.exactTime a (bd * n) 0])
      (⟨some MatrixAddressMachine.Label.outer, false, B2 n a am bd b6 s w L Q⟩ :
        TM2.Cfg (fun _ : AK => Bool) _ _) =
      ⟨none, false, B3 n a am bd b6 s w L Q⟩ :=
    mulS c3 hc3 (B2 n a am bd b6 s w L Q) a (bd * n)
      (by bsimp) (by bsimp) (by bsimp) (by bsimp) (by bsimp) (by bsimp)
  have h4 : ((advance P4)^[MatrixAddressMachine.exactTime b6 am 0])
      (⟨some MatrixAddressMachine.Label.outer, false, B3 n a am bd b6 s w L Q⟩ :
        TM2.Cfg (fun _ : AK => Bool) _ _) =
      ⟨none, false, B4 n a am bd b6 s w L Q⟩ :=
    mulS c4 hc4 (B3 n a am bd b6 s w L Q) b6 am
      (by bsimp) (by bsimp) (by bsimp) (by bsimp) (by bsimp) (by bsimp)
  have h5 : ((advance P5)^[max (a * am) (a * (bd * n)) + a * am + a * (bd * n) + 3])
      (⟨some ETHParameterScaleMachineMax.Label.scan,
        ((none, none) : ETHParameterScaleMachineMax.Control), B4 n a am bd b6 s w L Q⟩ :
        TM2.Cfg (fun _ : AK => Bool) _ _) =
      ⟨none, ((none, none) : ETHParameterScaleMachineMax.Control), B5 n a am bd b6 s w L Q⟩ :=
    maxS c5 hc5 (B4 n a am bd b6 s w L Q) (a * am) (a * (bd * n))
      (by bsimp) (by bsimp) (by bsimp) (by bsimp) (by bsimp)
  have h6 : ((advance P6)^[max (max (a * am) (a * (bd * n))) (b6 * am) +
      max (a * am) (a * (bd * n)) + b6 * am + 3])
      (⟨some ETHParameterScaleMachineMax.Label.scan,
        ((none, none) : ETHParameterScaleMachineMax.Control), B5 n a am bd b6 s w L Q⟩ :
        TM2.Cfg (fun _ : AK => Bool) _ _) =
      ⟨none, ((none, none) : ETHParameterScaleMachineMax.Control), B6 n a am bd b6 s w L Q⟩ :=
    maxS c6 hc6 (B5 n a am bd b6 s w L Q)
      (max (a * am) (a * (bd * n))) (b6 * am)
      (by bsimp) (by bsimp) (by bsimp) (by bsimp) (by bsimp)
  obtain ⟨u2, hu2, g2⟩ := BitMachineRawSequence.runs P1 P2
    MatrixAddressMachine.Label.outer MatrixAddressMachine.Label.outer
    false false false false (B0 n a am bd b6 s w L Q) (B1 n a am bd b6 s w L Q)
    (B2 n a am bd b6 s w L Q) _ _ h1 h2
  obtain ⟨u3, hu3, g3⟩ := BitMachineRawSequence.runs T2 P3
    (leftLabel MatrixAddressMachine.Label.outer) MatrixAddressMachine.Label.outer
    K2 K2 false false (B0 n a am bd b6 s w L Q) (B2 n a am bd b6 s w L Q)
    (B3 n a am bd b6 s w L Q) u2 _ g2 h3
  obtain ⟨u4, hu4, g4⟩ := BitMachineRawSequence.runs T3 P4
    (leftLabel (leftLabel MatrixAddressMachine.Label.outer)) MatrixAddressMachine.Label.outer
    K3 K3 false false (B0 n a am bd b6 s w L Q) (B3 n a am bd b6 s w L Q)
    (B4 n a am bd b6 s w L Q) u3 _ g3 h4
  obtain ⟨u5, hu5, g5⟩ := BitMachineRawSequence.runs T4 P5
    (leftLabel (leftLabel (leftLabel MatrixAddressMachine.Label.outer)))
    ETHParameterScaleMachineMax.Label.scan K4 K4
    ((none, none) : ETHParameterScaleMachineMax.Control)
    ((none, none) : ETHParameterScaleMachineMax.Control)
    (B0 n a am bd b6 s w L Q) (B4 n a am bd b6 s w L Q)
    (B5 n a am bd b6 s w L Q) u4 _ g4 h5
  obtain ⟨u6, hu6, g6⟩ := BitMachineRawSequence.runs T5 P6
    (leftLabel (leftLabel (leftLabel (leftLabel MatrixAddressMachine.Label.outer))))
    ETHParameterScaleMachineMax.Label.scan K5 K5
    ((none, none) : ETHParameterScaleMachineMax.Control)
    ((none, none) : ETHParameterScaleMachineMax.Control)
    (B0 n a am bd b6 s w L Q) (B5 n a am bd b6 s w L Q)
    (B6 n a am bd b6 s w L Q) u5 _ g5 h6
  refine ⟨u6, ?_, g6⟩
  unfold clock6
  omega

end SmallRatProg

#print axioms SmallRatProg.run6
