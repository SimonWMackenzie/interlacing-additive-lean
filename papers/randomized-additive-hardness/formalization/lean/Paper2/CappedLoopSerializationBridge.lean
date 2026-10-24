import Paper2.CappedLoopWideProjection

/-!
Scratch check of the exact source `RecursiveSamplingTape.writeTape` list
against the charged capped machine's direct recursive flat layout.
The source equivalence, not a replacement serializer, is the target.
-/

namespace Paper2.CappedLoop.SerializationBridge

open Paper2.CappedSampler
open Turing EthInapproximability.CurrentPaper.BitMachineEncoding

theorem flatBitTape_get (B R : ℕ)
    (tape : BitTape B R) (j : Fin R) (k : Fin B) :
    (CappedLoop.BlockTransfer.flatBitTape B R tape).get
      ⟨j.val * B + k.val, by
        rw [CappedLoop.BlockTransfer.flatBitTape_length]
        calc
          j.val * B + k.val < j.val * B + B :=
            Nat.add_lt_add_left k.isLt _
          _ = (j.val + 1) * B := by ring
          _ ≤ R * B := Nat.mul_le_mul_right B (Nat.succ_le_of_lt j.isLt)
          _ = B * R := by ring⟩ =
      (Paper2.RecursiveSamplingTape.attemptsEquiv B R tape) j k := by
  induction R with
  | zero => exact j.elim0
  | succ R ih =>
      induction j using Fin.cases with
      | zero =>
          simp only [CappedLoop.BlockTransfer.flatBitTape,
            Fin.val_zero, zero_mul, zero_add]
          simp only [List.get_eq_getElem]
          rw [List.getElem_append_left (by simp),
            List.getElem_ofFn]
          change tape.1 k =
            ((Fin.cons tape.1
              (Paper2.RecursiveSamplingTape.attemptsEquiv B R tape.2) :
                Fin (R + 1) → Fin B → Bool) 0) k
          simp
      | succ j =>
          simp only [CappedLoop.BlockTransfer.flatBitTape, Fin.val_succ]
          simp only [List.get_eq_getElem]
          rw [List.getElem_append_right (by
            simp only [List.length_ofFn]
            nlinarith)]
          have hindex : (j.val + 1) * B + k.val - B =
              j.val * B + k.val := by
                simp only [Nat.add_mul, one_mul]
                omega
          simp only [List.length_ofFn, hindex]
          simpa [Paper2.RecursiveSamplingTape.attemptsEquiv,
            Fin.consEquiv] using ih tape.2 j

theorem flatAdaptiveTape_get (B R N : ℕ)
    (tape : Adaptive.Tape B R N) (i : Fin N) (j : Fin R) (k : Fin B) :
    (CappedLoop.WideProjection.flatAdaptiveTape B R N tape).get
      ⟨(i.val * R + j.val) * B + k.val, by
        rw [CappedLoop.WideProjection.flatAdaptiveTape_length]
        simpa [Paper2.RecursiveSamplingTape.positionEquiv_val] using
          (Paper2.RecursiveSamplingTape.positionEquiv B R N (i,j,k)).isLt⟩ =
      Paper2.RecursiveSamplingTape.arrayEquiv B R N tape i j k := by
  induction N with
  | zero => exact i.elim0
  | succ N ih =>
      induction i using Fin.cases with
      | zero =>
          have hbound : j.val * B + k.val < B * R := by
            calc
              j.val * B + k.val < j.val * B + B :=
                Nat.add_lt_add_left k.isLt _
              _ = (j.val + 1) * B := by ring
              _ ≤ R * B := Nat.mul_le_mul_right B
                (Nat.succ_le_of_lt j.isLt)
              _ = B * R := by ring
          simp only [CappedLoop.WideProjection.flatAdaptiveTape,
            Fin.val_zero, zero_mul, zero_add, List.get_eq_getElem]
          rw [List.getElem_append_left (by
            rw [CappedLoop.BlockTransfer.flatBitTape_length]
            exact hbound)]
          change (CappedLoop.BlockTransfer.flatBitTape B R tape.1).get
            ⟨j.val * B + k.val, by
              rw [CappedLoop.BlockTransfer.flatBitTape_length]
              exact hbound⟩ =
            (Paper2.RecursiveSamplingTape.attemptsEquiv B R tape.1) j k
          exact flatBitTape_get B R tape.1 j k
      | succ i =>
          simp only [CappedLoop.WideProjection.flatAdaptiveTape,
            Fin.val_succ, List.get_eq_getElem]
          rw [List.getElem_append_right (by
            rw [CappedLoop.BlockTransfer.flatBitTape_length]
            simp only [Nat.add_mul, one_mul]
            rw [Nat.mul_comm B R]
            omega)]
          have hindex : ((i.val + 1) * R + j.val) * B + k.val - B * R =
              (i.val * R + j.val) * B + k.val := by
            simp only [Nat.add_mul, one_mul]
            rw [Nat.mul_comm B R]
            omega
          simp only [CappedLoop.BlockTransfer.flatBitTape_length, hindex]
          change (CappedLoop.WideProjection.flatAdaptiveTape B R N tape.2).get
            ⟨(i.val * R + j.val) * B + k.val, by
              rw [CappedLoop.WideProjection.flatAdaptiveTape_length]
              simpa [Paper2.RecursiveSamplingTape.positionEquiv_val] using
                (Paper2.RecursiveSamplingTape.positionEquiv B R N
                  (i,j,k)).isLt⟩ =
            Paper2.RecursiveSamplingTape.arrayEquiv B R N tape.2 i j k
          exact ih tape.2 i

theorem flatEquiv_position (B R N : ℕ) (tape : Adaptive.Tape B R N)
    (i : Fin N) (j : Fin R) (k : Fin B) :
    (Paper2.RecursiveSamplingTape.flatEquiv B R N tape)
      (Paper2.RecursiveSamplingTape.positionEquiv B R N (i,j,k)) =
      Paper2.RecursiveSamplingTape.arrayEquiv B R N tape i j k := by
  simp [Paper2.RecursiveSamplingTape.flatEquiv]

theorem flatAdaptiveTape_eq_writeTape (B R N : ℕ)
    (tape : Adaptive.Tape B R N) :
    CappedLoop.WideProjection.flatAdaptiveTape B R N tape =
      (Paper2.RecursiveSamplingTape.writeTape B R N tape).val := by
  apply List.ext_getElem (by
    rw [CappedLoop.WideProjection.flatAdaptiveTape_length]
    exact (Paper2.RecursiveSamplingTape.writeTape_length B R N tape).symm)
  intro z hz1 hz2
  let pos : Fin (Paper2.RecursiveSamplingTape.bitCount B R N) :=
    ⟨z, by simpa [CappedLoop.WideProjection.flatAdaptiveTape_length]
      using hz1⟩
  let ijk := (Paper2.RecursiveSamplingTape.positionEquiv B R N).symm pos
  have hpos0 : Paper2.RecursiveSamplingTape.positionEquiv B R N ijk = pos :=
    (Paper2.RecursiveSamplingTape.positionEquiv B R N).apply_symm_apply pos
  obtain ⟨i, j, k⟩ := ijk
  have hpos : Paper2.RecursiveSamplingTape.positionEquiv B R N (i,j,k) = pos :=
    hpos0
  have hval : (i.val * R + j.val) * B + k.val = z := by
    have hv := congrArg Fin.val hpos
    simpa [Paper2.RecursiveSamplingTape.positionEquiv_val, pos] using hv
  have hflat := flatAdaptiveTape_get B R N tape i j k
  have hsource := Paper2.RecursiveSamplingTape.readTape_bit B R N
    (Paper2.RecursiveSamplingTape.writeTape B R N tape) i j k
  rw [Paper2.RecursiveSamplingTape.readTape_writeTape] at hsource
  have hboth := hflat.trans hsource
  simpa [List.Vector.get, List.get_eq_getElem,
    Paper2.RecursiveSamplingTape.positionEquiv_val, hval] using hboth


/-- The charged wide capped draw now starts from the exact existing source
serialization, not merely a separately defined list of equal length. -/
theorem next_draw_writeTape (D B R N : ℕ) (hD : 0 < D)
    (hB : Nat.clog 2 D ≤ B)
    (tape : Adaptive.Tape B R (N + 1)) :
    ∃ t c,
      t ≤ R * (2 * B + Nat.clog 2 D + 6) + 3 +
        (D - 1 + (B - Nat.clog 2 D) + 2) +
        (R * (CappedLoop.Comparator.attemptBound D +
          (2 * Nat.clog 2 D + 3)) + 3) + 2 ∧
      ((advance CappedLoop.WideProjection.wideProgram)^[t])
        (⟨some (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
            (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
              CappedLoop.WideProjection.Label.start)),
          (((none, false), (none, false)), ((none, false), (none, false))),
          CappedLoop.WideProjection.bank
            (Paper2.RecursiveSamplingTape.writeTape B R (N + 1) tape).val
            (List.replicate (Nat.clog 2 D) true) [] []
            (List.replicate (B - Nat.clog 2 D) true)
            (List.replicate R true) [] [] (List.replicate (D - 1) true) []⟩ :
          Turing.TM2.Cfg (fun _ : Fin 10 => Bool)
            (EthInapproximability.CurrentPaper.BitMachineRawSequence.Label
              (EthInapproximability.CurrentPaper.BitMachineRawSequence.Label
                CappedLoop.WideProjection.Label CappedLoop.WideProjection.Prepare.Label)
              (EthInapproximability.CurrentPaper.BitMachineRawSequence.Label
                CappedLoop.Comparator.Label CappedLoop.Drain.Label))
            (EthInapproximability.CurrentPaper.BitMachineRawSequence.Control
              (EthInapproximability.CurrentPaper.BitMachineRawSequence.Control
                CappedLoop.WideProjection.Control CappedLoop.WideProjection.Control)
              (EthInapproximability.CurrentPaper.BitMachineRawSequence.Control
                CappedLoop.Comparator.Control CappedLoop.Drain.Control))) = c ∧
      c.l = none ∧
      c.stk 0 = (Paper2.RecursiveSamplingTape.writeTape B R N tape.2).val ∧
      (if (c.stk 9).head? = some true then some (c.stk 9).tail.length
        else none) =
        (CappedSampler.runWideBits D B R hB tape.1).map Fin.val := by
  simpa [← flatAdaptiveTape_eq_writeTape] using
    CappedLoop.WideProjection.next_draw_framed D B R N hD hB tape


end Paper2.CappedLoop.SerializationBridge
