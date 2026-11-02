import EthInapproximability.CurrentPaper.VectorsQuery

/-!
# Segment 1: the whole-bank run of the fixed vectors cell program

Lane owner:b-stage4-entry-program-3 (Paper B, unit 2, map item 3).

Imports, frozen and unchanged: the predecessor definitions
`EntryVectorsCell` (owner-2; object checked equal to its current source by
`CheckEntryVectorsCellObject`) and the CHECKED Codex phase contracts
`VectorsPrefix` (P1-P4), `VectorsMiddle` (P5-P8), `VectorsQuery` (P9).
The Codex draft `VectorsLast` is NOT imported: its three phase statements
(P10-P12) are re-proved here under this lane's namespace (the bank
definitions `B10`-`B12` are the draft's text; the P12 proof is repaired).

New here: P13 (the one-step finite-control combine), and the composition of
all thirteen phases with `BitMachineRawSequence.runs` (twelve charged
handoffs), giving ONE run of the literal `EntryVectorsCell.program` from the
writer's cell configuration back to the SAME bank with the answer bit.
-/

namespace EthInapproximability.CurrentPaper.VectorsCellRun

open Turing BitMachineEncoding
open EthInapproximability.CurrentPaper.EntryVectorsCell
open EthInapproximability.CurrentPaper.VectorsPrefix
open EthInapproximability.CurrentPaper.VectorsMiddle
open EthInapproximability.CurrentPaper.VectorsQuery

noncomputable section

def B10 (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ) : CS → List Bool :=
  Function.update (B9 edges D nV m M4 x y) (c 20) (List.replicate nV true)

def B11 (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ) : CS → List Bool :=
  Function.update (Function.update (Function.update (B10 edges D nV m M4 x y)
    (c 18) []) (c 20) []) (c 23)
      (EntryUnaryCompare.verdict true false false (x % D) nV ::
        B10 edges D nV m M4 x y (c 23))

def B12 (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ) : CS → List Bool :=
  Function.update (B11 edges D nV m M4 x y) (c 16) []

/-- The answer bit computed by the thirteen phases. -/
def cellValue (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ) : Bool :=
  comb (EntryUnaryCompare.verdict true false false y M4)
    (EntryUnaryCompare.verdict false true false (y / m) (x / D))
    (EntryUnaryCompare.verdict true false false (x % D) nV)
    (SourceGraphPayloadMachine.endpointHit edges (y % m) (x % D))

/-- The final bank: the fixed bank, both indices, and the one answer bit. -/
def B13 (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ) : CS → List Bool :=
  st x y (cellBank edges D nV m M4) [cellValue edges D nV m M4 x y]

theorem copy_nV (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ) :
    ((advance P10)^[2 * nV + 2])
      (⟨some BitMachineCopy.Label.scan, none, B9 edges D nV m M4 x y⟩ :
        TM2.Cfg (fun _ : CS => Bool) _ _) =
      ⟨none, none, B10 edges D nV m M4 x y⟩ := by
  have h := FamilyRowGeneric.copy_blank sCopyNV (B9 edges D nV m M4 x y)
    (by rfl) (by rfl)
  have hsrc : B9 edges D nV m M4 x y (sCopyNV 0) =
      List.replicate nV true := by rfl
  rw [hsrc, List.length_replicate] at h
  exact h

theorem compare_vertex (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ) :
    ∃ t ≤ max (x % D) nV + 2, ∃ v,
      ((advance P11)^[t])
        (⟨some EntryUnaryCompare.CL.loop, (none, none),
          B10 edges D nV m M4 x y⟩ : TM2.Cfg (fun _ : CS => Bool) _ _) =
        ⟨none, v, B11 edges D nV m M4 x y⟩ := by
  have h := EntryUnaryCompare.compare_run (c 18) (c 20) (c 23)
    (by decide) (by decide) (by decide) true false false
    (B10 edges D nV m M4 x y) (none, none) (x % D) nV
    (by rfl) (by rfl)
  exact h

theorem clear_remainder (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ) :
    ((advance P12)^[y % m + 2])
      (⟨some ClearLabel.loop, ((), none), B11 edges D nV m M4 x y⟩ :
        TM2.Cfg (fun _ : CS => Bool) _ _) =
      ⟨none, ((), none), B12 edges D nV m M4 x y⟩ := by
  have hp : P12 ClearLabel.loop =
      BitMachineClearBank.clearStep (c 16) ClearLabel.loop ClearLabel.done := rfl
  have h := BitMachineClearBank.clear_one_run P12 (c 16)
    ClearLabel.loop ClearLabel.done hp ()
    (B11 edges D nV m M4 x y)
  have hv : B11 edges D nV m M4 x y (c 16) =
      List.replicate (y % m) true := by rfl
  rw [hv, List.length_replicate] at h
  rw [show y % m + 2 = (y % m + 1) + 1 by omega,
    Function.iterate_succ_apply', h]
  rfl

/-- The literal bank after the four pops and the one push of P13. -/
theorem combine_bank (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ) :
    Function.update (Function.update (Function.update (Function.update
      (Function.update (B12 edges D nV m M4 x y) (c 21) []) (c 22) []) (c 23) [])
        (c 24) []) ANS [cellValue edges D nV m M4 x y] =
      B13 edges D nV m M4 x y := by
  funext k
  rcases k with k | k <;> fin_cases k <;> rfl

theorem combine (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ) :
    ∃ v, ((advance P13)^[1])
      (⟨some (), i13, B12 edges D nV m M4 x y⟩ :
        TM2.Cfg (fun _ : CS => Bool) _ _) =
      ⟨none, v, B13 edges D nV m M4 x y⟩ := by
  refine ⟨(some (EntryUnaryCompare.verdict true false false y M4),
    some (EntryUnaryCompare.verdict false true false (y / m) (x / D)),
    some (EntryUnaryCompare.verdict true false false (x % D) nV),
    some (SourceGraphPayloadMachine.endpointHit edges (y % m) (x % D))), ?_⟩
  rw [← combine_bank]
  rfl

/-- Explicit per-cell clock: the sum of the thirteen phase bounds plus the
twelve handoffs. -/
def cellBound (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ) : ℕ :=
  (2 * y + 2) + MatrixUnaryDivision.totalTime y m + (2 * x + 2) +
    MatrixUnaryDivision.totalTime x D + (2 * y + 2) + (2 * M4 + 2) +
    (max y M4 + 2) + (max (y / m) (x / D) + 2) +
    (3 * (x % D) + 3 * (y % m) + 6 +
      16 * ((SourceGraphPayloadMachine.endpointStream edges).length + 1) *
        (edges.length + 1)) +
    (2 * nV + 2) + (max (x % D) nV + 2) + (y % m + 2) + 1 + 12

theorem cell_run (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ) :
    ∃ t ≤ cellBound edges D nV m M4 x y, ∃ v,
      ((advance program)^[t])
        (MatrixTableWriter.cellCfg
          (some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
          initControl (cellBank edges D nV m M4) x y []) =
        MatrixTableWriter.cellCfg none v (cellBank edges D nV m M4) x y
          [cellValue edges D nV m M4 x y] := by
  obtain ⟨w13, h13⟩ := combine edges D nV m M4 x y
  obtain ⟨t12, ht12, r12⟩ := BitMachineRawSequence.runs P12 P13 ClearLabel.loop ()
    i12 ((), none) i13 w13 (B11 edges D nV m M4 x y) (B12 edges D nV m M4 x y)
    (B13 edges D nV m M4 x y) (y % m + 2) 1 (clear_remainder edges D nV m M4 x y) h13
  obtain ⟨t11, ht11, v11, h11⟩ := compare_vertex edges D nV m M4 x y
  obtain ⟨u11, hu11, r11⟩ := BitMachineRawSequence.runs P11 q12 EntryUnaryCompare.CL.loop
    (BitMachineRawSequence.leftLabel ClearLabel.loop) ((none, none) : EntryUnaryCompare.CV) v11
    (i12, i13) (i12, w13) (B10 edges D nV m M4 x y) (B11 edges D nV m M4 x y)
    (B13 edges D nV m M4 x y) t11 t12 h11 r12
  obtain ⟨u10, hu10, r10⟩ := BitMachineRawSequence.runs P10 q11 BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel EntryUnaryCompare.CL.loop) (none : Option Bool) none
    (((none, none) : EntryUnaryCompare.CV), (i12, i13))
    (((none, none) : EntryUnaryCompare.CV), (i12, w13))
    (B9 edges D nV m M4 x y) (B10 edges D nV m M4 x y)
    (B13 edges D nV m M4 x y) (2 * nV + 2) u11 (copy_nV edges D nV m M4 x y) r11
  obtain ⟨t9, ht9, v9, h9⟩ := query edges D nV m M4 x y
  obtain ⟨u9, hu9, r9⟩ := BitMachineRawSequence.runs P9 q10
    SourceGraphPayloadMachine.BaseCell.start
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    SourceGraphPayloadMachine.BaseCell.initial v9
    ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV), (i12, i13)))
    ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV), (i12, w13)))
    (B8 edges D nV m M4 x y) (B9 edges D nV m M4 x y)
    (B13 edges D nV m M4 x y) t9 u10 h9 r10
  obtain ⟨t8, ht8, v8, h8⟩ := compare_copies edges D nV m M4 x y
  obtain ⟨u8, hu8, r8⟩ := BitMachineRawSequence.runs P8 q9 EntryUnaryCompare.CL.loop
    (BitMachineRawSequence.leftLabel SourceGraphPayloadMachine.BaseCell.start)
    ((none, none) : EntryUnaryCompare.CV) v8
    (SourceGraphPayloadMachine.BaseCell.initial,
      ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV), (i12, i13))))
    (SourceGraphPayloadMachine.BaseCell.initial,
      ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV), (i12, w13))))
    (B7 edges D nV m M4 x y) (B8 edges D nV m M4 x y)
    (B13 edges D nV m M4 x y) t8 u9 h8 r9
  obtain ⟨t7, ht7, v7, h7⟩ := compare_padded edges D nV m M4 x y
  obtain ⟨u7, hu7, r7⟩ := BitMachineRawSequence.runs P7 q8 EntryUnaryCompare.CL.loop
    (BitMachineRawSequence.leftLabel EntryUnaryCompare.CL.loop)
    ((none, none) : EntryUnaryCompare.CV) v7
    (((none, none) : EntryUnaryCompare.CV), (SourceGraphPayloadMachine.BaseCell.initial,
      ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV), (i12, i13)))))
    (((none, none) : EntryUnaryCompare.CV), (SourceGraphPayloadMachine.BaseCell.initial,
      ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV), (i12, w13)))))
    (B6 edges D nV m M4 x y) (B7 edges D nV m M4 x y)
    (B13 edges D nV m M4 x y) t7 u8 h7 r8
  obtain ⟨u6, hu6, r6⟩ := BitMachineRawSequence.runs P6 q7 BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel EntryUnaryCompare.CL.loop) (none : Option Bool) none
    (((none, none) : EntryUnaryCompare.CV), (((none, none) : EntryUnaryCompare.CV),
      (SourceGraphPayloadMachine.BaseCell.initial,
      ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV), (i12, i13))))))
    (((none, none) : EntryUnaryCompare.CV), (((none, none) : EntryUnaryCompare.CV),
      (SourceGraphPayloadMachine.BaseCell.initial,
      ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV), (i12, w13))))))
    (B5 edges D nV m M4 x y) (B6 edges D nV m M4 x y)
    (B13 edges D nV m M4 x y) (2 * M4 + 2) u7 (copy_M4 edges D nV m M4 x y) r7
  obtain ⟨u5, hu5, r5⟩ := BitMachineRawSequence.runs P5 q6 BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) (none : Option Bool) none
    ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV),
      (((none, none) : EntryUnaryCompare.CV), (SourceGraphPayloadMachine.BaseCell.initial,
      ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV), (i12, i13)))))))
    ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV),
      (((none, none) : EntryUnaryCompare.CV), (SourceGraphPayloadMachine.BaseCell.initial,
      ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV), (i12, w13)))))))
    (B4 edges D nV m M4 x y) (B5 edges D nV m M4 x y)
    (B13 edges D nV m M4 x y) (2 * y + 2) u6 (copy_y_again edges D nV m M4 x y) r6
  obtain ⟨u4, hu4, r4⟩ := BitMachineRawSequence.runs P4 q5 MatrixUnaryDivision.Label.start
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) false false
    ((none : Option Bool), ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV),
      (((none, none) : EntryUnaryCompare.CV), (SourceGraphPayloadMachine.BaseCell.initial,
      ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV), (i12, i13))))))))
    ((none : Option Bool), ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV),
      (((none, none) : EntryUnaryCompare.CV), (SourceGraphPayloadMachine.BaseCell.initial,
      ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV), (i12, w13))))))))
    (B3 edges D nV m M4 x y) (B4 edges D nV m M4 x y)
    (B13 edges D nV m M4 x y) (MatrixUnaryDivision.totalTime x D) u5
    (divide_x edges D nV m M4 x y) r5
  obtain ⟨u3, hu3, r3⟩ := BitMachineRawSequence.runs P3 q4 BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel MatrixUnaryDivision.Label.start) (none : Option Bool) none
    (false, ((none : Option Bool), ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV),
      (((none, none) : EntryUnaryCompare.CV), (SourceGraphPayloadMachine.BaseCell.initial,
      ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV), (i12, i13)))))))))
    (false, ((none : Option Bool), ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV),
      (((none, none) : EntryUnaryCompare.CV), (SourceGraphPayloadMachine.BaseCell.initial,
      ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV), (i12, w13)))))))))
    (B2 edges D nV m M4 x y) (B3 edges D nV m M4 x y)
    (B13 edges D nV m M4 x y) (2 * x + 2) u4 (copy_x edges D nV m M4 x y) r4
  obtain ⟨u2, hu2, r2⟩ := BitMachineRawSequence.runs P2 q3 MatrixUnaryDivision.Label.start
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) false false
    ((none : Option Bool), (false, ((none : Option Bool), ((none : Option Bool),
      (((none, none) : EntryUnaryCompare.CV),
      (((none, none) : EntryUnaryCompare.CV), (SourceGraphPayloadMachine.BaseCell.initial,
      ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV), (i12, i13))))))))))
    ((none : Option Bool), (false, ((none : Option Bool), ((none : Option Bool),
      (((none, none) : EntryUnaryCompare.CV),
      (((none, none) : EntryUnaryCompare.CV), (SourceGraphPayloadMachine.BaseCell.initial,
      ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV), (i12, w13))))))))))
    (B1 edges D nV m M4 x y) (B2 edges D nV m M4 x y)
    (B13 edges D nV m M4 x y) (MatrixUnaryDivision.totalTime y m) u3
    (divide_y edges D nV m M4 x y) r3
  obtain ⟨u1, hu1, r1⟩ := BitMachineRawSequence.runs P1 q2 BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel MatrixUnaryDivision.Label.start) (none : Option Bool) none
    tailInit
    (false, ((none : Option Bool), (false, ((none : Option Bool), ((none : Option Bool),
      (((none, none) : EntryUnaryCompare.CV),
      (((none, none) : EntryUnaryCompare.CV), (SourceGraphPayloadMachine.BaseCell.initial,
      ((none : Option Bool), (((none, none) : EntryUnaryCompare.CV), (i12, w13)))))))))))
    (B0 edges D nV m M4 x y) (B1 edges D nV m M4 x y)
    (B13 edges D nV m M4 x y) (2 * y + 2) u2 (copy_y edges D nV m M4 x y) r2
  refine ⟨u1, ?_, _, r1⟩
  unfold cellBound
  omega

#print axioms copy_nV
#print axioms compare_vertex
#print axioms clear_remainder
#print axioms combine_bank
#print axioms combine
#print axioms cell_run

end
end EthInapproximability.CurrentPaper.VectorsCellRun
