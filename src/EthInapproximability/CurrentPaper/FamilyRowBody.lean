import EthInapproximability.CurrentPaper.FamilyRowGeneric

/-!
# One physical row of the Stage-4 one-hot family tables

Lane owner:b-stage4-entry-program, segment 1 (row body).

ONE fixed controller `bodyProgram` (twelve literal phases in a right-nested
`BitMachineRawSequence`) on the named-cell bank `Cell`.  From the unary row
counter `r` and the retained unary operand words `P, T, Q, RX, W, M` it
(1) copies `r`; (2) divides by `Q` with the admitted `MatrixUnaryDivision`
controller, landing `r / Q` and `r % Q` directly in the entry region;
(3)-(5) copies `P`, `T`, `M` into the entry region; (6) runs the admitted
unary accessor `PrimeSamplerEntryMachine.program`; (7) divides the entry
value by `RX`; (8)-(11) writes the one-hot words of quotient (width `W`)
and remainder (width `RX`) in front of the two accumulators, width copies
charged; (12) clears the four garbage entry cells by charged pops.

Exit: the SAME bank shape `rowBank` with only the two accumulators
extended.  No entry value, family value or table word is an input.
-/

namespace EthInapproximability.CurrentPaper.FamilyRowBody

open Turing BitMachineEncoding BitMachineStackEmbedding
open MatrixStage4ScalarPreparationOps FamilyRowGeneric

inductive Cell where
  | cnt | prime | order | q | rx | w | m
  | x | dcount | dsaved | cs
  | e (i : Fin 11)
  | quo | rem | wc | sv
  | first | row
  deriving DecidableEq

def eSlots : Fin 11 ↪ Cell := ⟨Cell.e, fun _ _ h => Cell.e.inj h⟩

def entryProgram :
    PrimeSamplerEntryMachine.Label →
      TM2.Stmt (fun _ : Cell => Bool) PrimeSamplerEntryMachine.Label
        PrimeSamplerEntryMachine.Control :=
  fun l => stackStmt eSlots (PrimeSamplerEntryMachine.program l)

theorem entry_embedded (S : Cell → List Bool) (p t l j m : ℕ)
    (hp : 0 < p) (hj : j < p) (hl : l < p ^ t)
    (h0 : S (.e 0) = List.replicate l true) (h1 : S (.e 1) = List.replicate p true)
    (h2 : S (.e 2) = []) (h3 : S (.e 3) = []) (h4 : S (.e 4) = [])
    (h5 : S (.e 5) = []) (h6 : S (.e 6) = List.replicate t true) (h7 : S (.e 7) = [])
    (h8 : S (.e 8) = List.replicate j true) (h9 : S (.e 9) = [])
    (h10 : S (.e 10) = List.replicate m true) :
    ∃ n ≤ PrimeSamplerEntryMachine.timeBound p t l j m,
      ((advance entryProgram)^[n])
        (⟨some (.inl (.inr .loop)), (false, none), S⟩ :
          TM2.Cfg (fun _ : Cell => Bool) PrimeSamplerEntryMachine.Label
            PrimeSamplerEntryMachine.Control) =
      ⟨none, (false, none),
        Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update S
            (.e 0) (List.replicate j true)) (.e 1) [])
            (.e 4) (List.replicate (PrimeSampler.entry p t m l j) true))
            (.e 6) (List.replicate p true))
            (.e 7) (List.replicate (PrimeSamplerEntryAlgorithm.horner p j t l / m) true))
            (.e 8) []⟩ := by
  obtain ⟨n, hn, he⟩ := entry_exact p t l j m hp hj hl
  refine ⟨n, hn, ?_⟩
  let c := PrimeSamplerEntryMachine.cfg (some (.inl (.inr .loop)))
    ![PrimeSamplerEntryMachine.unary l, PrimeSamplerEntryMachine.unary p, [], [], [], [],
      PrimeSamplerEntryMachine.unary t, [], PrimeSamplerEntryMachine.unary j, [],
      PrimeSamplerEntryMachine.unary m]
  have hstart : stackCfg eSlots S c =
      (⟨some (.inl (.inr .loop)), (false, none), S⟩ :
        TM2.Cfg (fun _ : Cell => Bool) PrimeSamplerEntryMachine.Label
          PrimeSamplerEntryMachine.Control) := by
    simp only [stackCfg, c, PrimeSamplerEntryMachine.cfg]
    congr 1
    apply bank_eq_self
    intro k
    fin_cases k <;>
      simp [eSlots, PrimeSamplerEntryMachine.unary, h0, h1, h2, h3, h4, h5, h6, h7,
        h8, h9, h10]
  have hrun := BitMachineStackRun.run eSlots S PrimeSamplerEntryMachine.program c n
  rw [hstart] at hrun
  unfold entryProgram
  rw [hrun]
  change stackCfg eSlots S (PrimeSamplerEntryMachine.run n c) = _
  rw [he]
  simp only [stackCfg, PrimeSamplerEntryMachine.cfg]
  congr 1
  have hloc : (![PrimeSamplerEntryMachine.unary j, [], [], [],
      PrimeSamplerEntryMachine.unary (PrimeSampler.entry p t m l j), [],
      PrimeSamplerEntryMachine.unary p,
      PrimeSamplerEntryMachine.unary (PrimeSamplerEntryAlgorithm.horner p j t l / m),
      [], [], PrimeSamplerEntryMachine.unary m] : Fin 11 → List Bool) =
      Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (fun k => S (eSlots k))
          0 (List.replicate j true)) 1 [])
          4 (List.replicate (PrimeSampler.entry p t m l j) true))
          6 (List.replicate p true))
          7 (List.replicate (PrimeSamplerEntryAlgorithm.horner p j t l / m) true))
          8 [] := by
    funext k
    fin_cases k <;>
      simp [eSlots, PrimeSamplerEntryMachine.unary, h2, h3, h5, h9, h10]
  rw [hloc, bank_update, bank_update, bank_update, bank_update, bank_update,
    bank_update, bank_restrict]
  rfl

/-! ## Slots, the clear phase, and the row bank -/

def slotX : Fin 3 ↪ Cell := ⟨![.cnt, .x, .cs], by decide⟩
def slotP : Fin 3 ↪ Cell := ⟨![.prime, .e 1, .cs], by decide⟩
def slotT : Fin 3 ↪ Cell := ⟨![.order, .e 6, .cs], by decide⟩
def slotM : Fin 3 ↪ Cell := ⟨![.m, .e 10, .cs], by decide⟩
def slotW : Fin 3 ↪ Cell := ⟨![.w, .wc, .cs], by decide⟩
def slotR : Fin 3 ↪ Cell := ⟨![.rx, .wc, .cs], by decide⟩
def div1 : Fin 6 ↪ Cell := ⟨![.x, .q, .dcount, .e 8, .e 0, .dsaved], by decide⟩
def div2 : Fin 6 ↪ Cell := ⟨![.e 4, .rx, .dcount, .rem, .quo, .dsaved], by decide⟩
def oh1 : Fin 4 ↪ Cell := ⟨![.quo, .wc, .sv, .first], by decide⟩
def oh2 : Fin 4 ↪ Cell := ⟨![.rem, .wc, .sv, .row], by decide⟩
def clearCells : Fin 4 ↪ Cell := ⟨![.e 0, .e 6, .e 7, .e 10], by decide⟩

inductive ClearLabel where
  | clear (i : Fin 5)
  | done
  deriving DecidableEq

def clearProgram : ClearLabel →
    TM2.Stmt (fun _ : Cell => Bool) ClearLabel (Unit × Option Bool)
  | .clear i => if h : i.val < 4 then
      BitMachineClearBank.clearStep (clearCells ⟨i.val, h⟩)
        (.clear i) (.clear ⟨i.val + 1, by omega⟩)
    else BitMachineClearBank.finishStep (fun _ => ()) .done
  | .done => .halt

def clearCost (S : Cell → List Bool) : ℕ :=
  (∑ i : Fin 4, (S (clearCells i)).length) + 6

theorem clear_run (S : Cell → List Bool) :
    ((advance clearProgram)^[clearCost S])
      (⟨some (.clear 0), ((), none), S⟩ :
        TM2.Cfg (fun _ : Cell => Bool) ClearLabel (Unit × Option Bool)) =
      ⟨none, ((), none), BitMachineClearBank.cleared clearCells S⟩ := by
  have hs (i : Fin 4) : clearProgram (.clear i.castSucc) =
      BitMachineClearBank.clearStep (clearCells i)
        (.clear i.castSucc) (.clear i.succ) := by
    simp only [clearProgram, Fin.val_castSucc, dif_pos i.isLt]
    rfl
  have hf : clearProgram (.clear (Fin.last 4)) =
      BitMachineClearBank.finishStep (fun _ => ()) .done := by
    simp only [clearProgram, Fin.val_last, lt_self_iff_false, ↓reduceDIte]
  have hr := BitMachineClearBank.clear_bank_run clearProgram
    (fun _ => ()) ClearLabel.done 4 clearCells clearCells.injective
    ClearLabel.clear hs hf () S
  have hd : advance clearProgram
      (⟨some .done, ((), none), BitMachineClearBank.cleared clearCells S⟩ :
        TM2.Cfg (fun _ : Cell => Bool) ClearLabel (Unit × Option Bool)) =
      ⟨none, ((), none), BitMachineClearBank.cleared clearCells S⟩ := rfl
  rw [clearCost, show (∑ i : Fin 4, (S (clearCells i)).length) + 6 =
      1 + ((∑ i : Fin 4, (S (clearCells i)).length) + 4 + 1) by omega,
    Function.iterate_add_apply, hr]
  exact hd

theorem mem_clearCells (k : Cell) :
    (∃ i, clearCells i = k) ↔
      (k = .e 0 ∨ k = .e 6 ∨ k = .e 7 ∨ k = .e 10) := by
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩

/-- The bank at the start and end of every row: counter, six operand words,
two accumulators, and every scratch cell blank. -/
def rowBank (r P T Q RX Wd Md : ℕ) (A1 A2 : List Bool) : Cell → List Bool
  | .cnt => List.replicate r true
  | .prime => List.replicate P true
  | .order => List.replicate T true
  | .q => List.replicate Q true
  | .rx => List.replicate RX true
  | .w => List.replicate Wd true
  | .m => List.replicate Md true
  | .first => A1
  | .row => A2
  | _ => []

/-! ## The fixed twelve-phase controller -/

abbrev CL := BitMachineCopy.Label
abbrev DL := MatrixUnaryDivision.Label
abbrev EL := PrimeSamplerEntryMachine.Label
abbrev EC := PrimeSamplerEntryMachine.Control
abbrev OL := PrimeSamplerFamilyTableOneHot.Label
abbrev KC := Unit × Option Bool

abbrev L12 := ClearLabel
abbrev L11 := BitMachineRawSequence.Label OL L12
abbrev L10 := BitMachineRawSequence.Label CL L11
abbrev L9 := BitMachineRawSequence.Label OL L10
abbrev L8 := BitMachineRawSequence.Label CL L9
abbrev L7 := BitMachineRawSequence.Label DL L8
abbrev L6 := BitMachineRawSequence.Label EL L7
abbrev L5 := BitMachineRawSequence.Label CL L6
abbrev L4 := BitMachineRawSequence.Label CL L5
abbrev L3 := BitMachineRawSequence.Label CL L4
abbrev L2 := BitMachineRawSequence.Label DL L3
abbrev L1 := BitMachineRawSequence.Label CL L2

abbrev C12 := KC
abbrev C11 := BitMachineRawSequence.Control (Option Bool) C12
abbrev C10 := BitMachineRawSequence.Control (Option Bool) C11
abbrev C9 := BitMachineRawSequence.Control (Option Bool) C10
abbrev C8 := BitMachineRawSequence.Control (Option Bool) C9
abbrev C7 := BitMachineRawSequence.Control Bool C8
abbrev C6 := BitMachineRawSequence.Control EC C7
abbrev C5 := BitMachineRawSequence.Control (Option Bool) C6
abbrev C4 := BitMachineRawSequence.Control (Option Bool) C5
abbrev C3 := BitMachineRawSequence.Control (Option Bool) C4
abbrev C2 := BitMachineRawSequence.Control Bool C3
abbrev C1 := BitMachineRawSequence.Control (Option Bool) C2

def i12 : C12 := ((), none)
def i11 : C11 := (none, i12)
def i10 : C10 := (none, i11)
def i9 : C9 := (none, i10)
def i8 : C8 := (none, i9)
def i7 : C7 := (false, i8)
def i6 : C6 := ((false, none), i7)
def i5 : C5 := (none, i6)
def i4 : C4 := (none, i5)
def i3 : C3 := (none, i4)
def i2 : C2 := (false, i3)
def i1 : C1 := (none, i2)

def s12 : L12 := .clear 0
def s11 : L11 := BitMachineRawSequence.leftLabel PrimeSamplerFamilyTableOneHot.Label.start
def s10 : L10 := BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan
def s9 : L9 := BitMachineRawSequence.leftLabel PrimeSamplerFamilyTableOneHot.Label.start
def s8 : L8 := BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan
def s7 : L7 := BitMachineRawSequence.leftLabel MatrixUnaryDivision.Label.start
def s6 : L6 := BitMachineRawSequence.leftLabel (.inl (.inr .loop))
def s5 : L5 := BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan
def s4 : L4 := BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan
def s3 : L3 := BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan
def s2 : L2 := BitMachineRawSequence.leftLabel MatrixUnaryDivision.Label.start
def s1 : L1 := BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan

abbrev Stmt (L V : Type) := TM2.Stmt (fun _ : Cell => Bool) L V

def P12 : L12 → Stmt L12 C12 := clearProgram
def P11 : L11 → Stmt L11 C11 :=
  BitMachineRawSequence.program (ohProgram oh2) P12 s12 none i12
def P10 : L10 → Stmt L10 C10 :=
  BitMachineRawSequence.program (copyProgram slotR) P11 s11 none i11
def P9 : L9 → Stmt L9 C9 :=
  BitMachineRawSequence.program (ohProgram oh1) P10 s10 none i10
def P8 : L8 → Stmt L8 C8 :=
  BitMachineRawSequence.program (copyProgram slotW) P9 s9 none i9
def P7 : L7 → Stmt L7 C7 :=
  BitMachineRawSequence.program (divProgram div2) P8 s8 false i8
def P6 : L6 → Stmt L6 C6 :=
  BitMachineRawSequence.program entryProgram P7 s7 (false, none) i7
def P5 : L5 → Stmt L5 C5 :=
  BitMachineRawSequence.program (copyProgram slotM) P6 s6 none i6
def P4 : L4 → Stmt L4 C4 :=
  BitMachineRawSequence.program (copyProgram slotT) P5 s5 none i5
def P3 : L3 → Stmt L3 C3 :=
  BitMachineRawSequence.program (copyProgram slotP) P4 s4 none i4
def P2 : L2 → Stmt L2 C2 :=
  BitMachineRawSequence.program (divProgram div1) P3 s3 false i3

/-- The single fixed row-body controller. -/
def bodyProgram : L1 → Stmt L1 C1 :=
  BitMachineRawSequence.program (copyProgram slotX) P2 s2 none i2

/-- Exact per-row clock (sum of the charged phase clocks and eleven
handoffs; the entry phase uses the admitted `timeBound`). -/
def bodyTime (r P T Q RX Wd Md : ℕ) : ℕ :=
  (2 * r + 2) + MatrixUnaryDivision.totalTime r Q + (2 * P + 2) + (2 * T + 2) +
    (2 * Md + 2) + PrimeSamplerEntryMachine.timeBound P T (r / Q) (r % Q) Md +
    MatrixUnaryDivision.totalTime (PrimeSampler.entry P T Md (r / Q) (r % Q)) RX +
    (2 * Wd + 2) + ohTime (PrimeSampler.entry P T Md (r / Q) (r % Q) / RX) Wd +
    (2 * RX + 2) + ohTime (PrimeSampler.entry P T Md (r / Q) (r % Q) % RX) RX +
    ((r % Q) + P + PrimeSamplerEntryAlgorithm.horner P (r % Q) T (r / Q) / Md + Md + 6) +
    11

set_option maxHeartbeats 1000000 in
/-- One row: the fixed controller turns `rowBank … A1 A2` into
`rowBank … (oneHot W (e / RX) ++ A1) (oneHot RX (e % RX) ++ A2)` for the
actual entry value `e = PrimeSampler.entry P T M (r / Q) (r % Q)`. -/
theorem body_run (r P T Q RX Wd Md : ℕ) (A1 A2 : List Bool)
    (hP : 0 < P) (hj : r % Q < P) (hl : r / Q < P ^ T) (hRX : 0 < RX)
    (hW : PrimeSampler.entry P T Md (r / Q) (r % Q) / RX < Wd) :
    ∃ t ≤ bodyTime r P T Q RX Wd Md,
      ((advance bodyProgram)^[t])
        (⟨some s1, i1, rowBank r P T Q RX Wd Md A1 A2⟩ :
          TM2.Cfg (fun _ : Cell => Bool) L1 C1) =
        ⟨none, i1, rowBank r P T Q RX Wd Md
          (MatrixStage4FamilyData.oneHot Wd
            ⟨PrimeSampler.entry P T Md (r / Q) (r % Q) / RX, hW⟩ ++ A1)
          (MatrixStage4FamilyData.oneHot RX
            ⟨PrimeSampler.entry P T Md (r / Q) (r % Q) % RX, Nat.mod_lt _ hRX⟩ ++ A2)⟩ := by
  let l := r / Q
  let j := r % Q
  let e := PrimeSampler.entry P T Md l j
  let h := PrimeSamplerEntryAlgorithm.horner P j T l
  have hR : e % RX < RX := Nat.mod_lt _ hRX
  let B0 := rowBank r P T Q RX Wd Md A1 A2
  let B1 := Function.update B0 Cell.x (List.replicate r true)
  let B2 := Function.update (Function.update (Function.update B1 Cell.x [])
    (Cell.e 8) (List.replicate (r % Q) true)) (Cell.e 0) (List.replicate (r / Q) true)
  let B3 := Function.update B2 (Cell.e 1) (List.replicate P true)
  let B4 := Function.update B3 (Cell.e 6) (List.replicate T true)
  let B5 := Function.update B4 (Cell.e 10) (List.replicate Md true)
  let B6 := Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update B5
      (Cell.e 0) (List.replicate j true)) (Cell.e 1) [])
      (Cell.e 4) (List.replicate e true))
      (Cell.e 6) (List.replicate P true))
      (Cell.e 7) (List.replicate (h / Md) true))
      (Cell.e 8) []
  let B7 := Function.update (Function.update (Function.update B6 (Cell.e 4) [])
    Cell.rem (List.replicate (e % RX) true)) Cell.quo (List.replicate (e / RX) true)
  let B8 := Function.update B7 Cell.wc (List.replicate Wd true)
  let B9 := Function.update (Function.update (Function.update B8 Cell.quo [])
    Cell.wc []) Cell.first (MatrixStage4FamilyData.oneHot Wd ⟨e / RX, hW⟩ ++ B8 Cell.first)
  let B10 := Function.update B9 Cell.wc (List.replicate RX true)
  let B11 := Function.update (Function.update (Function.update B10 Cell.rem [])
    Cell.wc []) Cell.row (MatrixStage4FamilyData.oneHot RX ⟨e % RX, hR⟩ ++ B10 Cell.row)
  let B12 := BitMachineClearBank.cleared clearCells B11
  -- phase 1
  have c1 : ((advance (copyProgram slotX))^[2 * r + 2])
      (⟨some .scan, none, B0⟩ : TM2.Cfg (fun _ : Cell => Bool) CL (Option Bool)) =
      ⟨none, none, B1⟩ := by
    have hh := copy_blank slotX B0 rfl rfl
    rw [show (B0 (slotX 0)).length = r by simp [B0, slotX, rowBank]] at hh
    exact hh
  -- phase 2
  have c2 : ((advance (divProgram div1))^[MatrixUnaryDivision.totalTime r Q])
      (⟨some .start, false, B1⟩ : TM2.Cfg (fun _ : Cell => Bool) DL Bool) =
      ⟨none, false, B2⟩ :=
    div_run div1 B1 r Q rfl rfl rfl rfl rfl rfl
  -- phases 3-5
  have c3 : ((advance (copyProgram slotP))^[2 * P + 2])
      (⟨some .scan, none, B2⟩ : TM2.Cfg (fun _ : Cell => Bool) CL (Option Bool)) =
      ⟨none, none, B3⟩ := by
    have hh := copy_blank slotP B2 rfl rfl
    rw [show (B2 (slotP 0)).length = P by simp [B2, B1, B0, slotP, rowBank]] at hh
    exact hh
  have c4 : ((advance (copyProgram slotT))^[2 * T + 2])
      (⟨some .scan, none, B3⟩ : TM2.Cfg (fun _ : Cell => Bool) CL (Option Bool)) =
      ⟨none, none, B4⟩ := by
    have hh := copy_blank slotT B3 rfl rfl
    rw [show (B3 (slotT 0)).length = T by simp [B3, B2, B1, B0, slotT, rowBank]] at hh
    exact hh
  have c5 : ((advance (copyProgram slotM))^[2 * Md + 2])
      (⟨some .scan, none, B4⟩ : TM2.Cfg (fun _ : Cell => Bool) CL (Option Bool)) =
      ⟨none, none, B5⟩ := by
    have hh := copy_blank slotM B4 rfl rfl
    rw [show (B4 (slotM 0)).length = Md by simp [B4, B3, B2, B1, B0, slotM, rowBank]] at hh
    exact hh
  -- phase 6
  obtain ⟨n6, hn6, c6⟩ := entry_embedded B5 P T l j Md hP hj hl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  -- phase 7
  have c7 : ((advance (divProgram div2))^[MatrixUnaryDivision.totalTime e RX])
      (⟨some .start, false, B6⟩ : TM2.Cfg (fun _ : Cell => Bool) DL Bool) =
      ⟨none, false, B7⟩ :=
    div_run div2 B6 e RX rfl rfl rfl rfl rfl rfl
  -- phases 8-9
  have c8 : ((advance (copyProgram slotW))^[2 * Wd + 2])
      (⟨some .scan, none, B7⟩ : TM2.Cfg (fun _ : Cell => Bool) CL (Option Bool)) =
      ⟨none, none, B8⟩ := by
    have hh := copy_blank slotW B7 rfl rfl
    rw [show (B7 (slotW 0)).length = Wd by
      simp [B7, B6, B5, B4, B3, B2, B1, B0, slotW, rowBank]] at hh
    exact hh
  have c9 : ((advance (ohProgram oh1))^[ohTime (e / RX) Wd])
      (⟨some .start, none, B8⟩ : TM2.Cfg (fun _ : Cell => Bool) OL (Option Bool)) =
      ⟨none, none, B9⟩ :=
    oh_run oh1 B8 (e / RX) Wd hW rfl rfl rfl
  -- phases 10-11
  have c10 : ((advance (copyProgram slotR))^[2 * RX + 2])
      (⟨some .scan, none, B9⟩ : TM2.Cfg (fun _ : Cell => Bool) CL (Option Bool)) =
      ⟨none, none, B10⟩ := by
    have hh := copy_blank slotR B9 rfl rfl
    rw [show (B9 (slotR 0)).length = RX by
      simp [B9, B8, B7, B6, B5, B4, B3, B2, B1, B0, slotR, rowBank]] at hh
    exact hh
  have c11 : ((advance (ohProgram oh2))^[ohTime (e % RX) RX])
      (⟨some .start, none, B10⟩ : TM2.Cfg (fun _ : Cell => Bool) OL (Option Bool)) =
      ⟨none, none, B11⟩ :=
    oh_run oh2 B10 (e % RX) RX hR rfl rfl rfl
  -- phase 12
  have c12 := clear_run B11
  have hcc : clearCost B11 = j + P + h / Md + Md + 6 := by
    simp [clearCost, Fin.sum_univ_four, clearCells, B11, B10, B9, B8, B7, B6, B5,
      B4, B3, B2, B1, B0, rowBank]
  rw [hcc] at c12
  -- sequencing
  obtain ⟨u11, hu11, r11⟩ := BitMachineRawSequence.runs (ohProgram oh2) P12
    PrimeSamplerFamilyTableOneHot.Label.start s12 none none i12 i12
    B10 B11 B12 _ _ c11 c12
  obtain ⟨u10, hu10, r10⟩ := BitMachineRawSequence.runs (copyProgram slotR) P11
    BitMachineCopy.Label.scan s11 none none i11 i11 B9 B10 B12 _ _ c10 r11
  obtain ⟨u9, hu9, r9⟩ := BitMachineRawSequence.runs (ohProgram oh1) P10
    PrimeSamplerFamilyTableOneHot.Label.start s10 none none i10 i10 B8 B9 B12 _ _ c9 r10
  obtain ⟨u8, hu8, r8⟩ := BitMachineRawSequence.runs (copyProgram slotW) P9
    BitMachineCopy.Label.scan s9 none none i9 i9 B7 B8 B12 _ _ c8 r9
  obtain ⟨u7, hu7, r7⟩ := BitMachineRawSequence.runs (divProgram div2) P8
    MatrixUnaryDivision.Label.start s8 false false i8 i8 B6 B7 B12 _ _ c7 r8
  obtain ⟨u6, hu6, r6⟩ := BitMachineRawSequence.runs entryProgram P7
    (.inl (.inr .loop)) s7 (false, none) (false, none) i7 i7 B5 B6 B12 _ _ c6 r7
  obtain ⟨u5, hu5, r5⟩ := BitMachineRawSequence.runs (copyProgram slotM) P6
    BitMachineCopy.Label.scan s6 none none i6 i6 B4 B5 B12 _ _ c5 r6
  obtain ⟨u4, hu4, r4⟩ := BitMachineRawSequence.runs (copyProgram slotT) P5
    BitMachineCopy.Label.scan s5 none none i5 i5 B3 B4 B12 _ _ c4 r5
  obtain ⟨u3, hu3, r3⟩ := BitMachineRawSequence.runs (copyProgram slotP) P4
    BitMachineCopy.Label.scan s4 none none i4 i4 B2 B3 B12 _ _ c3 r4
  obtain ⟨u2, hu2, r2⟩ := BitMachineRawSequence.runs (divProgram div1) P3
    MatrixUnaryDivision.Label.start s3 false false i3 i3 B1 B2 B12 _ _ c2 r3
  obtain ⟨u1, hu1, r1⟩ := BitMachineRawSequence.runs (copyProgram slotX) P2
    BitMachineCopy.Label.scan s2 none none i2 i2 B0 B1 B12 _ _ c1 r2
  have hfinal : B12 = rowBank r P T Q RX Wd Md
      (MatrixStage4FamilyData.oneHot Wd ⟨e / RX, hW⟩ ++ A1)
      (MatrixStage4FamilyData.oneHot RX ⟨e % RX, hR⟩ ++ A2) := by
    funext c
    simp only [B12, BitMachineClearBank.cleared, mem_clearCells]
    cases c with
    | e i =>
        fin_cases i <;>
          simp [B11, B10, B9, B8, B7, B6, B5, B4, B3, B2, B1, B0, rowBank]
    | _ => simp [B11, B10, B9, B8, B7, B6, B5, B4, B3, B2, B1, B0, rowBank]
  refine ⟨u1, ?_, ?_⟩
  · unfold bodyTime
    rw [show r / Q = l from rfl, show r % Q = j from rfl,
      show PrimeSampler.entry P T Md l j = e from rfl,
      show PrimeSamplerEntryAlgorithm.horner P j T l = h from rfl]
    omega
  · rw [← hfinal]
    exact r1

#print axioms entry_embedded
#print axioms clear_run
#print axioms body_run

end EthInapproximability.CurrentPaper.FamilyRowBody
