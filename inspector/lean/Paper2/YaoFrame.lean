import Paper2.YaoMachineRun
import Paper2.YaoFrameHdr
import Paper2.EncodedSelectedOutput

/-! Unit 5 segment Y8 (lane a-yao-owner-3): output framing appended to the Yao
table machine `Paper2.YaoMachine.yaoMachine` (frozen private predecessor
a-yao-owner-2, under root admission wave12-a24).

ONE fixed program `yaoFramed t lambda` per `(t, lambda)` on the stack
`FStack t lambda = WStack t lambda ⊕ HeaderA.HB`:

* stage A: the table machine `yaoMachine t lambda`, embedded on the left
  summand (admitted `BitMachineStackRun.run`);
* stages B, C: two charged admitted copies of the prelude cell `b =
  paddedEdgeBits e` (`sN 5`) onto the threshold cell;
* stage D: the admitted fixed writer pushes `4*t+2` marks, so the threshold cell
  holds unary `B = 2*b+4*t+2` (R-Y3, Y:149);
* stage E: the admitted header stage `HeaderA.prog` (three unary-to-binary
  conversions and the admitted `MatrixInstanceEncoding` serializer), placed so
  that its three fuel cells are the writer's `rows`, `cols` cells and the
  threshold cell, and its output cell is the writer's output cell.

Four charged handoffs.  Exit bank exact: the writer bank of
`physical_yao_table` with `rows`, `cols` consumed to `[]` and the output cell
holding `encodeInstance (yaoInstanceDraft t lambda x bits)`; every header cell
back to `[]`.

DRAFT (marked): `yaoInstanceDraft` and `yaoLanguageDraft` are the root ruling
R-Y3 format and language; they are NOT an author decision (D-A4 / D-Y3 are
untaken) and nothing here adopts them. -/

noncomputable section

namespace Paper2.YaoFrame

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.EncodedCommunication
open Paper2.Yao
open Paper2.YaoLowerBound
open Paper2.YaoLowerBound.Materialization
open Paper2.YaoLookup
open Paper2.YaoMaterialization
open Paper2.YaoSourceCodec
open Paper2.YaoPrelude
open Paper2.YaoMachine
open Paper2.HeaderA

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384
set_option linter.unusedSimpArgs false

/-! ## DRAFT definitions (R-Y3; pending D-A4 / D-Y3) -/

/-- **DRAFT (R-Y3, pending D-A4 / D-Y3).** The printed Yao instance: the exact
dimensions of the materialized table, threshold `B = 2*b+4*t+2`, and the
printed table itself. -/
def yaoInstanceDraft (t lambda : ℕ) (x : YaoSource t)
    (bits : SerializedTape t (paddedEdgeBits x.2.1) lambda) : EncodedCommunication.Instance :=
  ⟨rowCount x.1 t (paddedEdgeBits x.2.1) lambda, columnCount t (paddedEdgeBits x.2.1) lambda,
    2 * paddedEdgeBits x.2.1 + 4 * t + 2, (materialize t lambda x.2.2 bits).bits⟩

/-- **DRAFT (R-Y3, pending D-A4 / D-Y3).** The Yao decision language: valid
encoded instances whose table has Alice-first strict-alternation cost at most
the threshold. -/
def yaoLanguageDraft : Set (List Bool) :=
  { input | ∃ i, decodeInstance input = some i ∧
      Dalt .alice (ProtocolVerifier.tableGame i.rows i.cols i.table) ≤ i.threshold }

/-! ## Stack and placements -/

abbrev FStack (t lambda : ℕ) := WStack t lambda ⊕ HB

def wEmb (t lambda : ℕ) : WStack t lambda ↪ FStack t lambda := ⟨Sum.inl, Sum.inl_injective⟩

def hFun (t lambda : ℕ) : HB → FStack t lambda
  | .inl p => .inr (.inl p)
  | .inr j => (![.inl (.inr .rows), .inl (.inr .cols), .inr (.inr 2), .inr (.inr 3),
      .inr (.inr 4), .inl (.inr .output)] : Fin 6 → FStack t lambda) j

theorem hFun_injective (t lambda : ℕ) : Function.Injective (hFun t lambda) := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b
  · simpa [hFun] using h
  · fin_cases b <;> simp [hFun] at h
  · fin_cases a <;> simp [hFun] at h
  · fin_cases a <;> fin_cases b <;> simp_all [hFun]

def hEmb (t lambda : ℕ) : HB ↪ FStack t lambda := ⟨hFun t lambda, hFun_injective t lambda⟩

def bCell {t lambda : ℕ} : FStack t lambda := .inl (sN 5)
def thrCell {t lambda : ℕ} : FStack t lambda := .inr (.inr 2)
def scrCell {t lambda : ℕ} : FStack t lambda := .inr (.inr 3)

def cpB (t lambda : ℕ) : Fin 3 ↪ FStack t lambda :=
  ⟨![bCell, thrCell, scrCell], by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all [bCell, thrCell, scrCell]⟩

/-! ## The program -/

def stageA (t lambda : ℕ) := fun l => stackStmt (wEmb t lambda) (yaoMachine t lambda l)
def stageE (t lambda : ℕ) := fun l => stackStmt (hEmb t lambda) (HeaderA.prog l)
def stageD (t lambda : ℕ) :=
  SourceClauseFixedUnary.program (thrCell (t := t) (lambda := lambda)) (4 * t + 2)

def fDE (t lambda : ℕ) :=
  BitMachineRawSequence.program (stageD t lambda) (stageE t lambda) progStart () progCtl
def fCDE (t lambda : ℕ) :=
  BitMachineRawSequence.program (ExactParameterBranchInstall.copyProgram (cpB t lambda))
    (fDE t lambda) (BitMachineRawSequence.leftLabel (0 : SourceClauseFixedUnary.Label (4 * t + 2)))
    none ((), progCtl)
def fBCDE (t lambda : ℕ) :=
  BitMachineRawSequence.program (ExactParameterBranchInstall.copyProgram (cpB t lambda))
    (fCDE t lambda) (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) none
    (none, ((), progCtl))
/-- The framed Yao machine: ONE fixed program per `(t, lambda)`. -/
def yaoFramed (t lambda : ℕ) :=
  BitMachineRawSequence.program (stageA t lambda) (fBCDE t lambda)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) (yaoControl t lambda)
    ((none : Option Bool), ((none : Option Bool), ((), progCtl)))

def framedControl (t lambda : ℕ) :=
  (yaoControl t lambda, ((none : Option Bool), ((none : Option Bool), ((), progCtl))))

/-! ## Banks -/

/-- The input bank: the table machine's input on the left, all header cells empty. -/
def framedInit {t : ℕ} (lambda : ℕ) (x : YaoSource t) (tape : List Bool) :
    FStack t lambda → List Bool :=
  Sum.elim (initBank lambda x tape) (fun _ => [])

/-- The exact final writer bank of `physical_yao_table`. -/
def Wfin {t : ℕ} (lambda : ℕ) (x : YaoSource t)
    (bits : SerializedTape t (paddedEdgeBits x.2.1) lambda) : WStack t lambda → List Bool :=
  (MatrixTableWriter.ready (fun n => prepBank lambda x bits.val (.inl (.inl n)))
    (rowCount x.1 t (paddedEdgeBits x.2.1) lambda) (columnCount t (paddedEdgeBits x.2.1) lambda)
    0 0 0 0 [] ((materialize t lambda x.2.2 bits).bits ++ [])).contents

/-- The exact final bank of the framed machine. -/
def framedOut {t : ℕ} (lambda : ℕ) (x : YaoSource t)
    (bits : SerializedTape t (paddedEdgeBits x.2.1) lambda) : FStack t lambda → List Bool :=
  Sum.elim (Function.update (Function.update (Function.update (Wfin lambda x bits)
      (.inr .rows) []) (.inr .cols) [])
      (.inr .output) (encodeInstance (yaoInstanceDraft t lambda x bits)))
    (fun _ => [])

def frameClock {t : ℕ} (lambda : ℕ) (x : YaoSource t) : ℕ :=
  yaoClock lambda x + (2 * paddedEdgeBits x.2.1 + 2) + (2 * paddedEdgeBits x.2.1 + 2) +
    (4 * t + 2 + 1) +
    (UnaryBinaryEncoding.coefficient * (rowCount x.1 t (paddedEdgeBits x.2.1) lambda + 1) ^ 2 +
      UnaryBinaryEncoding.coefficient * (columnCount t (paddedEdgeBits x.2.1) lambda + 1) ^ 2 +
      UnaryBinaryEncoding.coefficient * (2 * paddedEdgeBits x.2.1 + 4 * t + 2 + 1) ^ 2 +
      (2 * (natField (rowCount x.1 t (paddedEdgeBits x.2.1) lambda) ++
        natField (columnCount t (paddedEdgeBits x.2.1) lambda) ++
        natField (2 * paddedEdgeBits x.2.1 + 4 * t + 2)).length + 2) + 3) + 4

theorem bank_wEmb {t lambda : ℕ} (f : WStack t lambda → List Bool) :
    bank (wEmb t lambda) (fun _ => []) f = Sum.elim f (fun _ => []) := by
  funext j
  rcases j with w | h
  · exact bank_at (wEmb t lambda) _ f w
  · rw [bank_outside]
    · rfl
    · rintro ⟨k, hk⟩
      simp [wEmb] at hk

theorem Wfin_b {t : ℕ} (lambda : ℕ) (x : YaoSource t)
    (bits : SerializedTape t (paddedEdgeBits x.2.1) lambda) :
    Wfin lambda x bits (sN 5) = List.replicate (paddedEdgeBits x.2.1) true := by
  change prepBank lambda x bits.val (sN 5) = _
  simp [prepBank, preludeFullOut, preludeOut, Function.update_apply, thetaIdx, thetaPlace,
    thetaFun, sN, st_eq_iff]

theorem Wfin_rows {t : ℕ} (lambda : ℕ) (x : YaoSource t)
    (bits : SerializedTape t (paddedEdgeBits x.2.1) lambda) :
    Wfin lambda x bits (.inr .rows) =
      List.replicate (rowCount x.1 t (paddedEdgeBits x.2.1) lambda) true := rfl

theorem Wfin_cols {t : ℕ} (lambda : ℕ) (x : YaoSource t)
    (bits : SerializedTape t (paddedEdgeBits x.2.1) lambda) :
    Wfin lambda x bits (.inr .cols) =
      List.replicate (columnCount t (paddedEdgeBits x.2.1) lambda) true := rfl

theorem Wfin_output {t : ℕ} (lambda : ℕ) (x : YaoSource t)
    (bits : SerializedTape t (paddedEdgeBits x.2.1) lambda) :
    Wfin lambda x bits (.inr .output) = (materialize t lambda x.2.2 bits).bits ++ [] := rfl

/-! ## Y8: the framed machine theorem -/

/-- Y8: ONE physical run of the fixed framed program from the code `encode x`
and the raw tape `bits.val` to the exact final bank, whose writer output cell
holds `encodeInstance (yaoInstanceDraft t lambda x bits)`. -/
theorem physical_yao_framed (t lambda : ℕ) (ht : 1 ≤ t) (x : YaoSource t)
    (bits : SerializedTape t (paddedEdgeBits x.2.1) lambda) :
    ∃ total ≤ frameClock lambda x, ∃ c',
      ((advance (yaoFramed t lambda))^[total])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel YaoHeaderParser.startLabel)),
          framedControl t lambda, framedInit lambda x bits.val⟩ :
          TM2.Cfg (fun _ : FStack t lambda => Bool) _ _) =
        ⟨none, c', framedOut lambda x bits⟩ := by
  classical
  -- stage A
  obtain ⟨tA, htA, cA, hA⟩ := physical_yao_table t lambda ht x bits
  have hA' := BitMachineStackRun.run (wEmb t lambda) (fun _ => []) (yaoMachine t lambda)
    ⟨some (BitMachineRawSequence.leftLabel YaoHeaderParser.startLabel), yaoControl t lambda,
      initBank lambda x bits.val⟩ tA
  rw [hA] at hA'
  simp only [stackCfg, bank_wEmb] at hA'
  obtain ⟨S0, hS0⟩ : ∃ S : FStack t lambda → List Bool,
      S = Sum.elim (Wfin lambda x bits) (fun _ => []) := ⟨_, rfl⟩
  have rA : ((advance (stageA t lambda))^[tA])
      (⟨some (BitMachineRawSequence.leftLabel YaoHeaderParser.startLabel), yaoControl t lambda,
        framedInit lambda x bits.val⟩ : TM2.Cfg (fun _ : FStack t lambda => Bool) _ _) =
      ⟨none, cA, S0⟩ := by rw [hS0]; exact hA'
  -- stage B
  obtain ⟨tB, htB, rB⟩ := copy_append_run (cpB t lambda) S0 (List.replicate (paddedEdgeBits x.2.1) true) []
    (by simp [cpB, bCell, hS0, Wfin_b, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]) (by simp [cpB, thrCell, hS0, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr])
    (by simp [cpB, scrCell, hS0, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr])
  obtain ⟨S1, hS1⟩ : ∃ S : FStack t lambda → List Bool,
      S = Function.update S0 (cpB t lambda 1) (List.replicate (paddedEdgeBits x.2.1) true ++ []) := ⟨_, rfl⟩
  rw [← hS1] at rB
  -- stage C
  obtain ⟨tC, htC, rC⟩ := copy_append_run (cpB t lambda) S1 (List.replicate (paddedEdgeBits x.2.1) true)
    (List.replicate (paddedEdgeBits x.2.1) true ++ [])
    (by simp [hS1, cpB, bCell, thrCell, hS0, Wfin_b, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr])
    (by simp [hS1, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr])
    (by simp [hS1, cpB, scrCell, thrCell, hS0, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr])
  obtain ⟨S2, hS2⟩ : ∃ S : FStack t lambda → List Bool, S = Function.update S1 (cpB t lambda 1)
      (List.replicate (paddedEdgeBits x.2.1) true ++ (List.replicate (paddedEdgeBits x.2.1) true ++ [])) := ⟨_, rfl⟩
  rw [← hS2] at rC
  -- stage D
  have rD := push_const_run (thrCell (t := t) (lambda := lambda)) S2 (4 * t + 2)
    (List.replicate (paddedEdgeBits x.2.1) true ++ (List.replicate (paddedEdgeBits x.2.1) true ++ []))
    (by simp [hS2, cpB, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr])
  obtain ⟨S3, hS3⟩ : ∃ S : FStack t lambda → List Bool,
      S = Function.update S0 (thrCell (t := t) (lambda := lambda)) (List.replicate (2 * paddedEdgeBits x.2.1 + 4 * t + 2) true) :=
    ⟨_, rfl⟩
  have hS3eq : Function.update S2 (thrCell (t := t) (lambda := lambda))
      (List.replicate (4 * t + 2) true ++
        (List.replicate (paddedEdgeBits x.2.1) true ++ (List.replicate (paddedEdgeBits x.2.1) true ++ []))) = S3 := by
    have hl : List.replicate (4 * t + 2) true ++
        (List.replicate (paddedEdgeBits x.2.1) true ++ (List.replicate (paddedEdgeBits x.2.1) true ++ [])) = List.replicate (2 * paddedEdgeBits x.2.1 + 4 * t + 2) true := by
      rw [List.append_nil, List.replicate_append_replicate, List.replicate_append_replicate]
      congr 1
      omega
    rw [hl, hS3, hS2, hS1]
    simp only [cpB, Function.Embedding.coeFn_mk, Matrix.cons_val_one, Matrix.cons_val_zero,
      Function.update_idem]
  rw [hS3eq] at rD
  -- stage E
  obtain ⟨tE, htE, rE⟩ := header_run_exact (rowCount x.1 t (paddedEdgeBits x.2.1) lambda) (columnCount t (paddedEdgeBits x.2.1) lambda) (2 * paddedEdgeBits x.2.1 + 4 * t + 2) (materialize t lambda x.2.2 bits).bits []
  have hEin : ∀ k, Hin (rowCount x.1 t (paddedEdgeBits x.2.1) lambda) (columnCount t (paddedEdgeBits x.2.1) lambda) (2 * paddedEdgeBits x.2.1 + 4 * t + 2) (materialize t lambda x.2.2 bits).bits [] k = S3 (hEmb t lambda k) := by
    intro k
    rcases k with k | j
    · simp [Hin, hEmb, hFun, hS3, hS0, thrCell, Function.update_apply, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
    · fin_cases j <;>
        simp [Hin, hEmb, hFun, hS3, hS0, thrCell, Function.update_apply, Wfin_rows, Wfin_cols,
          Wfin_output, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  have hE' := BitMachineStackRun.run (hEmb t lambda) S3 HeaderA.prog
    ⟨some progStart, progCtl, Hin (rowCount x.1 t (paddedEdgeBits x.2.1) lambda) (columnCount t (paddedEdgeBits x.2.1) lambda) (2 * paddedEdgeBits x.2.1 + 4 * t + 2) (materialize t lambda x.2.2 bits).bits []⟩ tE
  rw [rE] at hE'
  simp only [stackCfg] at hE'
  rw [bank_eq_self _ _ _ hEin] at hE'
  have hEout : bank (hEmb t lambda) S3 (Hout (rowCount x.1 t (paddedEdgeBits x.2.1) lambda) (columnCount t (paddedEdgeBits x.2.1) lambda) (2 * paddedEdgeBits x.2.1 + 4 * t + 2) (materialize t lambda x.2.2 bits).bits []) = framedOut lambda x bits := by
    funext j
    by_cases hk : ∃ m, hEmb t lambda m = j
    · obtain ⟨m, rfl⟩ := hk
      rw [bank_at]
      rcases m with p | i
      · simp [Hout, outH, hEmb, hFun, framedOut, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
      · fin_cases i <;>
          simp [Hout, outH, hEmb, hFun, framedOut, Function.update_apply, yaoInstanceDraft,
            encodeInstance, List.append_assoc, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
    · rw [bank_outside _ _ _ _ hk]
      have hn : ∀ m, hEmb t lambda m ≠ j := fun m h => hk ⟨m, h⟩
      rcases j with w | h
      · have h0 := hn (.inr 0); have h1 := hn (.inr 1); have h5 := hn (.inr 5)
        simp only [hEmb, hFun, Function.Embedding.coeFn_mk, ne_eq] at h0 h1 h5
        have hw0 : w ≠ .inr .rows := by intro e; apply h0; rw [e]; rfl
        have hw1 : w ≠ .inr .cols := by intro e; apply h1; rw [e]; rfl
        have hw5 : w ≠ .inr .output := by intro e; apply h5; rw [e]; rfl
        simp [hS3, hS0, thrCell, framedOut, Function.update_apply, hw0, hw1, hw5, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
      · have h2 := hn (.inr 2)
        have hne : (Sum.inr h : FStack t lambda) ≠ thrCell := fun e => h2 (by rw [e]; rfl)
        rw [hS3, Function.update_of_ne hne, hS0]
        rfl
  rw [hEout] at hE'
  have rE' : ((advance (stageE t lambda))^[tE])
      (⟨some progStart, progCtl, S3⟩ : TM2.Cfg (fun _ : FStack t lambda => Bool) _ _) =
      ⟨none, progCtl, framedOut lambda x bits⟩ := hE'
  -- sequencing
  obtain ⟨u1, hu1, q1⟩ := BitMachineRawSequence.runs (stageD t lambda) (stageE t lambda)
    (0 : SourceClauseFixedUnary.Label (4 * t + 2)) progStart () () progCtl progCtl
    S2 S3 _ _ _ rD rE'
  obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs
    (ExactParameterBranchInstall.copyProgram (cpB t lambda)) (fDE t lambda)
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel (0 : SourceClauseFixedUnary.Label (4 * t + 2)))
    none none ((), progCtl) ((), progCtl) S1 S2 _ _ _ rC q1
  obtain ⟨u3, hu3, q3⟩ := BitMachineRawSequence.runs
    (ExactParameterBranchInstall.copyProgram (cpB t lambda)) (fCDE t lambda)
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none none (none, ((), progCtl)) (none, ((), progCtl)) S0 S1 _ _ _ rB q2
  obtain ⟨u4, hu4, q4⟩ := BitMachineRawSequence.runs (stageA t lambda) (fBCDE t lambda)
    (BitMachineRawSequence.leftLabel YaoHeaderParser.startLabel)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (yaoControl t lambda) cA ((none : Option Bool), ((none : Option Bool), ((), progCtl)))
    (none, (none, ((), progCtl))) (framedInit lambda x bits.val) S0 _ _ _ rA q3
  refine ⟨u4, ?_, _, q4⟩
  simp only [List.length_replicate] at htB htC
  unfold frameClock
  omega

/-! ## The printed word and the DRAFT language -/

theorem framedOut_output {t : ℕ} (lambda : ℕ) (x : YaoSource t)
    (bits : SerializedTape t (paddedEdgeBits x.2.1) lambda) :
    framedOut lambda x bits (.inl (.inr .output)) =
      encodeInstance (yaoInstanceDraft t lambda x bits) := by
  simp [framedOut, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]

theorem selectorCount_pos (t b lambda : ℕ) : 0 < selectorCount t b lambda := by
  unfold selectorCount selectorSampleCount
  positivity

theorem payloadCount_pos (t b lambda : ℕ) : 0 < payloadCount t b lambda := by
  unfold payloadCount payloadSampleCount
  have hd : 0 < payloadDelta b t := by unfold payloadDelta; positivity
  have hn : 0 < 2 ^ b * (2 ^ t * 2 ^ t + 1) * (aliceNodes (b + 3 * t - 3) + 1) := by positivity
  exact Nat.div_pos (by omega) hd

/-- For a nonempty vertex set the printed instance is valid (all tapes). -/
theorem yaoInstanceDraft_valid {t : ℕ} (lambda : ℕ) (x : YaoSource t) (hv : 0 < x.1)
    (bits : SerializedTape t (paddedEdgeBits x.2.1) lambda) :
    (yaoInstanceDraft t lambda x bits).Valid := by
  refine ⟨?_, ?_, (materialize t lambda x.2.2 bits).length⟩
  · exact Nat.mul_pos hv (selectorCount_pos _ _ _)
  · exact Nat.mul_pos (Nat.mul_pos (by positivity) (by positivity)) (payloadCount_pos _ _ _)

theorem decode_framed {t : ℕ} (lambda : ℕ) (x : YaoSource t) (hv : 0 < x.1)
    (bits : SerializedTape t (paddedEdgeBits x.2.1) lambda) :
    decodeInstance (encodeInstance (yaoInstanceDraft t lambda x bits)) =
      some (yaoInstanceDraft t lambda x bits) :=
  decode_encode _ (yaoInstanceDraft_valid lambda x hv bits)

/-- The printed word is in the DRAFT language iff the printed table has
`Dalt .alice ≤ B`. -/
theorem framed_language_iff {t : ℕ} (lambda : ℕ) (x : YaoSource t) (hv : 0 < x.1)
    (bits : SerializedTape t (paddedEdgeBits x.2.1) lambda) :
    encodeInstance (yaoInstanceDraft t lambda x bits) ∈ yaoLanguageDraft ↔
      Dalt .alice (materialize t lambda x.2.2 bits).matrix ≤
        2 * paddedEdgeBits x.2.1 + 4 * t + 2 := by
  have hd := decode_framed lambda x hv bits
  constructor
  · rintro ⟨i, hi, hcost⟩
    rw [hd] at hi
    cases Option.some.inj hi
    simpa only [yaoInstanceDraft, Paper2.EncodedSelectedOutput.tableGame_eq_matrix] using hcost
  · intro hcost
    refine ⟨yaoInstanceDraft t lambda x bits, hd, ?_⟩
    simpa only [yaoInstanceDraft, Paper2.EncodedSelectedOutput.tableGame_eq_matrix] using hcost

end Paper2.YaoFrame

end

#print axioms Paper2.YaoFrame.hFun_injective
#print axioms Paper2.YaoFrame.bank_wEmb
#print axioms Paper2.YaoFrame.Wfin_b
#print axioms Paper2.YaoFrame.physical_yao_framed
#print axioms Paper2.YaoFrame.framedOut_output
#print axioms Paper2.YaoFrame.selectorCount_pos
#print axioms Paper2.YaoFrame.payloadCount_pos
#print axioms Paper2.YaoFrame.yaoInstanceDraft_valid
#print axioms Paper2.YaoFrame.decode_framed
#print axioms Paper2.YaoFrame.framed_language_iff
