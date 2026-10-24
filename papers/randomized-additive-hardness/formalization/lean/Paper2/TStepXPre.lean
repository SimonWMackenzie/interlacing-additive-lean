import Paper2.SrcX
import Paper2.SrcReq
import Paper2.TemplateStepRun

/-! Unit 3, ROOT DECISION R5: the one-level composite restated over the
extended bank `JT = TemplateStep.J ⊕ SrcX.JX` (never editing the admitted
`TemplateStep`). This module: the placement `ιE` of the source-arm bank
(`srcA ↦ srcCell`, `fwA ↦ r1 tagC`, `ccC ↦ nC 4`, `rcC ↦ nC 7`, every other
cell to the `SrcX.JX` copy `E`), the ONE fixed program `stepX`, and the
shared prefix run `pre_run` (the admitted `TemplateStep.pre` = navigation
join ; request selection, exactly as in the admitted `template_step`). -/

set_option maxHeartbeats 32000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.TemplateStepX

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource
open RecursiveLabelCodecScratch RecursiveEntries
open BitMachineRawSequence (leftLabel)
open Paper2.TemplateStep (J RS nC r1 r2 lC pcC myJ iN i1 i2 eL srcCell navP rs1 pre arm
  armStart armCtl)

abbrev JT := J ⊕ SrcX.JX

def inJ : J ↪ JT := ⟨Sum.inl, Sum.inl_injective⟩

def ccX : SrcX.JX := .inl (.inl (.inl FetchIndexed.ccC))
def rcX : SrcX.JX := .inl (.inl (.inl FetchIndexed.rcC))

/-- The placement of the source-arm bank (root decision R5). -/
def ιEf (z : SrcX.JX) : JT :=
  if z = SrcX.srcAX then .inl srcCell
  else if z = SrcX.fwX then .inl (r1 RequestSelect.tagC)
  else if z = ccX then .inl (nC 4)
  else if z = rcX then .inl (nC 7)
  else .inr z

theorem ιEf_injective : Function.Injective ιEf := by
  intro a b h
  unfold ιEf at h
  split_ifs at h <;> simp_all [srcCell, r1, nC, RequestSelect.tagC, RequestSelect.rowC]

def ιE : SrcX.JX ↪ JT := ⟨ιEf, ιEf_injective⟩

theorem ιE_srcA : ιE SrcX.srcAX = .inl srcCell := by
  change ιEf SrcX.srcAX = _; unfold ιEf; simp
theorem ιE_fw : ιE SrcX.fwX = .inl (r1 RequestSelect.tagC) := by
  change ιEf SrcX.fwX = _; unfold ιEf; simp [SrcX.fwX, SrcX.srcAX, SrcU.srcA]
theorem ιE_cc : ιE ccX = .inl (nC 4) := by
  change ιEf ccX = _; unfold ιEf; simp [ccX, SrcX.fwX, SrcX.srcAX, SrcU.srcA, FetchIndexed.ccC,
    FetchIndexed.fwC]
theorem ιE_rc : ιE rcX = .inl (nC 7) := by
  change ιEf rcX = _; unfold ιEf; simp [ccX, rcX, SrcX.fwX, SrcX.srcAX, SrcU.srcA, FetchIndexed.ccC,
    FetchIndexed.fwC, FetchIndexed.rcC]
theorem ιE_other (z : SrcX.JX) (h1 : z ≠ SrcX.srcAX) (h2 : z ≠ SrcX.fwX) (h3 : z ≠ ccX)
    (h4 : z ≠ rcX) : ιE z = .inr z := by
  change ιEf z = _; unfold ιEf; simp [h1, h2, h3, h4]

/-- A `J` cell outside the four placed cells is not in the range of `ιE`. -/
theorem ιE_range_inl (xx : J) (h1 : xx ≠ srcCell) (h2 : xx ≠ r1 RequestSelect.tagC)
    (h3 : xx ≠ nC 4) (h4 : xx ≠ nC 7) : ¬ ∃ z, ιE z = .inl xx := by
  rintro ⟨z, hz⟩
  change ιEf z = _ at hz
  unfold ιEf at hz
  split_ifs at hz <;> simp_all

/-- The `E` copies of the placed cells are not in the range of `ιE`. -/
theorem ιE_range_srcA : ¬ ∃ z, ιE z = .inr SrcX.srcAX := by
  rintro ⟨z, hz⟩
  change ιEf z = _ at hz
  unfold ιEf at hz
  split_ifs at hz with e1 <;> simp_all

theorem liftT {Kk L V : Type*} [DecidableEq Kk] (ι : Kk ↪ JT)
    (P : L → TM2.Stmt (fun _ : Kk => Bool) L V)
    (W : JT → List Bool) (S T : Kk → List Bool) (hS : ∀ k, S k = W (ι k)) (l : L) (v v' : V)
    (t : ℕ)
    (hrun : ((advance P)^[t]) (⟨some l, v, S⟩ : TM2.Cfg (fun _ : Kk => Bool) L V) =
      ⟨none, v', T⟩) :
    ((advance (fun l => stackStmt ι (P l)))^[t])
        (⟨some l, v, W⟩ : TM2.Cfg (fun _ : JT => Bool) L V) =
      ⟨none, v', bank ι W T⟩ := by
  have hs := BitMachineStackRun.run ι W P (⟨some l, v, S⟩ : TM2.Cfg (fun _ : Kk => Bool) L V) t
  rw [hrun] at hs
  simp only [stackCfg] at hs
  rwa [bank_eq_self ι W S hS] at hs

theorem bank_inJ (X : J → List Bool) (Y : SrcX.JX → List Bool) (T : J → List Bool) :
    bank inJ (Sum.elim X Y) T = Sum.elim T Y := by
  funext j
  cases j with
  | inl j => exact bank_at inJ _ T j
  | inr j => exact bank_outside inJ _ T (.inr j) (by rintro ⟨k, hk⟩; cases hk)

/-! ### The ONE fixed program -/

def cpCf : Fin 3 → JT := ![.inr SrcX.lblX, .inl (r2 RequestSelect.rowC), .inr SrcX.srcAX]
theorem cpCf_injective : Function.Injective cpCf := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [cpCf, SrcX.lblX, SrcX.srcAX, SrcU.srcA]
def cpC : Fin 3 ↪ JT := ⟨cpCf, cpCf_injective⟩

def cpRf : Fin 3 → JT := ![.inl srcCell, .inl (r2 RequestSelect.tagC), .inr SrcX.srcAX]
theorem cpRf_injective : Function.Injective cpRf := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [cpRf, srcCell, r1, r2, RequestSelect.tagC,
    RequestSelect.rowC]
def cpR : Fin 3 ↪ JT := ⟨cpRf, cpRf_injective⟩

def preX := fun l => stackStmt inJ (pre l)
def armX := fun l => stackStmt inJ (arm l)
def srcXT := fun l => stackStmt ιE (SrcX.srcX l)
def cp1 := MatrixStage4ScalarPreparationOps.copyProgram cpC
def cp2 := MatrixStage4ScalarPreparationOps.copyProgram cpR
def srcP1 := BitMachineRawSequence.program srcXT cp1 BitMachineCopy.Label.scan SrcX.srcXCtl
  (none : Option Bool)
/-- The source-case arm over `JT`: the three-tag source arm placed by `ιE`,
then the two charged copies of its outputs into the request output cells. -/
def srcP := BitMachineRawSequence.program srcP1 cp2 BitMachineCopy.Label.scan
  (SrcX.srcXCtl, (none : Option Bool)) (none : Option Bool)
def srcPStart := FetchIndexed.labelOf srcP (leftLabel (leftLabel (.inl ())))
def srcPCtl := ((SrcX.srcXCtl, (none : Option Bool)), (none : Option Bool))

/-- One request level over `JT`, with the source arm discharged: ONE fixed program. -/
def stepX :=
  BitMachineRawSequence.program preX
    (TagDispatch.ifProgram (inJ srcCell) armX srcP armStart srcPStart armCtl srcPCtl) (.inl ())
    (NavJoin.ctl, RequestSelect.startControl) ((none : Option Bool), (armCtl, srcPCtl))

def stepXCtl := ((NavJoin.ctl, RequestSelect.startControl),
  ((none : Option Bool), (armCtl, srcPCtl)))

/-! ### Banks and the shared prefix -/

variable {n p s q₁ q₂ w Q : ℕ} [NeZero n] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]

/-- The level entry bank on `J` (the admitted `template_step`'s `W0`). -/
def W0f (k : ℕ)
    (x : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q (k + 1))
    (y : Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q (k + 1)) :
    J → List Bool :=
  Sum.elim (NavJoin.jb (NavJoin.inVec
      (encodeCode (seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)).1)
      (encodeCode (seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)).2)))
    (Sum.elim (RequestSelect.mk [] [] (RequestSelect.vec
      ((defaultCarrierCodecs n p s q₁ q₂ w Q (k + 1)).1.encode x)
      ((defaultCarrierCodecs n p s q₁ q₂ w Q (k + 1)).2.encode y) [] [] [] [] [])) (fun _ => []))

/-- The bank after the prefix (the admitted `template_step`'s `W2`). -/
def W2f (k : ℕ)
    (x : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q (k + 1))
    (y : Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q (k + 1)) :
    J → List Bool :=
  bank i1 (bank iN (W0f k x y) (NavJoin.jb (NavJoin.outVec n p s q₁ q₂ w Q k)))
    (RequestSelect.mk ((taggedColumnCodec q₁ q₂ s (defaultCarrierCodecs n p s q₁ q₂ w Q k).2).encode
        (x y.1).2)
      ((rawRowCodec q₁ q₂ s (defaultCarrierCodecs n p s q₁ q₂ w Q k).1
        (defaultItemCodec n s)).encode (y.2 (x y.1).1))
      (RequestSelect.vec ((defaultCarrierCodecs n p s q₁ q₂ w Q (k + 1)).1.encode x)
        ((defaultCarrierCodecs n p s q₁ q₂ w Q (k + 1)).2.encode y)
        (encodeCode (.append (.ticket w)
          (taggedCode q₁ q₂ s (seedRecursiveCodes n p s q₁ q₂ w Q k).2)))
        (encodeCode (graphRowsCode (V := Fin n) q₁ q₂ s (seedRecursiveCodes n p s q₁ q₂ w Q k).1))
        (List.replicate y.1.val true)
        ((piCodec (rawRowCodec q₁ q₂ s (defaultCarrierCodecs n p s q₁ q₂ w Q k).1
          (defaultItemCodec n s)) w).encode y.2)
        (List.replicate (x y.1).1.val true)))

/-- The request-selection clock of the prefix (as in `template_step`). -/
def selClock (k : ℕ)
    (x : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q (k + 1))
    (y : Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q (k + 1)) :
    ℕ :=
  RequestSelect.clock ((defaultCarrierCodecs n p s q₁ q₂ w Q (k + 1)).2.encode y) y.1.val
    (x y.1).1.val
    (.append (.ticket w) (taggedCode q₁ q₂ s (seedRecursiveCodes n p s q₁ q₂ w Q k).2))
    (graphRowsCode (V := Fin n) q₁ q₂ s (seedRecursiveCodes n p s q₁ q₂ w Q k).1)
    (List.ofFn (fun j => (prodCodec (finCodec w)
      (taggedColumnCodec q₁ q₂ s (defaultCarrierCodecs n p s q₁ q₂ w Q k).2)).encode (x j)))
    (List.ofFn (fun i => (rawRowCodec q₁ q₂ s (defaultCarrierCodecs n p s q₁ q₂ w Q k).1
      (defaultItemCodec n s)).encode (y.2 i)))

/-- The shared prefix: the admitted `TemplateStep.pre` from the level entry bank. -/
theorem pre_run [NeZero s] (hp : 0 < p) (hs : 4 ≤ s) (k : ℕ)
    (x : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q (k + 1))
    (y : Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q (k + 1)) :
    ∃ t ≤ NavJoin.joinBound n p s q₁ q₂ w Q k + selClock k x y + 1, ∃ v,
      ((advance pre)^[t])
        (⟨some (leftLabel NavJoin.startLabel), (NavJoin.ctl, RequestSelect.startControl),
          W0f k x y⟩ : TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, v, W2f k x y⟩ := by
  obtain ⟨t1, ht1, p1⟩ := NavJoin.join_run (n := n) (p := p) (s := s) (q₁ := q₁) (q₂ := q₂)
    (w := w) (Q := Q) (NeZero.pos Q) (NeZero.pos w) (by omega) (NeZero.pos q₂) k
  have l1 := TemplateStep.lift iN NavJoin.program (W0f k x y) _ _ (fun _ => rfl) _ _ _ _ p1
  obtain ⟨t2, ht2, v2, p2⟩ := RequestSelectActual.select_run (n := n) (p := p) (s := s)
    (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) hp hs k x y
  have hW1 : bank iN (W0f k x y) (NavJoin.jb (NavJoin.outVec n p s q₁ q₂ w Q k)) =
      Sum.elim (NavJoin.jb (NavJoin.outVec n p s q₁ q₂ w Q k))
        (fun z => W0f k x y (.inr z)) := TemplateStep.W1_eq _ _
  have hS1 : ∀ kk, RequestSelect.mk [] [] (RequestSelect.vec
      ((defaultCarrierCodecs n p s q₁ q₂ w Q (k + 1)).1.encode x)
      ((defaultCarrierCodecs n p s q₁ q₂ w Q (k + 1)).2.encode y)
      (encodeCode (.append (.ticket w)
        (taggedCode q₁ q₂ s (seedRecursiveCodes n p s q₁ q₂ w Q k).2)))
      (encodeCode (graphRowsCode (V := Fin n) q₁ q₂ s (seedRecursiveCodes n p s q₁ q₂ w Q k).1))
      [] [] []) kk =
      bank iN (W0f k x y) (NavJoin.jb (NavJoin.outVec n p s q₁ q₂ w Q k)) (i1 kk) := by
    intro kk
    rw [hW1]
    rcases kk with j | j | q
    · rfl
    · rfl
    · fin_cases q <;> rfl
  have l2 := TemplateStep.lift i1 RequestSelect.program _ _ _ hS1 _ _ _ _ p2
  obtain ⟨u1, hu1, q1⟩ := BitMachineRawSequence.runs navP rs1 NavJoin.startLabel
    RequestSelect.startLabel NavJoin.ctl NavJoin.ctl RequestSelect.startControl v2
    _ _ _ _ _ l1 l2
  refine ⟨u1, ?_, _, q1⟩
  have ht1' : t1 ≤ NavJoin.joinBound n p s q₁ q₂ w Q k := ht1
  have ht2' : t2 ≤ selClock k x y := ht2
  omega

/-- The `r2` cells are blank after the prefix. -/
theorem W2f_r2 (k : ℕ)
    (x : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q (k + 1))
    (y : Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q (k + 1))
    (xx : RS) : W2f k x y (r2 xx) = [] := by
  unfold W2f
  rw [TemplateStep.i1_off _ _ _ (by intro yy; simp [r2, r1]) (by simp [r2, nC])
    (by simp [r2, nC]), show r2 xx = .inr (.inr (.inl xx)) from rfl,
    TemplateStep.bank_iN_inr]
  rfl

end

#print axioms ιEf_injective
#print axioms ιE_srcA
#print axioms ιE_fw
#print axioms ιE_cc
#print axioms ιE_rc
#print axioms ιE_other
#print axioms ιE_range_inl
#print axioms ιE_range_srcA
#print axioms liftT
#print axioms bank_inJ
#print axioms cpCf_injective
#print axioms cpRf_injective
#print axioms pre_run
#print axioms W2f_r2

end Paper2.TemplateStepX
