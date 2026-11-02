import EthInapproximability.CurrentPaper.SourceCSPPositiveSuffix
import EthInapproximability.CurrentPaper.SourceCSPRowQueryFrame

/-!
# Physical bridge from the guarded header to the row controller

The left bank retains the actual header-parser output. Four literal
source-preserving copies and one status pop prepare the right bank for a
reusable row loop. The fifth extra stack is copy scratch. No uncharged
data reconfiguration is used.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPHeaderRowBridge

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev RowOuter (q : Nat) := SourceCSPRowQueryFrame.Stack q ⊕ Fin 4
abbrev Stack (q : Nat) := SourceCSPPositiveHeader.Stack ⊕
  (SourceCSPRowQueryFrame.Stack q ⊕ Fin 5)

def headerEmbedding {q : Nat} : SourceCSPPositiveHeader.Stack ↪ Stack q where
  toFun := Sum.inl
  inj' := by intro x y h; exact Sum.inl.inj h

def rowEmbedding {q : Nat} : RowOuter q ↪ Stack q where
  toFun
    | .inl k => .inr (.inl k)
    | .inr k => .inr (.inr ⟨k.val, by omega⟩)
  inj' := by
    intro x y h
    cases x <;> cases y <;> simp_all [Fin.ext_iff]

def scratch {q : Nat} : Stack q := .inr (.inr 4)
def source {q : Nat} : Stack q := .inl SourceCSPPositiveSuffix.rowSlot
def count {q : Nat} : Stack q := .inl (.inl (.inr 6))
def capSource {q : Nat} : Stack q := .inl (.inr 6)
def rowSource {q : Nat} : Stack q := .inr (.inl (.inr 0))
def rowCap {q : Nat} : Stack q := .inr (.inl (.inr 3))
def loopCount {q : Nat} : Stack q := .inr (.inr 0)
def loopCap {q : Nat} : Stack q := .inr (.inr 1)

def initial {q : Nat} (input : List Bool) : Stack q → List Bool
  | .inl k => SourceCSPPositiveHeader.initial input k
  | .inr _ => []

def copyEmbedding {q : Nat} (src dst : Stack q) (hs : src ≠ dst)
    (hx : src ≠ scratch) (hy : dst ≠ scratch) : Fin 3 ↪ Stack q where
  toFun k := if k = 0 then src else if k = 1 then dst else scratch
  inj' := by intro x y h; fin_cases x <;> fin_cases y <;> simp_all

def copyProgram {q : Nat} (src dst : Stack q) (hs : src ≠ dst)
    (hx : src ≠ scratch) (hy : dst ≠ scratch)
    (l : BitMachineCopy.Label) :
    TM2.Stmt (fun _ : Stack q => Bool) BitMachineCopy.Label (Option Bool) :=
  stmt (copyEmbedding src dst hs hx hy) id id id none (BitMachineCopy.program l)

theorem copy_framed {q : Nat} (src dst : Stack q) (hs : src ≠ dst)
    (hx : src ≠ scratch) (hy : dst ≠ scratch)
    (before : Stack q → List Bool) (word : List Bool)
    (hsrc : before src = word) (hdst : before dst = [])
    (hscratch : before scratch = []) :
    ∃ t S, t ≤ 2 * word.length + 2 ∧
      ((advance (copyProgram src dst hs hx hy))^[t])
        (⟨some .scan, none, before⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) BitMachineCopy.Label (Option Bool)) =
        ⟨none, none, S⟩ ∧
      S src = word ∧ S dst = word ∧ S scratch = [] ∧
      (∀ k, k ≠ src → k ≠ dst → k ≠ scratch → S k = before k) := by
  let ι := copyEmbedding src dst hs hx hy
  let localCfg := BitMachineCopy.cfg (some .scan) none word [] []
  have hhalt : (((advance BitMachineCopy.program)^[2 * word.length + 2])
      localCfg).l = none := by
    rw [show ((advance BitMachineCopy.program)^[2 * word.length + 2])
      localCfg = BitMachineCopy.cfg none none word word [] from by
      simpa only [BitMachineCopy.run, localCfg, List.append_nil] using
        BitMachineCopy.run_correct none word []]
    rfl
  obtain ⟨t, ht, hr⟩ := outputs ι before id id id (fun _ => rfl)
    none BitMachineCopy.program (copyProgram src dst hs hx hy)
    (fun _ => rfl) localCfg (2 * word.length + 2) hhalt
  have hstart : cfg ι before id id none localCfg =
      (⟨some .scan, none, before⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) BitMachineCopy.Label (Option Bool)) := by
    simp only [cfg, stackCfg, BitMachineInline.cfg, localCfg,
      BitMachineCopy.cfg, id_eq]
    congr 1
    apply bank_eq_self
    intro k
    fin_cases k <;> simp [ι, copyEmbedding, BitMachineCopy.stackContents,
      hsrc, hdst, hscratch]
  have hlocal : ((advance BitMachineCopy.program)^[2 * word.length + 2])
      localCfg = BitMachineCopy.cfg none none word word [] :=
    by simpa only [BitMachineCopy.run, localCfg, List.append_nil] using
      BitMachineCopy.run_correct none word []
  rw [hstart, hlocal] at hr
  let S := bank ι before (BitMachineCopy.stackContents word word [])
  refine ⟨t, S, ht, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [copyProgram, S, cfg, stackCfg, BitMachineInline.cfg,
      BitMachineCopy.cfg, id_eq, Option.map_none] using hr
  · change bank ι before _ (ι 0) = _
    rw [bank_at]
    rfl
  · change bank ι before _ (ι 1) = _
    rw [bank_at]
    rfl
  · change bank ι before _ (ι 2) = _
    rw [bank_at]
    rfl
  · intro k hk0 hk1 hk2
    apply bank_outside
    rintro ⟨i, hi⟩
    fin_cases i <;> simp [ι, copyEmbedding] at hi
    · exact hk0 hi.symm
    · exact hk1 hi.symm
    · exact hk2 hi.symm

theorem copy_exact {q : Nat} (src dst : Stack q) (hs : src ≠ dst)
    (hx : src ≠ scratch) (hy : dst ≠ scratch)
    (before : Stack q → List Bool) (word : List Bool)
    (hsrc : before src = word) (hdst : before dst = [])
    (hscratch : before scratch = []) :
    ∃ t, t ≤ 2 * word.length + 2 ∧
      ((advance (copyProgram src dst hs hx hy))^[t])
        (⟨some .scan, none, before⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) BitMachineCopy.Label (Option Bool)) =
        ⟨none, none, Function.update before dst word⟩ := by
  obtain ⟨t, S, ht, hr, hsrc', hdst', hscratch', hout⟩ :=
    copy_framed src dst hs hx hy before word hsrc hdst hscratch
  have heq : S = Function.update before dst word := by
    funext k
    by_cases hk0 : k = src
    · subst k
      rw [hsrc']
      simp [hs, hsrc]
    by_cases hk1 : k = dst
    · subst k
      simpa using hdst'
    by_cases hk2 : k = scratch
    · subst k
      rw [hscratch']
      rw [Function.update_of_ne hk1, hscratch]
    rw [hout k hk0 hk1 hk2, Function.update_of_ne hk1]
  exact ⟨t, ht, hr.trans (by rw [heq])⟩

def rowCopyProgram {q : Nat} :=
  copyProgram (q := q) (source (q := q)) rowSource
    (by simp [source, rowSource]) (by simp [source, scratch])
    (by simp [rowSource, scratch])

def capPopProgram {q : Nat} (_ : Unit) :
    TM2.Stmt (fun _ : Stack q => Bool) Unit (Option Bool) :=
  .pop capSource (fun _ b => b) .halt

theorem cap_pop {q : Nat} (before : Stack q → List Bool) (cap : List Bool)
    (hcap : before capSource = true :: cap) :
    advance capPopProgram
      (⟨some (), none, before⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) Unit (Option Bool)) =
      ⟨none, some true, Function.update before capSource cap⟩ := by
  simp [advance, TM2.step, TM2.stepAux, capPopProgram, hcap]

def capRowProgram {q : Nat} :=
  copyProgram (q := q) (capSource (q := q)) rowCap
    (by simp [capSource, rowCap]) (by simp [capSource, scratch])
    (by simp [rowCap, scratch])

def capLoopProgram {q : Nat} :=
  copyProgram (q := q) (capSource (q := q)) loopCap
    (by simp [capSource, loopCap]) (by simp [capSource, scratch])
    (by simp [loopCap, scratch])

def countProgram {q : Nat} :=
  copyProgram (q := q) (count (q := q)) loopCount
    (by simp [count, loopCount]) (by simp [count, scratch])
    (by simp [loopCount, scratch])

def stage2 {q : Nat} :=
  BitMachineRawSequence.program (rowCopyProgram (q := q)) capPopProgram ()
    (none : Option Bool) (none : Option Bool)

def stage3 {q : Nat} :=
  BitMachineRawSequence.program (stage2 (q := q)) capRowProgram .scan
    ((none, none) : Option Bool × Option Bool) (none : Option Bool)

def stage4 {q : Nat} :=
  BitMachineRawSequence.program (stage3 (q := q)) capLoopProgram .scan
    (((none, none), none) : (Option Bool × Option Bool) × Option Bool)
    (none : Option Bool)

def prepareProgram {q : Nat} :=
  BitMachineRawSequence.program (stage4 (q := q)) countProgram .scan
    ((((none, none), none), none) :
      ((Option Bool × Option Bool) × Option Bool) × Option Bool)
    (none : Option Bool)

abbrev Label2 := BitMachineRawSequence.Label BitMachineCopy.Label Unit
abbrev Label3 := BitMachineRawSequence.Label Label2 BitMachineCopy.Label
abbrev Label4 := BitMachineRawSequence.Label Label3 BitMachineCopy.Label
abbrev Label5 := BitMachineRawSequence.Label Label4 BitMachineCopy.Label
abbrev Control2 := Option Bool × Option Bool
abbrev Control3 := Control2 × Option Bool
abbrev Control4 := Control3 × Option Bool
abbrev Control5 := Control4 × Option Bool

def start {q : Nat} (before : Stack q → List Bool) :
    TM2.Cfg (fun _ : Stack q => Bool) Label5 Control5 :=
  ⟨some (.inl (.inl (.inl (.inl .scan)))),
    ((((none, none), none), none), none), before⟩

def prepared {q : Nat} (before : Stack q → List Bool)
    (rows cap unaryM : List Bool) : Stack q → List Bool :=
  Function.update
    (Function.update
      (Function.update
      (Function.update
        (Function.update before rowSource rows) capSource cap)
        rowCap cap) loopCap cap) loopCount unaryM

theorem prepare_run {q : Nat} (before : Stack q → List Bool)
    (rows cap unaryM : List Bool)
    (hrows : before source = rows)
    (hcap : before capSource = true :: cap)
    (hm : before count = unaryM)
    (hblank : ∀ k : SourceCSPRowQueryFrame.Stack q ⊕ Fin 5,
      before (.inr k) = []) :
    ∃ t, t ≤ 2 * rows.length + 4 * cap.length +
        2 * unaryM.length + 13 ∧
      ((advance (prepareProgram (q := q)))^[t]) (start before) =
        ⟨none, ((((none, none), none), none), none),
          prepared before rows cap unaryM⟩ := by
  let S1 := Function.update before rowSource rows
  let S2 := Function.update S1 capSource cap
  let S3 := Function.update S2 rowCap cap
  let S4 := Function.update S3 loopCap cap
  let S5 := Function.update S4 loopCount unaryM
  obtain ⟨t1, ht1, hr1⟩ := copy_exact source rowSource
    (by simp [source, rowSource]) (by simp [source, scratch])
    (by simp [rowSource, scratch]) before rows hrows
    (hblank (.inl (.inr 0))) (hblank (.inr 4))
  change ((advance rowCopyProgram)^[t1])
    (⟨some .scan, none, before⟩ :
      TM2.Cfg (fun _ : Stack q => Bool) BitMachineCopy.Label (Option Bool)) =
    ⟨none, none, S1⟩ at hr1
  have hcap1 : S1 capSource = true :: cap := by
    change (Function.update before rowSource rows) capSource = _
    rw [Function.update_of_ne (by simp [capSource, rowSource])]
    exact hcap
  have hr2 : ((advance capPopProgram)^[1])
      (⟨some (), none, S1⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) Unit (Option Bool)) =
      ⟨none, some true, S2⟩ := by
    exact cap_pop S1 cap hcap1
  have hcap2 : S2 capSource = cap := by simp [S2, capSource]
  have hrowCap2 : S2 rowCap = [] := by
    simp [S2, S1, rowCap, capSource, rowSource, hblank (.inl (.inr 3))]
  have hscratch2 : S2 scratch = [] := by
    simp [S2, S1, scratch, capSource, rowSource, hblank (.inr 4)]
  obtain ⟨t3, ht3, hr3⟩ := copy_exact capSource rowCap
    (by simp [capSource, rowCap]) (by simp [capSource, scratch])
    (by simp [rowCap, scratch]) S2 cap hcap2 hrowCap2 hscratch2
  change ((advance capRowProgram)^[t3])
    (⟨some .scan, none, S2⟩ :
      TM2.Cfg (fun _ : Stack q => Bool) BitMachineCopy.Label (Option Bool)) =
    ⟨none, none, S3⟩ at hr3
  have hcap3 : S3 capSource = cap := by
    change (Function.update S2 rowCap cap) capSource = _
    rw [Function.update_of_ne (by simp [capSource, rowCap])]
    exact hcap2
  have hloopCap3 : S3 loopCap = [] := by
    simp [S3, S2, S1, loopCap, rowCap, capSource, rowSource,
      hblank (.inr 1)]
  have hscratch3 : S3 scratch = [] := by
    change (Function.update S2 rowCap cap) scratch = _
    rw [Function.update_of_ne (by simp [scratch, rowCap])]
    exact hscratch2
  obtain ⟨t4, ht4, hr4⟩ := copy_exact capSource loopCap
    (by simp [capSource, loopCap]) (by simp [capSource, scratch])
    (by simp [loopCap, scratch]) S3 cap hcap3 hloopCap3 hscratch3
  change ((advance capLoopProgram)^[t4])
    (⟨some .scan, none, S3⟩ :
      TM2.Cfg (fun _ : Stack q => Bool) BitMachineCopy.Label (Option Bool)) =
    ⟨none, none, S4⟩ at hr4
  have hm4 : S4 count = unaryM := by
    change (Function.update (Function.update
      (Function.update (Function.update before rowSource rows) capSource cap)
      rowCap cap) loopCap cap) count = _
    rw [Function.update_of_ne (by simp [count, loopCap]),
      Function.update_of_ne (by simp [count, rowCap]),
      Function.update_of_ne (by simp [count, capSource]),
      Function.update_of_ne (by simp [count, rowSource])]
    exact hm
  have hloopCount4 : S4 loopCount = [] := by
    simp [S4, S3, S2, S1, loopCount, loopCap, rowCap, capSource,
      rowSource, hblank (.inr 0)]
  have hscratch4 : S4 scratch = [] := by
    change (Function.update S3 loopCap cap) scratch = _
    rw [Function.update_of_ne (by simp [scratch, loopCap])]
    exact hscratch3
  obtain ⟨t5, ht5, hr5⟩ := copy_exact count loopCount
    (by simp [count, loopCount]) (by simp [count, scratch])
    (by simp [loopCount, scratch]) S4 unaryM hm4 hloopCount4 hscratch4
  change ((advance countProgram)^[t5])
    (⟨some .scan, none, S4⟩ :
      TM2.Cfg (fun _ : Stack q => Bool) BitMachineCopy.Label (Option Bool)) =
    ⟨none, none, S5⟩ at hr5
  obtain ⟨t12, ht12, hr12⟩ := BitMachineRawSequence.runs
    rowCopyProgram capPopProgram .scan ()
    (none : Option Bool) none (none : Option Bool) (some true)
    before S1 S2 t1 1 hr1 hr2
  obtain ⟨t123, ht123, hr123⟩ := BitMachineRawSequence.runs
    stage2 capRowProgram (.inl .scan : Label2) .scan
    ((none, none) : Control2) (none, some true)
    (none : Option Bool) none before S2 S3 t12 t3 hr12 hr3
  obtain ⟨t1234, ht1234, hr1234⟩ := BitMachineRawSequence.runs
    stage3 capLoopProgram (.inl (.inl .scan) : Label3) .scan
    (((none, none), none) : Control3) ((none, none), none)
    (none : Option Bool) none before S3 S4 t123 t4 hr123 hr4
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    stage4 countProgram (.inl (.inl (.inl .scan)) : Label4) .scan
    ((((none, none), none), none) : Control4)
    (((none, none), none), none)
    (none : Option Bool) none before S4 S5 t1234 t5 hr1234 hr5
  refine ⟨t, ?_, ?_⟩
  · omega
  · simpa only [prepareProgram, start, prepared, S5, S4, S3, S2, S1] using hr

def ready {q : Nat} (rows cap unaryM : List Bool) : RowOuter q → List Bool
  | .inl k => SourceCSPRowQueryFrame.initial rows cap k
  | .inr k => if k = 0 then unaryM else if k = 1 then cap else []

theorem prepared_ready {q : Nat} (before : Stack q → List Bool)
    (rows cap unaryM : List Bool)
    (hblank : ∀ k : SourceCSPRowQueryFrame.Stack q ⊕ Fin 5,
      before (.inr k) = []) :
    (fun k => prepared before rows cap unaryM (rowEmbedding k)) =
      ready rows cap unaryM := by
  funext k
  cases k with
  | inl r =>
      cases r with
      | inl jk =>
          simp [prepared, rowEmbedding, ready,
            SourceCSPRowQueryFrame.initial, rowSource, rowCap,
            loopCap, loopCount, capSource, hblank]
      | inr i =>
          fin_cases i <;>
            simp [prepared, rowEmbedding, ready,
              SourceCSPRowQueryFrame.initial, rowSource, rowCap,
              loopCap, loopCount, capSource, hblank]
  | inr i =>
      fin_cases i <;>
        simp [prepared, rowEmbedding, ready, rowSource, rowCap,
          loopCap, loopCount, capSource, hblank]

abbrev HeaderLabel (a q : Nat) := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label
    (SourceCSPConstraintGuard.HeaderLabel a q) SourceCSPQueryRange.Label)
  (BitMachineRawSequence.Label
    (BitMachineRawSequence.Label Unit (SourceFixedUnaryBudget.Label q))
    SourceCSPVertexCap.Label)

abbrev HeaderControl :=
  (SourceCSPConstraintGuard.HeaderControl × SourceCSPQueryRange.Control) ×
    ((Option Bool × Option Bool) × SourceCSPVertexCap.Control)

def headerProgram (a q : Nat) (l : HeaderLabel a q) :
    TM2.Stmt (fun _ : Stack q => Bool) (HeaderLabel a q) HeaderControl :=
  stmt headerEmbedding id id id none
    (SourceCSPPositiveHeader.fullHeaderProgram a q l)

def headerStart : HeaderControl :=
  (((((none, none), (((none, none), none), none)),
    ((none, none), (none, false)))),
    ((none, none), (((none, none), (none, false)), none)))

def prepareStart : Control5 := ((((none, none), none), none), none)

def fullProgram (a q : Nat) :=
  BitMachineRawSequence.program (headerProgram a q) prepareProgram
    (.inl (.inl (.inl (.inl .scan))) : Label5)
    headerStart prepareStart

def headerFinal (v : SourceCSPVertexCap.Control) : HeaderControl :=
  ((((none, none), (((none, none), none), none)),
    ((none, none), (none, false))), ((none, none), v))

theorem encoded_header_framed {a q : Nat}
    (P : EncodedETHSource.ConstraintInstance a q)
    (hn : 0 < P.vertices) (hsize : SourceCSPCodec.ValidSize P) :
    ∃ t v S,
      t ≤ SourceCSPPositiveHeader.positiveBound a q
        (EncodedETHSource.constraintBits P).length
        P.constraints.bits.length P.vertices P.constraints ∧
      ((advance (headerProgram a q))^[t])
        (⟨some (.inl (.inl (.inl (.inl BitMachineCopy.Label.scan)))),
          headerStart, initial (EncodedETHSource.constraintBits P)⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) (HeaderLabel a q) HeaderControl) =
        ⟨none, headerFinal v, S⟩ ∧
      S source = SourceCSPPositiveHeader.rows P ∧
      S count = List.replicate P.constraints true ∧
      S capSource = true :: List.replicate (P.vertices - 1) true ∧
      (∀ k : SourceCSPRowQueryFrame.Stack q ⊕ Fin 5,
        S (.inr k) = []) := by
  let input := EncodedETHSource.constraintBits P
  obtain ⟨th, vh, Sh, hth, hrh, hcap, hm, hrows⟩ :=
    SourceCSPPositiveSuffix.encoded_positive_row_suffix P hn hsize
  let localCfg : TM2.Cfg (fun _ : SourceCSPPositiveHeader.Stack => Bool)
      (HeaderLabel a q) HeaderControl :=
    ⟨some (.inl (.inl (.inl (.inl BitMachineCopy.Label.scan)))),
      headerStart, SourceCSPPositiveHeader.initial input⟩
  have hhalt : (((advance (SourceCSPPositiveHeader.fullHeaderProgram a q))^[th])
      localCfg).l = none := by
    rw [show ((advance (SourceCSPPositiveHeader.fullHeaderProgram a q))^[th])
      localCfg = ⟨none, headerFinal vh, Sh⟩ from by
      simpa only [input, localCfg, headerStart, headerFinal] using hrh]
  obtain ⟨t, ht, hr⟩ := outputs headerEmbedding (initial input)
    id id id (fun _ => rfl) none
    (SourceCSPPositiveHeader.fullHeaderProgram a q) (headerProgram a q)
    (fun _ => rfl) localCfg th hhalt
  have hstart : cfg headerEmbedding (initial input) id id none localCfg =
      (⟨some (.inl (.inl (.inl (.inl BitMachineCopy.Label.scan)))),
        headerStart, initial input⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (HeaderLabel a q) HeaderControl) := by
    simp only [cfg, stackCfg, BitMachineInline.cfg, localCfg, id_eq]
    congr 1
    apply bank_eq_self
    intro k
    rfl
  have hlocal : ((advance (SourceCSPPositiveHeader.fullHeaderProgram a q))^[th])
      localCfg = ⟨none, headerFinal vh, Sh⟩ := by
    simpa only [input, localCfg, headerStart, headerFinal] using hrh
  rw [hstart, hlocal] at hr
  let S : Stack q → List Bool :=
    bank (headerEmbedding (q := q)) (initial (q := q) input) Sh
  refine ⟨t, vh, S, ht.trans hth, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [headerProgram, S, cfg, stackCfg, BitMachineInline.cfg,
      headerFinal, id_eq, Option.map_none] using hr
  · change bank headerEmbedding _ _ (headerEmbedding SourceCSPPositiveSuffix.rowSlot) = _
    rw [bank_at]
    exact hrows
  · change bank headerEmbedding _ _ (headerEmbedding (.inl (.inr 6))) = _
    rw [bank_at]
    exact hm
  · change bank headerEmbedding _ _ (headerEmbedding (.inr 6)) = _
    rw [bank_at]
    exact hcap
  · intro k
    change bank headerEmbedding (initial input) Sh (.inr k) = []
    rw [bank_outside]
    · rfl
    · rintro ⟨j, hj⟩
      cases hj

/-- The encoded positive-header program physically prepares the exact row-loop
entry bank. The row stream and both unary counters are copied/peeled by the
finite `prepareProgram`, and its transition cost is included. -/
theorem encoded_row_ready {a q : Nat}
    (P : EncodedETHSource.ConstraintInstance a q)
    (hn : 0 < P.vertices) (hsize : SourceCSPCodec.ValidSize P) :
    ∃ t S,
      t ≤ SourceCSPPositiveHeader.positiveBound a q
        (EncodedETHSource.constraintBits P).length
        P.constraints.bits.length P.vertices P.constraints +
        2 * (SourceCSPPositiveHeader.rows P).length +
        4 * (P.vertices - 1) + 2 * P.constraints + 14 ∧
      ((advance (fullProgram a q))^[t])
        (⟨some (.inl (.inl (.inl (.inl (.inl BitMachineCopy.Label.scan))))),
          (headerStart, prepareStart),
          initial (EncodedETHSource.constraintBits P)⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            (BitMachineRawSequence.Label (HeaderLabel a q) Label5)
            (HeaderControl × Control5)) =
        ⟨none, (headerStart, prepareStart), S⟩ ∧
      (fun k => S (rowEmbedding k)) =
        ready (SourceCSPPositiveHeader.rows P)
          (List.replicate (P.vertices - 1) true)
          (List.replicate P.constraints true) := by
  let input := EncodedETHSource.constraintBits P
  let rows := SourceCSPPositiveHeader.rows P
  let cap := List.replicate (P.vertices - 1) true
  let unaryM := List.replicate P.constraints true
  obtain ⟨th, vh, Sh, hth, hrh, hrows, hm, hcap, hblank⟩ :=
    encoded_header_framed P hn hsize
  obtain ⟨tp, htp, hrp⟩ :=
    prepare_run Sh rows cap unaryM hrows hcap hm hblank
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (headerProgram a q) prepareProgram
    (.inl (.inl (.inl (.inl BitMachineCopy.Label.scan))) : HeaderLabel a q)
    (.inl (.inl (.inl (.inl BitMachineCopy.Label.scan))) : Label5)
    headerStart (headerFinal vh) prepareStart prepareStart
    (initial input) Sh (prepared Sh rows cap unaryM)
    th tp hrh (by simpa only [start, prepareStart] using hrp)
  refine ⟨t, prepared Sh rows cap unaryM, ?_, ?_, ?_⟩
  · simp only [cap, unaryM, List.length_replicate] at htp
    have hth' : th ≤ SourceCSPPositiveHeader.positiveBound a q input.length
        P.constraints.bits.length P.vertices P.constraints := by
      simpa only [input] using hth
    change t ≤ SourceCSPPositiveHeader.positiveBound a q input.length
      P.constraints.bits.length P.vertices P.constraints +
      2 * rows.length + 4 * (P.vertices - 1) + 2 * P.constraints + 14
    omega
  · simpa only [fullProgram, input, rows, cap, unaryM,
      headerStart, prepareStart] using hr
  · exact prepared_ready Sh rows cap unaryM hblank

end EthInapproximability.CurrentPaper.SourceCSPHeaderRowBridge
