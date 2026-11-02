import Paper2.YaoCtrlBlock

/-! Unit 5 segment Y5, staging + core (lane a-yao-owner-2): the controller's
exact start bank is staged from charged unary cells, then the core block runs.

Consumer: the one-entry callback Y5.  The start bank
`tapeRawBank S₀ bits.val`, `S₀ = Sum.elim (selectorInitial t lambda e z g l p).stk (fun _ => [])`,
is identified cell by cell (`start_bank_eq`): it is the tape in `tapeSource`, unary `e`
in the scalar machine input and unary `z, g, l, p` in the four frame label cells, and
`[]` everywhere else.  The staging program is five charged copies from source cells
(`σ (inr 2..6)`) into those five region cells.  With the core block, one fixed program
per `(t, lambda)` takes a bank whose region is cleaned (tape only) to the SAME bank
with the entry bit in the answer cell: `physical_entry_core`. -/

noncomputable section

namespace Paper2.YaoCtrlBlock

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.YaoLowerBound
open Paper2.YaoLowerBound.Materialization
open Paper2.YaoLookup
open Paper2.YaoEntryParameterJoin
open Paper2.YaoParameterBank
open Paper2.YaoEntryControllerJoin
open Paper2.YaoUniformClock

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384
set_option linter.unusedSimpArgs false

variable {J : Type*} [DecidableEq J]

/-- A frame cell of the controller region. -/
def frameCell {t lambda : ℕ} (f : FrameStack t lambda) : InputStack t lambda :=
  .inl (.inl (.inl (.inl (.inl (.inl f)))))

/-- The five staged cells: `e` (scalar machine input), `z`, `g`, `l`, `p` (labels). -/
def stageCell {t lambda : ℕ} : Fin 5 → InputStack t lambda :=
  ![frameCell (.inl (.inl ScalarA.input)), frameCell (.inr 0), frameCell (.inr 1),
    frameCell (.inr 2), frameCell (.inr 3)]

/-- The staged region. -/
def stagedRegion {t lambda : ℕ} (tape : List Bool) (e z g l p : ℕ) :
    InputStack t lambda → List Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (tapeOnly tape) (stageCell 0) (List.replicate e true)) (stageCell 1) (List.replicate z true))
    (stageCell 2) (List.replicate g true)) (stageCell 3) (List.replicate l true))
    (stageCell 4) (List.replicate p true)

/-- Cell-by-cell identification of the controller's start bank. -/
theorem start_bank_eq (t lambda e z g l p : ℕ) (tape : List Bool) :
    tapeRawBank (Sum.elim (selectorInitial t lambda e z g l p).stk (fun _ => [])) tape =
      stagedRegion tape e z g l p := by
  funext k
  rcases k with ((((((((b | i) | j) | m) | n) | o) | q) | r) | u)
  · simp only [tapeRawBank, stagedRegion, stageCell, frameCell, tapeOnly, selectorInitial,
      widthInitial, frameStart, BitMachineComposition.liftCfg, rawInit, Sum.elim_inl,
      Function.update_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Sum.inl.injEq, reduceCtorEq, if_false,
      tapeSource]
    split_ifs <;> simp_all
  · simp [tapeRawBank, stagedRegion, stageCell, frameCell, tapeOnly,
      selectorInitial, widthInitial, frameStart, BitMachineComposition.liftCfg, rawInit,
      Function.update_apply, tapeSource]
  · fin_cases j <;> simp [tapeRawBank, stagedRegion, stageCell, frameCell, tapeOnly,
      selectorInitial, widthInitial, frameStart, BitMachineComposition.liftCfg, labelBanks,
      Function.update_apply, tapeSource]
  all_goals (simp [tapeRawBank, stagedRegion, stageCell, frameCell, tapeOnly, selectorInitial,
      widthInitial, Function.update_apply, tapeSource, routedForeign]; try (split <;> rfl))

#print axioms start_bank_eq

/-! ## The staging copies and the entry core -/

/-- Source cells of the staging copies. -/
def stageSrc : Fin 5 → Fin 7 := ![2, 3, 4, 5, 6]

/-- Copy source `σ (inr (k+2))` into region cell `stageCell k`, scratch `σ (inr 1)`. -/
def stageCopy {t lambda : ℕ} (k : Fin 5) : Fin 3 ↪ InputStack t lambda ⊕ Fin 7 :=
  ⟨![.inr (stageSrc k), .inl (stageCell k), .inr 1], by
    have hk : stageSrc k ≠ 1 := by fin_cases k <;> decide
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩

def coreRegion : Fin 2 ↪ Fin 7 := ⟨![0, 1], by decide⟩

/-- The block placement inside the core placement. -/
def blockPlace {t lambda : ℕ} (σ : InputStack t lambda ⊕ Fin 7 ↪ J) :
    InputStack t lambda ⊕ Fin 2 ↪ J :=
  (Function.Embedding.sumMap (Function.Embedding.refl _) coreRegion).trans σ

def cp {t lambda : ℕ} (σ : InputStack t lambda ⊕ Fin 7 ↪ J) (k : Fin 5) :=
  ExactParameterBranchInstall.copyProgram ((stageCopy k).trans σ)

def stg45 {t lambda : ℕ} (σ : InputStack t lambda ⊕ Fin 7 ↪ J) :=
  BitMachineRawSequence.program (cp σ 3) (cp σ 4) BitMachineCopy.Label.scan none none
def stg345 {t lambda : ℕ} (σ : InputStack t lambda ⊕ Fin 7 ↪ J) :=
  BitMachineRawSequence.program (cp σ 2) (stg45 σ)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) none (none, none)
def stg2345 {t lambda : ℕ} (σ : InputStack t lambda ⊕ Fin 7 ↪ J) :=
  BitMachineRawSequence.program (cp σ 1) (stg345 σ)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) none (none, (none, none))
/-- The staging program: five charged copies. -/
def stage {t lambda : ℕ} (σ : InputStack t lambda ⊕ Fin 7 ↪ J) :=
  BitMachineRawSequence.program (cp σ 0) (stg2345 σ)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) none (none, (none, (none, none)))

def stageControl : Option Bool × (Option Bool × (Option Bool × (Option Bool × Option Bool))) :=
  (none, (none, (none, (none, none))))

/-- The fixed entry-core program: staging, then the core block. -/
def entryCore {t lambda : ℕ} (σ : InputStack t lambda ⊕ Fin 7 ↪ J) :=
  BitMachineRawSequence.program (stage σ) (block (blockPlace σ))
    (BitMachineRawSequence.leftLabel (.inl (.inl .scan))) stageControl (blockControl t lambda)

/-- Uniform bound on every start-bank cell. -/
def startMax (t lambda e : ℕ) : ℕ :=
  tapeBitCount t (paddedEdgeBits e) lambda + e + selectorCount t (paddedEdgeBits e) lambda +
    2 ^ (t - 1) + payloadCount t (paddedEdgeBits e) lambda + (2 ^ t * 2 ^ t + 1)

def coreClock (t lambda e : ℕ) : ℕ :=
  (2 * startMax t lambda e + 2) * 5 + 4 + blockClock t lambda e (startMax t lambda e) + 1

theorem start_cell_le {v e : ℕ} (t lambda : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (bits : SerializedTape t (paddedEdgeBits e) lambda)
    (vertex : Fin v)
    (z : Fin (selectorCount t (paddedEdgeBits e) lambda))
    (g : Fin (2 ^ (t - 1))) (a : Fin (paddedEdgeCount e))
    (l : Fin (payloadCount t (paddedEdgeBits e) lambda)) (k : InputStack t lambda) :
    (stagedRegion (t := t) (lambda := lambda) bits.val e z.val g.val l.val
      (positionEval (paddedEdgesEval edges) a vertex).val k).length ≤ startMax t lambda e := by
  have hz := z.isLt
  have hg := g.isLt
  have hl := l.isLt
  have hp := (positionEval (paddedEdgesEval edges) a vertex).isLt
  have hb : bits.val.length = tapeBitCount t (paddedEdgeBits e) lambda := bits.property
  unfold stagedRegion tapeOnly startMax
  simp only [Function.update_apply]
  split_ifs <;> simp <;> omega

/-- Y5 entry core: from a bank whose controller region is cleaned (raw tape
only) and whose five source cells hold unary `e, z, g, l, p`, one physical run of
the fixed program writes the entry bit into the answer cell and changes nothing
else. -/
theorem physical_entry_core {v e : ℕ} (t lambda : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (bits : SerializedTape t (paddedEdgeBits e) lambda)
    (vertex : Fin v)
    (z : Fin (selectorCount t (paddedEdgeBits e) lambda))
    (g : Fin (2 ^ (t - 1))) (a : Fin (paddedEdgeCount e))
    (l : Fin (payloadCount t (paddedEdgeBits e) lambda))
    (σ : InputStack t lambda ⊕ Fin 7 ↪ J) (B : J → List Bool)
    (hreg : ∀ k, B (σ (.inl k)) = tapeOnly bits.val k)
    (hans : B (σ (.inr 0)) = []) (hscr : B (σ (.inr 1)) = [])
    (he : B (σ (.inr 2)) = List.replicate e true)
    (hz : B (σ (.inr 3)) = List.replicate z.val true)
    (hg : B (σ (.inr 4)) = List.replicate g.val true)
    (hl : B (σ (.inr 5)) = List.replicate l.val true)
    (hp : B (σ (.inr 6)) = List.replicate (positionEval (paddedEdgesEval edges) a vertex).val true) :
    ∃ total ≤ coreClock t lambda e, ∃ c',
      ((advance (entryCore σ))^[total])
        (⟨some (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
            BitMachineCopy.Label.scan)), (stageControl, blockControl t lambda), B⟩ :
          TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, c', Function.update B (σ (.inr 0))
          [matrixFromTape t lambda edges (readTape t (paddedEdgeBits e) lambda bits)
            (vertex, z) (g, a, l)]⟩ := by
  classical
  have hinj := σ.injective
  set p := (positionEval (paddedEdgesEval edges) a vertex).val with hpv
  have hsc : ∀ k : Fin 5, B (σ (.inl (stageCell k))) = [] := by
    intro k
    rw [hreg]
    fin_cases k <;> simp [tapeOnly, stageCell, frameCell, tapeSource]
  have hm := start_cell_le t lambda edges bits vertex z g a l
  -- five copies
  obtain ⟨t1, ht1, hr1⟩ := ExactParameterBranchInstall.copy_run ((stageCopy 0).trans σ) B
    (List.replicate e true) (by simp [stageCopy, stageSrc, he]) (by simpa [stageCopy, stageSrc] using hsc 0)
    (by simp [stageCopy, stageSrc, hscr])
  set B1 := Function.update B (σ (.inl (stageCell 0))) (List.replicate e true) with hB1
  obtain ⟨t2, ht2, hr2⟩ := ExactParameterBranchInstall.copy_run ((stageCopy 1).trans σ) B1
    (List.replicate z.val true) (by simp [hB1, stageCopy, stageSrc, hinj.eq_iff, hz])
    (by simp [hB1, stageCopy, stageSrc, hinj.eq_iff, stageCell, frameCell]; simpa [stageCell, frameCell] using hsc 1)
    (by simp [hB1, stageCopy, stageSrc, hinj.eq_iff, hscr])
  set B2 := Function.update B1 (σ (.inl (stageCell 1))) (List.replicate z.val true) with hB2
  obtain ⟨t3, ht3, hr3⟩ := ExactParameterBranchInstall.copy_run ((stageCopy 2).trans σ) B2
    (List.replicate g.val true) (by simp [hB2, hB1, stageCopy, stageSrc, hinj.eq_iff, hg])
    (by simp [hB2, hB1, stageCopy, stageSrc, hinj.eq_iff, stageCell, frameCell]
        simpa [stageCell, frameCell] using hsc 2)
    (by simp [hB2, hB1, stageCopy, stageSrc, hinj.eq_iff, hscr])
  set B3 := Function.update B2 (σ (.inl (stageCell 2))) (List.replicate g.val true) with hB3
  obtain ⟨t4, ht4, hr4⟩ := ExactParameterBranchInstall.copy_run ((stageCopy 3).trans σ) B3
    (List.replicate l.val true) (by simp [hB3, hB2, hB1, stageCopy, stageSrc, hinj.eq_iff, hl])
    (by simp [hB3, hB2, hB1, stageCopy, stageSrc, hinj.eq_iff, stageCell, frameCell]
        simpa [stageCell, frameCell] using hsc 3)
    (by simp [hB3, hB2, hB1, stageCopy, stageSrc, hinj.eq_iff, hscr])
  set B4 := Function.update B3 (σ (.inl (stageCell 3))) (List.replicate l.val true) with hB4
  obtain ⟨t5, ht5, hr5⟩ := ExactParameterBranchInstall.copy_run ((stageCopy 4).trans σ) B4
    (List.replicate p true) (by simp [hB4, hB3, hB2, hB1, stageCopy, stageSrc, hinj.eq_iff, hp])
    (by simp [hB4, hB3, hB2, hB1, stageCopy, stageSrc, hinj.eq_iff, stageCell, frameCell]
        simpa [stageCell, frameCell] using hsc 4)
    (by simp [hB4, hB3, hB2, hB1, stageCopy, stageSrc, hinj.eq_iff, hscr])
  set B5 := Function.update B4 (σ (.inl (stageCell 4))) (List.replicate p true) with hB5
  have hB5reg : ∀ k, B5 (blockPlace σ (.inl k)) = tapeRawBank
      (Sum.elim (selectorInitial t lambda e z.val g.val l.val p).stk (fun _ => [])) bits.val k := by
    intro k
    rw [start_bank_eq]
    change B5 (σ (.inl k)) = _
    simp only [hB5, hB4, hB3, hB2, hB1, stagedRegion, Function.update_apply, hinj.eq_iff,
      Sum.inl.injEq, hreg]
  have hB5out : ∀ i : Fin 7, B5 (σ (.inr i)) = B (σ (.inr i)) := by
    intro i
    simp [hB5, hB4, hB3, hB2, hB1, hinj.eq_iff]
  -- the core block
  obtain ⟨t6, ht6, c6, hr6⟩ := physical_block t lambda edges bits vertex z g a l (blockPlace σ)
    B5 (startMax t lambda e) hB5reg
    (by intro k; rw [start_bank_eq]; exact hm k)
    (by change B5 (σ (.inr 0)) = []; rw [hB5out, hans])
    (by change B5 (σ (.inr 1)) = []; rw [hB5out, hscr])
  have hfin : Function.update (BitMachineStackEmbedding.bank (region (blockPlace σ)) B5
      (tapeOnly bits.val)) (blockPlace σ (.inr 0))
      [matrixFromTape t lambda edges (readTape t (paddedEdgeBits e) lambda bits)
        (vertex, z) (g, a, l)] =
      Function.update B (σ (.inr 0))
      [matrixFromTape t lambda edges (readTape t (paddedEdgeBits e) lambda bits)
        (vertex, z) (g, a, l)] := by
    have hbk : BitMachineStackEmbedding.bank (region (blockPlace σ)) B5 (tapeOnly bits.val) = B := by
      funext j
      by_cases hj : ∃ k, σ (.inl k) = j
      · obtain ⟨k, rfl⟩ := hj
        have := BitMachineStackEmbedding.bank_at (region (blockPlace σ)) B5
          (tapeOnly (t := t) (lambda := lambda) bits.val) k
        exact this.trans (hreg k).symm
      · rw [BitMachineStackEmbedding.bank_outside (region (blockPlace σ)) B5 _ j
          (by rintro ⟨k, hk⟩; exact hj ⟨k, hk⟩)]
        have h5 : ∀ i : Fin 5, j ≠ σ (.inl (stageCell i)) := fun i h => hj ⟨_, h.symm⟩
        simp only [hB5, hB4, hB3, hB2, hB1]
        rw [Function.update_of_ne (h5 4), Function.update_of_ne (h5 3),
          Function.update_of_ne (h5 2), Function.update_of_ne (h5 1),
          Function.update_of_ne (h5 0)]
    rw [hbk]
    rfl
  rw [hfin] at hr6
  -- sequencing
  obtain ⟨u4, hu4, hrun4⟩ := BitMachineRawSequence.runs (cp σ 3) (cp σ 4)
    BitMachineCopy.Label.scan BitMachineCopy.Label.scan none none none none B3 B4 B5 t4 t5 hr4 hr5
  obtain ⟨u3, hu3, hrun3⟩ := BitMachineRawSequence.runs (cp σ 2) (stg45 σ)
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none none (none, none) (none, none) B2 B3 B5 t3 u4 hr3 hrun4
  obtain ⟨u2, hu2, hrun2⟩ := BitMachineRawSequence.runs (cp σ 1) (stg345 σ)
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none none (none, (none, none)) (none, (none, none)) B1 B2 B5 t2 u3 hr2 hrun3
  obtain ⟨u1, hu1, hrun1⟩ := BitMachineRawSequence.runs (cp σ 0) (stg2345 σ)
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none none (none, (none, (none, none))) (none, (none, (none, none))) B B1 B5 t1 u2 hr1 hrun2
  obtain ⟨u, hu, hrun⟩ := BitMachineRawSequence.runs (stage σ) (block (blockPlace σ))
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (BitMachineRawSequence.leftLabel (.inl (.inl .scan))) stageControl stageControl
    (blockControl t lambda) c6 B B5 _ u1 t6 hrun1 hr6
  refine ⟨u, ?_, _, hrun⟩
  have hz' := z.isLt
  have hg' := g.isLt
  have hl' := l.isLt
  have hp' := (positionEval (paddedEdgesEval edges) a vertex).isLt
  simp only [List.length_replicate] at ht1 ht2 ht3 ht4 ht5
  unfold coreClock startMax at *
  omega

#print axioms start_cell_le
#print axioms physical_entry_core

end Paper2.YaoCtrlBlock

end
