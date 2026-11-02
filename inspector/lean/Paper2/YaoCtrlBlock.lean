import Paper2.YaoCtrlGrowth
import Paper2.YaoPrelPay
import Paper2.ClearAll

/-! Unit 5 segment Y5, core block (lane a-yao-owner-2): the ported entry
controller placed in an ambient bank, followed by the answer move and the
MANDATORY cleanup with the production `ClearAll`.

Consumer: the one-entry callback Y5 (`MatrixTableWriter.EntryRuns` needs the
foreign bank restored exactly).  One fixed program per `(t, lambda)`, placed by
`κ : InputStack t lambda ⊕ Fin 2 ↪ J`: the `inl` region carries the controller's
own stacks, `κ (inr 0)` is the answer cell (writer answer cell in Y5), `κ (inr 1)`
a copy scratch.  Three stages, two charged handoffs:
the frozen private controller `fullEntryProgram` (a-yao-owner-1 `Y0FullEntryController`,
under root admission) embedded by `BitMachineStackEmbedding.outputs`; a charged copy of
the answer cell `entryEmbed t lambda 12` to `κ (inr 0)`; `ClearAll.all_run` over every
region cell except the raw tape `tapeSource`, with `Lmax` from `controller_exit_length_le`
(a-yao-owner-1 `YaoCtrlGrowth`) and `controller_bound_le_uniform` (`YaoUniformClock`).

Entry premise: the region holds the controller's exact start bank
`tapeRawBank S₀ bits.val` (staging from charged unary cells is NOT part of this
block); every start cell has length at most `L0` (a parameter, supplied by the
staging step).  Exit bank exact: the region is empty except the raw tape cell,
which holds `bits.val` again; the answer cell holds the one-bit word
`[matrixFromTape …]`; every other cell is unchanged. -/

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

noncomputable instance inputStackFintype (t lambda : ℕ) : Fintype (InputStack t lambda) := by
  unfold InputStack
  infer_instance

/-- The region embedding. -/
def region {t lambda : ℕ} (κ : InputStack t lambda ⊕ Fin 2 ↪ J) : InputStack t lambda ↪ J :=
  Function.Embedding.inl.trans κ

/-- The embedded controller. -/
def ctrlEmb {t lambda : ℕ} (κ : InputStack t lambda ⊕ Fin 2 ↪ J) (l : FullLabel t lambda) :
    TM2.Stmt (fun _ : J => Bool) (FullLabel t lambda) (FullControl t lambda) :=
  BitMachineStackEmbedding.stmt (region κ) id id id none (fullEntryProgram t lambda l)

/-- The answer copy: source `entryEmbed 12`, target `κ (inr 0)`, scratch `κ (inr 1)`. -/
def ansCopy {t lambda : ℕ} : Fin 3 ↪ InputStack t lambda ⊕ Fin 2 :=
  ⟨![.inl (entryEmbed t lambda 12), .inr 0, .inr 1], by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩

/-- The region cells other than the raw tape, in the admitted `Fintype` order. -/
abbrev Clearable (t lambda : ℕ) := {k : InputStack t lambda // k ≠ tapeSource t lambda}

def clearCells {t lambda : ℕ} (κ : InputStack t lambda ⊕ Fin 2 ↪ J) :
    Fin (Fintype.card (Clearable t lambda)) → J :=
  fun i => region κ ((Fintype.equivFin (Clearable t lambda)).symm i).val

omit [DecidableEq J] in
theorem clearCells_injective {t lambda : ℕ} (κ : InputStack t lambda ⊕ Fin 2 ↪ J) :
    Function.Injective (clearCells κ) := by
  intro i j h
  apply (Fintype.equivFin (Clearable t lambda)).symm.injective
  exact Subtype.ext ((region κ).injective h)

def blockTail {t lambda : ℕ} (κ : InputStack t lambda ⊕ Fin 2 ↪ J) :=
  BitMachineRawSequence.program (ExactParameterBranchInstall.copyProgram (ansCopy.trans κ))
    (Paper2.ClearAll.prog (clearCells κ))
    (⟨0, by omega⟩ : Fin (Fintype.card (Clearable t lambda) + 1)) none none

/-- The fixed controller block program. -/
def block {t lambda : ℕ} (κ : InputStack t lambda ⊕ Fin 2 ↪ J) :=
  BitMachineRawSequence.program (ctrlEmb κ) (blockTail κ)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    ((none, (loaderInitialControl t lambda, ())), Paper2.YaoEntryComposition.initialControl)
    (none, none)

def blockControl (t lambda : ℕ) : FullControl t lambda × (Option Bool × Option Bool) :=
  (((none, (loaderInitialControl t lambda, ())), Paper2.YaoEntryComposition.initialControl),
    ((none : Option Bool), (none : Option Bool)))

/-- The region after cleanup: the raw tape only. -/
def tapeOnly {t lambda : ℕ} (tape : List Bool) : InputStack t lambda → List Bool :=
  fun k => if k = tapeSource t lambda then tape else []

def blockClock (t lambda e L0 : ℕ) : ℕ :=
  controllerUniform t lambda e + (2 * 1 + 2) +
    (Fintype.card (Clearable t lambda) *
      (L0 + BitMachineStackGrowth.perStep (fullEntryProgram t lambda) *
        controllerUniform t lambda e + 1) + 1) + 2

/-- Y5 core block: one physical run from the controller's exact start bank (in
the region) to the exact cleaned bank with the entry bit in the answer cell. -/
theorem physical_block {v e : ℕ} (t lambda : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (bits : SerializedTape t (paddedEdgeBits e) lambda)
    (vertex : Fin v)
    (z : Fin (selectorCount t (paddedEdgeBits e) lambda))
    (g : Fin (2 ^ (t - 1))) (a : Fin (paddedEdgeCount e))
    (l : Fin (payloadCount t (paddedEdgeBits e) lambda))
    (κ : InputStack t lambda ⊕ Fin 2 ↪ J) (B : J → List Bool) (L0 : ℕ)
    (hreg : ∀ k, B (κ (.inl k)) = tapeRawBank
      (Sum.elim (selectorInitial t lambda e z.val g.val l.val
        (positionEval (paddedEdgesEval edges) a vertex).val).stk (fun _ => []))
      bits.val k)
    (hL0 : ∀ k, (tapeRawBank
      (Sum.elim (selectorInitial t lambda e z.val g.val l.val
        (positionEval (paddedEdgesEval edges) a vertex).val).stk (fun _ => []))
      bits.val k).length ≤ L0)
    (hans : B (κ (.inr 0)) = []) (hscr : B (κ (.inr 1)) = []) :
    ∃ total ≤ blockClock t lambda e L0, ∃ c',
      ((advance (block κ))^[total])
        (⟨some (BitMachineRawSequence.leftLabel (.inl (.inl .scan))),
          blockControl t lambda, B⟩ : TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, c', Function.update
          (BitMachineStackEmbedding.bank (region κ) B (tapeOnly bits.val)) (κ (.inr 0))
          [matrixFromTape t lambda edges (readTape t (paddedEdgeBits e) lambda bits)
            (vertex, z) (g, a, l)]⟩ := by
  classical
  have hinj := κ.injective
  set S₀ : PayloadStack t lambda → List Bool :=
    Sum.elim (selectorInitial t lambda e z.val g.val l.val
      (positionEval (paddedEdgesEval edges) a vertex).val).stk (fun _ => []) with hS₀
  set ans := matrixFromTape t lambda edges (readTape t (paddedEdgeBits e) lambda bits)
    (vertex, z) (g, a, l) with hansv
  obtain ⟨_, _, _, _, _, _, total, S, _, _, _, _, _, _, _, hT, hrest⟩ :=
    physical_full_entry_controller t lambda edges bits vertex z g a l
  dsimp only at hrest
  obtain ⟨hrun, hbit, htape⟩ := hrest
  have hTu : total ≤ controllerUniform t lambda e :=
    hT.trans (Paper2.YaoUniformClock.controller_bound_le_uniform t lambda edges bits vertex z g a l)
  set c0 : TM2.Cfg (fun _ : InputStack t lambda => Bool) (FullLabel t lambda)
      (FullControl t lambda) :=
    ⟨some (.inl (.inl .scan)),
      ((none, (loaderInitialControl t lambda, ())), Paper2.YaoEntryComposition.initialControl),
      tapeRawBank S₀ bits.val⟩ with hc0
  set F := entryEndBank t lambda
    (Sum.elim (routedFinal S bits.val) (fun _ => bits.val))
    (Paper2.YaoEntryComposition.entryFinal t lambda edges bits vertex z g a l).stk with hF
  -- stage 1: the embedded controller
  have hhalt : (((advance (fullEntryProgram t lambda))^[total]) c0).l = none := by
    rw [hc0, hrun]
  obtain ⟨n1, hn1, hr1⟩ := BitMachineStackEmbedding.outputs (region κ) B id id id
    (fun _ => rfl) none (fullEntryProgram t lambda) (ctrlEmb κ) (by intro l; rfl) c0 total hhalt
  have hbank : BitMachineStackEmbedding.bank (region κ) B c0.stk = B :=
    BitMachineStackEmbedding.bank_eq_self _ _ _ (fun k => (hreg k).symm)
  rw [hc0, hrun] at hr1
  have hr1' : ((advance (ctrlEmb κ))^[n1])
      (⟨some (.inl (.inl .scan)),
        ((none, (loaderInitialControl t lambda, ())), Paper2.YaoEntryComposition.initialControl),
        B⟩ : TM2.Cfg (fun _ : J => Bool) (FullLabel t lambda) (FullControl t lambda)) =
      ⟨none, ((none, (loaderInitialControl t lambda, ())),
        Paper2.YaoEntryComposition.initialControl),
        BitMachineStackEmbedding.bank (region κ) B F⟩ := by
    have h := hr1
    unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
      BitMachineInline.cfg at h
    simp only [id] at h
    have hbank' : BitMachineStackEmbedding.bank (region κ) B (tapeRawBank S₀ bits.val) = B := hbank
    rw [hbank'] at h
    exact h
  set B1 := BitMachineStackEmbedding.bank (region κ) B F with hB1
  have hB1reg : ∀ k, B1 (κ (.inl k)) = F k := fun k =>
    BitMachineStackEmbedding.bank_at (region κ) B F k
  have hB1out : ∀ i : Fin 2, B1 (κ (.inr i)) = B (κ (.inr i)) := by
    intro i
    apply BitMachineStackEmbedding.bank_outside
    rintro ⟨k, hk⟩
    exact Sum.inl_ne_inr (hinj hk)
  -- stage 2: copy the answer bit
  obtain ⟨n2, hn2, hr2⟩ := ExactParameterBranchInstall.copy_run (ansCopy.trans κ) B1 [ans]
    (by simp only [ansCopy, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk,
          Matrix.cons_val_zero]; rw [hB1reg]; exact hbit)
    (by simp only [ansCopy, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk,
          Matrix.cons_val_one, Matrix.cons_val_zero]; rw [hB1out, hans])
    (by simp only [ansCopy, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk]
        rw [show (![Sum.inl (entryEmbed t lambda 12), Sum.inr 0, Sum.inr 1] :
          Fin 3 → InputStack t lambda ⊕ Fin 2) 2 = Sum.inr 1 from rfl, hB1out, hscr])
  change _ = (⟨none, none, Function.update B1 (κ (.inr 0)) [ans]⟩ :
    TM2.Cfg (fun _ : J => Bool) BitMachineCopy.Label (Option Bool)) at hr2
  set B2 := Function.update B1 (κ (.inr 0)) [ans] with hB2
  -- stage 3: clear every region cell except the raw tape
  have hL : ∀ i, (B2 (clearCells κ i)).length ≤
      L0 + BitMachineStackGrowth.perStep (fullEntryProgram t lambda) *
        controllerUniform t lambda e := by
    intro i
    simp only [clearCells, region, Function.Embedding.trans_apply, Function.Embedding.inl_apply]
    rw [hB2, Function.update_of_ne (fun h => Sum.inl_ne_inr (hinj h)), hB1reg]
    have hx := Paper2.YaoCtrlGrowth.controller_exit_length_le t lambda c0 total
      (controllerUniform t lambda e) hTu _ F (by rw [hc0, hrun])
      ((Fintype.equivFin (Clearable t lambda)).symm i).val
    have h0 := hL0 ((Fintype.equivFin (Clearable t lambda)).symm i).val
    simp only [hc0] at hx
    omega
  obtain ⟨n3, hn3, v3, hr3⟩ := Paper2.ClearAll.all_run (clearCells κ) (clearCells_injective κ)
    _ B2 hL none
  have hfin : Paper2.ClearAll.clearFrom (clearCells κ) 0 B2 = Function.update
      (BitMachineStackEmbedding.bank (region κ) B (tapeOnly bits.val)) (κ (.inr 0)) [ans] := by
    funext j
    rw [Paper2.YaoPrelude.clearFrom_zero]
    by_cases hj : ∃ k, κ (.inl k) = j
    · obtain ⟨k, rfl⟩ := hj
      rw [Function.update_of_ne (fun h => Sum.inl_ne_inr (hinj h))]
      have hbk : BitMachineStackEmbedding.bank (region κ) B (tapeOnly bits.val) (κ (.inl k)) =
          tapeOnly bits.val k := BitMachineStackEmbedding.bank_at (region κ) B _ k
      rw [hbk]
      by_cases hk : k = tapeSource t lambda
      · subst hk
        rw [if_neg (by
          rintro ⟨i, hi⟩
          have := (hinj hi)
          exact ((Fintype.equivFin (Clearable t lambda)).symm i).property
            (Sum.inl_injective this))]
        rw [hB2, Function.update_of_ne (fun h => Sum.inl_ne_inr (hinj h)), hB1reg, hF]
        simp only [tapeOnly, if_true, eq_self_iff_true]
        exact htape
      · rw [if_pos ⟨(Fintype.equivFin (Clearable t lambda)) ⟨k, hk⟩, by
          simp [clearCells, region]⟩]
        simp [tapeOnly, hk]
    · rw [if_neg (by
        rintro ⟨i, hi⟩
        exact hj ⟨_, hi⟩)]
      have hout : BitMachineStackEmbedding.bank (region κ) B (tapeOnly bits.val) j = B j :=
        BitMachineStackEmbedding.bank_outside (region κ) B _ j
          (by rintro ⟨k, hk⟩; exact hj ⟨k, hk⟩)
      have hout1 : B1 j = B j := BitMachineStackEmbedding.bank_outside (region κ) B F j
          (by rintro ⟨k, hk⟩; exact hj ⟨k, hk⟩)
      rw [hB2]
      by_cases h0 : j = κ (.inr 0)
      · subst h0; simp
      · rw [Function.update_of_ne h0, Function.update_of_ne h0, hout1, hout]
  rw [hfin] at hr3
  -- sequencing with two charged handoffs
  obtain ⟨u2, hu2, hrun2⟩ := BitMachineRawSequence.runs
    (ExactParameterBranchInstall.copyProgram (ansCopy.trans κ))
    (Paper2.ClearAll.prog (clearCells κ)) BitMachineCopy.Label.scan
    (⟨0, by omega⟩ : Fin (Fintype.card (Clearable t lambda) + 1))
    none none none v3 B1 B2 _ n2 n3 hr2 hr3
  obtain ⟨u1, hu1, hrun1⟩ := BitMachineRawSequence.runs (ctrlEmb κ) (blockTail κ)
    (.inl (.inl .scan)) (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    ((none, (loaderInitialControl t lambda, ())), Paper2.YaoEntryComposition.initialControl)
    ((none, (loaderInitialControl t lambda, ())), Paper2.YaoEntryComposition.initialControl)
    (none, none) (none, v3) B B1 _ n1 u2 hr1' hrun2
  refine ⟨u1, ?_, _, hrun1⟩
  simp only [List.length_singleton] at hn2
  unfold blockClock
  omega

#print axioms physical_block

end Paper2.YaoCtrlBlock

end
