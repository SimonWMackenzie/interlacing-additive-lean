import Paper2.YaoCtrlStage

/-! Unit 5 segment Y5 (lane a-yao-owner-2): the one-entry callback.

Consumer: `MatrixTableWriter.EntryRuns` (Y7).  One fixed program `entryProgram Ω`
per `(t, lambda)`, placement `Ω : InputStack t lambda ⊕ Fin 23 ↪ J`.
Named cells `Ω (inr i)`: 0 writer row `x`, 1 writer column `y`, 2 answer,
3 `sel`, 4 `pay`, 5 `pow`, 6 `K = arity t`, 7 `e` (prelude outputs), 8 the body
stream `tokens (List.ofFn (flatten edges))` (Y2 work cell, R-Y2), 9..14 the
Y4/Y3 outputs `vertex, z, g, a, l, p`, 15..22 scratch; the `inl` region is the
controller's own bank, holding only the raw tape `bits.val` in `tapeSource`.

Four stages, three charged handoffs: Y4 `physical_index_decode` (frozen
a-yao-owner-1); Y3 `physical_position` (frozen a-yao-owner-1); the entry core
`physical_entry_core` (staging + controller + answer move + cleanup); the
production `ClearAll` over the six Y4/Y3 output cells.  Exit bank: the entry
bit `(materialize t lambda edges bits).matrix ⟨x,_⟩ ⟨y,_⟩` in the answer cell,
every other cell exactly as at entry. -/

noncomputable section

namespace Paper2.YaoOneEntry

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
open Paper2.YaoCtrlBlock
open Paper2.YaoMaterialization
open Paper2.UnaryFieldListParserScratch
open Paper2.YaoSourceCodec

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384
set_option linter.unusedSimpArgs false

variable {J : Type*} [DecidableEq J]

def f14 : Fin 14 ↪ Fin 23 := ⟨![0, 1, 3, 4, 5, 15, 16, 17, 9, 10, 11, 12, 13, 18], by decide⟩
def f13 : Fin 13 ↪ Fin 23 := ⟨![8, 12, 6, 9, 15, 16, 17, 18, 19, 14, 20, 21, 22], by decide⟩
def f7 : Fin 7 ↪ Fin 23 := ⟨![2, 15, 7, 10, 11, 13, 14], by decide⟩
def f6 : Fin 6 ↪ Fin 23 := ⟨![9, 10, 11, 12, 13, 14], by decide⟩

def y4Place {t lambda : ℕ} (Ω : InputStack t lambda ⊕ Fin 23 ↪ J) : Fin 14 ↪ J :=
  (f14.trans Function.Embedding.inr).trans Ω
def y3Place {t lambda : ℕ} (Ω : InputStack t lambda ⊕ Fin 23 ↪ J) : Fin 13 ↪ J :=
  (f13.trans Function.Embedding.inr).trans Ω
def corePlace {t lambda : ℕ} (Ω : InputStack t lambda ⊕ Fin 23 ↪ J) :
    InputStack t lambda ⊕ Fin 7 ↪ J :=
  (Function.Embedding.sumMap (Function.Embedding.refl _) f7).trans Ω
def outCells {t lambda : ℕ} (Ω : InputStack t lambda ⊕ Fin 23 ↪ J) : Fin 6 → J :=
  fun i => Ω (.inr (f6 i))

omit [DecidableEq J] in
theorem outCells_injective {t lambda : ℕ} (Ω : InputStack t lambda ⊕ Fin 23 ↪ J) :
    Function.Injective (outCells Ω) := by
  intro i j h
  exact f6.injective (Sum.inr_injective (Ω.injective h))

def rest2 {t lambda : ℕ} (Ω : InputStack t lambda ⊕ Fin 23 ↪ J) :=
  BitMachineRawSequence.program (entryCore (corePlace Ω)) (Paper2.ClearAll.prog (outCells Ω))
    (⟨0, by omega⟩ : Fin 7) (stageControl, blockControl t lambda) none
def rest1 {t lambda : ℕ} (Ω : InputStack t lambda ⊕ Fin 23 ↪ J) :=
  BitMachineRawSequence.program (Paper2.YaoPositionFull.program (y3Place Ω)) (rest2 Ω)
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))
    Paper2.YaoPositionFull.startControl ((stageControl, blockControl t lambda), none)
/-- The fixed one-entry program. -/
def entryProgram {t lambda : ℕ} (Ω : InputStack t lambda ⊕ Fin 23 ↪ J) :=
  BitMachineRawSequence.program (Paper2.YaoIndexDecoder.program (y4Place Ω)) (rest1 Ω)
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    Paper2.YaoIndexDecoder.startControl
    (Paper2.YaoPositionFull.startControl, ((stageControl, blockControl t lambda), none))

def entryControl (t lambda : ℕ) :=
  (Paper2.YaoIndexDecoder.startControl,
    (Paper2.YaoPositionFull.startControl, ((stageControl, blockControl t lambda),
      (none : Option Bool))))

/-- The entry clock, monotone in `x, y` (uniform after substituting bounds). -/
def entryClock (t lambda e L x y : ℕ) : ℕ :=
  ((2 * x + 2) + (8 * x + 3 * selectorCount t (paddedEdgeBits e) lambda + 4) + (2 * y + 2) +
    (8 * y + 3 * payloadCount t (paddedEdgeBits e) lambda + 4) +
    (8 * y + 3 * paddedEdgeCount e + 4) + 4) +
  ((2 * L + 2) + (2 * y + 2) + (2 * arity t + 2) + (y * (2 * arity t + 3) + 1 + (arity t + 1)) +
    (2 * arity t + 2) + (2 * (y * arity t) + 5 * L + arity t * (3 * x + 6) + arity t + 6) + 5) +
  coreClock t lambda e + (6 * (x + y + arity t + 1 + 1) + 1) + 3

theorem entryClock_mono (t lambda e L : ℕ) {x y x' y' : ℕ} (hx : x ≤ x') (hy : y ≤ y') :
    entryClock t lambda e L x y ≤ entryClock t lambda e L x' y' := by
  unfold entryClock
  have h1 := Nat.mul_le_mul_right (2 * arity t + 3) hy
  have h2 := Nat.mul_le_mul_right (arity t) hy
  have h3 := Nat.mul_le_mul_left (arity t) (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hx) 6)
  omega

/-- Value bridge: the materialized entry at `⟨x,hx⟩, ⟨y,hy⟩` through the decoded indices. -/
theorem entry_value {v e : ℕ} (t lambda : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (bits : SerializedTape t (paddedEdgeBits e) lambda)
    (X : Fin (rowCount v t (paddedEdgeBits e) lambda))
    (Y : Fin (columnCount t (paddedEdgeBits e) lambda)) :
    (materialize t lambda edges bits).matrix X Y =
      matrixFromTape t lambda edges (readTape t (paddedEdgeBits e) lambda bits)
        (((rowIndex v t (paddedEdgeBits e) lambda).symm X).1,
          ((rowIndex v t (paddedEdgeBits e) lambda).symm X).2)
        (((columnIndex t (paddedEdgeBits e) lambda).symm Y).1,
          ((columnIndex t (paddedEdgeBits e) lambda).symm Y).2.1,
          ((columnIndex t (paddedEdgeBits e) lambda).symm Y).2.2) := by
  rw [materialize_matrix]
  rfl

/-- Y5 main theorem: one physical run of the fixed one-entry program writes the
materialized entry into the answer cell and leaves every other cell unchanged. -/
theorem physical_one_entry {v e : ℕ} (t lambda : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (bits : SerializedTape t (paddedEdgeBits e) lambda)
    (Ω : InputStack t lambda ⊕ Fin 23 ↪ J) (B : J → List Bool) (x y : ℕ)
    (hxr : x < rowCount v t (paddedEdgeBits e) lambda)
    (hyc : y < columnCount t (paddedEdgeBits e) lambda)
    (hx : B (Ω (.inr 0)) = List.replicate x true) (hy : B (Ω (.inr 1)) = List.replicate y true)
    (hans : B (Ω (.inr 2)) = [])
    (hsel : B (Ω (.inr 3)) = List.replicate (selectorCount t (paddedEdgeBits e) lambda) true)
    (hpay : B (Ω (.inr 4)) = List.replicate (payloadCount t (paddedEdgeBits e) lambda) true)
    (hpow : B (Ω (.inr 5)) = List.replicate (paddedEdgeCount e) true)
    (hK : B (Ω (.inr 6)) = List.replicate (arity t) true)
    (he : B (Ω (.inr 7)) = List.replicate e true)
    (hbody : B (Ω (.inr 8)) = tokens (List.ofFn (flatten edges)))
    (hs : ∀ i : Fin 23, 9 ≤ i.val → B (Ω (.inr i)) = [])
    (hreg : ∀ k, B (Ω (.inl k)) = tapeOnly bits.val k) :
    ∃ total ≤ entryClock t lambda e (tokens (List.ofFn (flatten edges))).length x y, ∃ c',
      ((advance (entryProgram Ω))^[total])
        (⟨some (BitMachineRawSequence.leftLabel Paper2.YaoIndexDecoder.startLabel),
          entryControl t lambda, B⟩ : TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, c', Function.update B (Ω (.inr 2))
          [(materialize t lambda edges bits).matrix ⟨x, hxr⟩ ⟨y, hyc⟩]⟩ := by
  classical
  have hinj := Ω.injective
  set X : Fin (rowCount v t (paddedEdgeBits e) lambda) := ⟨x, hxr⟩ with hX
  set Y : Fin (columnCount t (paddedEdgeBits e) lambda) := ⟨y, hyc⟩ with hY
  set vtx := ((rowIndex v t (paddedEdgeBits e) lambda).symm X).1 with hvtx
  set z := ((rowIndex v t (paddedEdgeBits e) lambda).symm X).2 with hz
  set g := ((columnIndex t (paddedEdgeBits e) lambda).symm Y).1 with hg
  set a := ((columnIndex t (paddedEdgeBits e) lambda).symm Y).2.1 with ha
  set l := ((columnIndex t (paddedEdgeBits e) lambda).symm Y).2.2 with hl
  obtain ⟨hrv, hrz⟩ := Paper2.YaoIndexDecoder.row_decode v t (paddedEdgeBits e) lambda X
  obtain ⟨hcl, hca, hcg⟩ := Paper2.YaoIndexDecoder.column_decode t (paddedEdgeBits e) lambda Y
  have e8 : x / selectorCount t (paddedEdgeBits e) lambda = vtx.val := hrv
  have e9 : x % selectorCount t (paddedEdgeBits e) lambda = z.val := hrz
  have e10 : y / payloadCount t (paddedEdgeBits e) lambda / paddedEdgeCount e = g.val := hcg
  have e11 : y / payloadCount t (paddedEdgeBits e) lambda % paddedEdgeCount e = a.val := hca
  have e12 : y % payloadCount t (paddedEdgeBits e) lambda = l.val := hcl
  have hsi : ∀ i : Fin 23, 9 ≤ i.val → B (Ω (.inr i)) = [] := hs
  -- stage 1: Y4
  obtain ⟨t1, ht1, hr1⟩ := Paper2.YaoIndexDecoder.physical_index_decode (y4Place Ω) B x y
    (selectorCount t (paddedEdgeBits e) lambda) (payloadCount t (paddedEdgeBits e) lambda)
    (paddedEdgeCount e) hx hy hsel hpay hpow
    (hsi 15 (by decide)) (hsi 16 (by decide)) (hsi 17 (by decide)) (hsi 9 (by decide))
    (hsi 10 (by decide)) (hsi 11 (by decide)) (hsi 12 (by decide)) (hsi 13 (by decide))
    (hsi 18 (by decide))
  set B1 := Paper2.YaoIndexDecoder.outBank (y4Place Ω) B x y
    (selectorCount t (paddedEdgeBits e) lambda) (payloadCount t (paddedEdgeBits e) lambda)
    (paddedEdgeCount e) with hB1
  have hB1v : B1 = Function.update (Function.update (Function.update (Function.update
      (Function.update B (Ω (.inr 9)) (List.replicate vtx.val true))
        (Ω (.inr 10)) (List.replicate z.val true))
        (Ω (.inr 11)) (List.replicate g.val true))
        (Ω (.inr 12)) (List.replicate a.val true))
        (Ω (.inr 13)) (List.replicate l.val true) := by
    rw [hB1, Paper2.YaoIndexDecoder.outBank, e8, e9, e10, e11, e12]
    rfl
  rw [hB1v] at hr1
  -- stage 2: Y3
  obtain ⟨t2, ht2, c2, hr2⟩ := Paper2.YaoPositionFull.physical_position (y3Place Ω)
    (Function.update (Function.update (Function.update (Function.update
      (Function.update B (Ω (.inr 9)) (List.replicate vtx.val true))
        (Ω (.inr 10)) (List.replicate z.val true))
        (Ω (.inr 11)) (List.replicate g.val true))
        (Ω (.inr 12)) (List.replicate a.val true))
        (Ω (.inr 13)) (List.replicate l.val true)) edges a vtx
    (by simp [y3Place, f13, hinj.eq_iff, hbody]) (by simp [y3Place, f13, hinj.eq_iff])
    (by simp [y3Place, f13, hinj.eq_iff, hK]) (by simp [y3Place, f13, hinj.eq_iff])
    (by simp [y3Place, f13, hinj.eq_iff, hsi 15 (by decide)])
    (by simp [y3Place, f13, hinj.eq_iff, hsi 16 (by decide)])
    (by simp [y3Place, f13, hinj.eq_iff, hsi 17 (by decide)])
    (by simp [y3Place, f13, hinj.eq_iff, hsi 18 (by decide)])
    (by simp [y3Place, f13, hinj.eq_iff, hsi 19 (by decide)])
    (by simp [y3Place, f13, hinj.eq_iff, hsi 14 (by decide)])
    (by simp [y3Place, f13, hinj.eq_iff, hsi 20 (by decide)])
    (by simp [y3Place, f13, hinj.eq_iff, hsi 21 (by decide)])
    (by simp [y3Place, f13, hinj.eq_iff, hsi 22 (by decide)])
  set p := (positionEval (paddedEdgesEval edges) a vtx).val with hp
  set B2 := Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update B (Ω (.inr 9)) (List.replicate vtx.val true))
        (Ω (.inr 10)) (List.replicate z.val true))
        (Ω (.inr 11)) (List.replicate g.val true))
        (Ω (.inr 12)) (List.replicate a.val true))
        (Ω (.inr 13)) (List.replicate l.val true))
        (Ω (.inr 14)) (List.replicate p true) with hB2
  change _ = (⟨none, c2, B2⟩ : TM2.Cfg (fun _ : J => Bool) _ _) at hr2
  -- stage 3: the entry core
  obtain ⟨t3, ht3, c3, hr3⟩ := physical_entry_core t lambda edges bits vtx z g a l
    (corePlace Ω) B2
    (by intro k; simp [hB2, corePlace, hinj.eq_iff, hreg])
    (by simp [hB2, corePlace, f7, hinj.eq_iff, hans])
    (by simp [hB2, corePlace, f7, hinj.eq_iff, hsi 15 (by decide)])
    (by simp [hB2, corePlace, f7, hinj.eq_iff, he])
    (by simp [hB2, corePlace, f7, hinj.eq_iff])
    (by simp [hB2, corePlace, f7, hinj.eq_iff])
    (by simp [hB2, corePlace, f7, hinj.eq_iff])
    (by simp [hB2, corePlace, f7, hinj.eq_iff, hp])
  set ans := matrixFromTape t lambda edges (readTape t (paddedEdgeBits e) lambda bits)
    (vtx, z) (g, a, l) with hansv
  change _ = (⟨none, c3, Function.update B2 (Ω (.inr 2)) [ans]⟩ :
    TM2.Cfg (fun _ : J => Bool) _ _) at hr3
  set B3 := Function.update B2 (Ω (.inr 2)) [ans] with hB3
  -- stage 4: clear the six Y4/Y3 outputs
  have hL : ∀ i, (B3 (outCells Ω i)).length ≤ x + y + arity t + 1 := by
    intro i
    have hvx : vtx.val ≤ x := by rw [← e8]; exact Nat.div_le_self _ _
    have hzx : z.val ≤ x := by rw [← e9]; exact Nat.mod_le _ _
    have hgy : g.val ≤ y := by
      rw [← e10]; exact (Nat.div_le_self _ _).trans (Nat.div_le_self _ _)
    have hay : a.val ≤ y := by
      rw [← e11]; exact (Nat.mod_le _ _).trans (Nat.div_le_self _ _)
    have hly : l.val ≤ y := by rw [← e12]; exact Nat.mod_le _ _
    have hpK : p < arity t + 1 := (positionEval (paddedEdgesEval edges) a vtx).isLt
    fin_cases i <;> simp [outCells, f6, hB3, hB2, hinj.eq_iff] <;> omega
  obtain ⟨t4, ht4, v4, hr4⟩ := Paper2.ClearAll.all_run (outCells Ω) (outCells_injective Ω)
    (x + y + arity t + 1) B3 hL none
  have hfin : Paper2.ClearAll.clearFrom (outCells Ω) 0 B3 = Function.update B (Ω (.inr 2))
      [(materialize t lambda edges bits).matrix ⟨x, hxr⟩ ⟨y, hyc⟩] := by
    rw [entry_value]
    funext j
    rw [Paper2.YaoPrelude.clearFrom_zero]
    by_cases hj : ∃ i, outCells Ω i = j
    · rw [if_pos hj]
      obtain ⟨i, rfl⟩ := hj
      fin_cases i <;> simp [outCells, f6, hinj.eq_iff, hsi 9 (by decide), hsi 10 (by decide),
        hsi 11 (by decide), hsi 12 (by decide), hsi 13 (by decide), hsi 14 (by decide)]
    · rw [if_neg hj]
      have h9 : j ≠ Ω (.inr 9) := fun h => hj ⟨0, h.symm⟩
      have h10 : j ≠ Ω (.inr 10) := fun h => hj ⟨1, h.symm⟩
      have h11 : j ≠ Ω (.inr 11) := fun h => hj ⟨2, h.symm⟩
      have h12 : j ≠ Ω (.inr 12) := fun h => hj ⟨3, h.symm⟩
      have h13 : j ≠ Ω (.inr 13) := fun h => hj ⟨4, h.symm⟩
      have h14 : j ≠ Ω (.inr 14) := fun h => hj ⟨5, h.symm⟩
      simp only [hB3, hB2, Function.update_apply, h9, h10, h11, h12, h13, h14, if_false]
      rfl
  rw [hfin] at hr4
  -- sequencing
  obtain ⟨u3, hu3, hrun3⟩ := BitMachineRawSequence.runs (entryCore (corePlace Ω))
    (Paper2.ClearAll.prog (outCells Ω))
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    (⟨0, by omega⟩ : Fin 7) (stageControl, blockControl t lambda) c3 none v4 B2 B3 _ t3 t4 hr3 hr4
  obtain ⟨u2, hu2, hrun2⟩ := BitMachineRawSequence.runs (Paper2.YaoPositionFull.program (y3Place Ω))
    (rest2 Ω) (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))
    Paper2.YaoPositionFull.startControl c2 ((stageControl, blockControl t lambda), none)
    ((stageControl, blockControl t lambda), v4) _ B2 _ t2 u3 hr2 hrun3
  obtain ⟨u1, hu1, hrun1⟩ := BitMachineRawSequence.runs (Paper2.YaoIndexDecoder.program (y4Place Ω))
    (rest1 Ω) Paper2.YaoIndexDecoder.startLabel
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    Paper2.YaoIndexDecoder.startControl Paper2.YaoIndexDecoder.startControl
    (Paper2.YaoPositionFull.startControl, ((stageControl, blockControl t lambda), none))
    (Paper2.YaoPositionFull.startControl, ((stageControl, blockControl t lambda), v4))
    B _ _ t1 u2 hr1 hrun2
  refine ⟨u1, ?_, _, hrun1⟩
  have hvx : vtx.val ≤ x := by rw [← e8]; exact Nat.div_le_self _ _
  have hay : a.val ≤ y := by
    rw [← e11]; exact (Nat.mod_le _ _).trans (Nat.div_le_self _ _)
  have hyq : y / payloadCount t (paddedEdgeBits e) lambda ≤ y := Nat.div_le_self _ _
  have m1 := Nat.mul_le_mul_right (2 * arity t + 3) hay
  have m2 := Nat.mul_le_mul_right (arity t) hay
  have m3 := Nat.mul_le_mul_left (arity t) (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hvx) 6)
  unfold entryClock
  omega

#print axioms entryClock_mono
#print axioms entry_value
#print axioms physical_one_entry

end Paper2.YaoOneEntry

end
