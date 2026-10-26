import EthInapproximability.CurrentPaper.WeightedRawWordsLog

/-! # S2b/c/d: cost₀, cols₀, rows₀ from master `B`, scratch cleared

From `B = unary b`: `w1 := b`, push one (`1+b`), `w0 := 64` (fixed unary),
`w2 := 64*(1+b)` (production multiplier), `w3 := clog 2 (64*(1+b))`
(production LogCopy, region cleared), `Y := 1+e` and consumer word 2 `:= 1+e`,
consumer word 4 `:= 2^e`, consumer word 3 `:= 2^(2^e)` (production unary
power, twice), then an exact-length clear of `w0..w3`. -/

namespace EthInapproximability.CurrentPaper.WeightedRawWords

open Turing BitMachineEncoding BitMachineStackEmbedding

noncomputable section

def mulSlots : Fin 6 ↪ Global where
  toFun
    | 0 => aux (.w 0)
    | 1 => aux (.w 1)
    | 2 => aux (.mul 0)
    | 3 => aux (.mul 1)
    | 4 => aux (.mul 2)
    | 5 => aux (.w 2)
  inj' := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [aux]

def pow1Slots : MatrixUnaryPower.Stack ↪ Global where
  toFun
    | .inl 0 => rawCell 4
    | .inl 1 => aux (.pw 0)
    | .inl 2 => aux (.pw 1)
    | .inr () => aux (.w 3)
  inj' := by
    intro x y h
    rcases x with x | x <;> rcases y with y | y
    all_goals first
      | (fin_cases x <;> fin_cases y <;> simp_all [aux, rawCell, cons, WeightedActualSizeSuffix.scaleKey, ETHScaleGlobalLog.raw])
      | (fin_cases x <;> simp_all [aux, rawCell, cons, WeightedActualSizeSuffix.scaleKey, ETHScaleGlobalLog.raw])
      | (fin_cases y <;> simp_all [aux, rawCell, cons, WeightedActualSizeSuffix.scaleKey, ETHScaleGlobalLog.raw])
      | rfl

def pow2Slots : MatrixUnaryPower.Stack ↪ Global where
  toFun
    | .inl 0 => rawCell 3
    | .inl 1 => aux (.pw 0)
    | .inl 2 => aux (.pw 1)
    | .inr () => rawCell 4
  inj' := by
    intro x y h
    rcases x with x | x <;> rcases y with y | y
    all_goals first
      | (fin_cases x <;> fin_cases y <;> simp_all [aux, rawCell, cons, WeightedActualSizeSuffix.scaleKey, ETHScaleGlobalLog.raw])
      | (fin_cases x <;> simp_all [aux, rawCell, cons, WeightedActualSizeSuffix.scaleKey, ETHScaleGlobalLog.raw])
      | (fin_cases y <;> simp_all [aux, rawCell, cons, WeightedActualSizeSuffix.scaleKey, ETHScaleGlobalLog.raw])
      | rfl

def scratchCells : Fin 4 → Global
  | 0 => aux (.w 0)
  | 1 => aux (.w 1)
  | 2 => aux (.w 2)
  | 3 => aux (.w 3)

theorem scratchCells_injective : Function.Injective scratchCells := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [scratchCells, aux]

def cB := copyProg (aux .B) (aux (.w 1)) (by simp [aux]) (by simp [aux]) (by simp [aux])
def cY := copyProg (aux (.w 3)) (aux .Y) (by simp [aux]) (by simp [aux]) (by simp [aux])
def cW2 := copyProg (aux .Y) (rawCell 2) (aux_ne_rawCell 2 _) (by simp [aux])
  (rawCell_ne_aux 2 _)

abbrev PowCtrl := MatrixUnaryPower.Control
def powCtrl : PowCtrl := ((false, false), none)

def p10 := BitMachineRawSequence.program
  (MatrixStage4ScalarPreparationOps.unaryPowerProgram pow2Slots)
  (clearProgram scratchCells) 0 powCtrl ((), none)
def p9 := BitMachineRawSequence.program
  (MatrixStage4ScalarPreparationOps.unaryPowerProgram pow1Slots) p10
  (BitMachineRawSequence.leftLabel (.inr false)) powCtrl (powCtrl, ((), none))
def p8 := BitMachineRawSequence.program cW2 p9
  (BitMachineRawSequence.leftLabel (.inr false)) none (powCtrl, (powCtrl, ((), none)))
def p7 := BitMachineRawSequence.program (SourceClauseFixedUnary.program (aux .Y) 1) p8
  (BitMachineRawSequence.leftLabel .scan) () (none, (powCtrl, (powCtrl, ((), none))))
def p6 := BitMachineRawSequence.program cY p7
  (BitMachineRawSequence.leftLabel 0) none ((), (none, (powCtrl, (powCtrl, ((), none)))))
def p5 := BitMachineRawSequence.program logStageProgram p6
  (BitMachineRawSequence.leftLabel .scan)
  (ETHParameterScaleMachineLogCopy.copyControl none, (none, ((), none)))
  (none, ((), (none, (powCtrl, (powCtrl, ((), none))))))
def p4 := BitMachineRawSequence.program
  (MatrixStage4ScalarPreparationOps.multiplyProgram mulSlots) p5
  (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (.inl .scan))) false
  ((ETHParameterScaleMachineLogCopy.copyControl none, (none, ((), none))),
    (none, ((), (none, (powCtrl, (powCtrl, ((), none)))))))
def p3 := BitMachineRawSequence.program (SourceClauseFixedUnary.program (aux (.w 0)) 64) p4
  (BitMachineRawSequence.leftLabel .outer) ()
  (false, ((ETHParameterScaleMachineLogCopy.copyControl none, (none, ((), none))),
    (none, ((), (none, (powCtrl, (powCtrl, ((), none))))))))
def p2 := BitMachineRawSequence.program (SourceClauseFixedUnary.program (aux (.w 1)) 1) p3
  (BitMachineRawSequence.leftLabel 0) ()
  ((), (false, ((ETHParameterScaleMachineLogCopy.copyControl none, (none, ((), none))),
    (none, ((), (none, (powCtrl, (powCtrl, ((), none)))))))))
/-- The S2 cost/columns/rows program. -/
def costProgram := BitMachineRawSequence.program cB p2
  (BitMachineRawSequence.leftLabel 0) none
  ((), ((), (false, ((ETHParameterScaleMachineLogCopy.copyControl none, (none, ((), none))),
    (none, ((), (none, (powCtrl, (powCtrl, ((), none))))))))))

abbrev CostCtrlT := BitMachineRawSequence.Control (Option Bool)
  (BitMachineRawSequence.Control Unit (BitMachineRawSequence.Control Unit
    (BitMachineRawSequence.Control Bool (BitMachineRawSequence.Control
      (BitMachineRawSequence.Control ETHParameterScaleMachineLogCopy.Control
        (BitMachineRawSequence.Control (Option Bool) (Unit × Option Bool)))
      (BitMachineRawSequence.Control (Option Bool) (BitMachineRawSequence.Control Unit
        (BitMachineRawSequence.Control (Option Bool)
          (BitMachineRawSequence.Control MatrixUnaryPower.Control
            (BitMachineRawSequence.Control MatrixUnaryPower.Control (Unit × Option Bool))))))))))

def costCtrl : CostCtrlT := (none,
  ((), ((), (false, ((ETHParameterScaleMachineLogCopy.copyControl none, (none, ((), none))),
    (none, ((), (none, (powCtrl, (powCtrl, ((), none)))))))))))

/-- `e = clog 2 (64*(1+b))`. -/
def costExp (b : ℕ) : ℕ := Nat.clog 2 (64 * (1 + b))

def costFinal (G : Global → List Bool) (b : ℕ) : Global → List Bool :=
  Function.update (Function.update (Function.update (Function.update G
    (aux .Y) (List.replicate (1 + costExp b) true))
    (rawCell 2) (List.replicate (1 + costExp b) true))
    (rawCell 4) (List.replicate (2 ^ costExp b) true))
    (rawCell 3) (List.replicate (2 ^ 2 ^ costExp b) true)

def costBound (b : ℕ) : ℕ :=
  (2*b+2) + 2 + 65 + MatrixAddressMachine.exactTime 64 (1+b) 0 +
    logStageBound (64 * (1+b)) + (2 * costExp b + 2) + 2 + (2 * (1 + costExp b) + 2) +
    (4 * 2 ^ costExp b + 5 * costExp b + 7) +
    (4 * 2 ^ 2 ^ costExp b + 5 * 2 ^ costExp b + 7) +
    ((64 + (1 + b) + 64 * (1 + b) + costExp b) + 4 + 2) + 10

theorem cleared_update_mem {n : ℕ} (cells : Fin n → Global) (S : Global → List Bool)
    (a : Global) (u : List Bool) (ha : ∃ i, cells i = a) :
    BitMachineClearBank.cleared cells (Function.update S a u) =
      BitMachineClearBank.cleared cells S := by
  funext j
  by_cases hj : j = a
  · subst hj
    simp [BitMachineClearBank.cleared, ha]
  · simp [BitMachineClearBank.cleared, hj]

theorem cleared_eq_self {n : ℕ} (cells : Fin n → Global) (S : Global → List Bool)
    (h : ∀ i, S (cells i) = []) : BitMachineClearBank.cleared cells S = S := by
  funext j
  unfold BitMachineClearBank.cleared
  split_ifs with hc
  · obtain ⟨i, rfl⟩ := hc
    exact (h i).symm
  · rfl

@[simp] theorem aux_inj' (a b : Aux) : aux a = aux b ↔ a = b :=
  ⟨fun h => Sum.inr.inj h, fun h => h ▸ rfl⟩

@[simp] theorem rawCell_inj' (i j : Fin 6) : rawCell i = rawCell j ↔ i = j := by
  constructor
  · intro h
    simpa [rawCell, cons, WeightedActualSizeSuffix.scaleKey, ETHScaleGlobalLog.raw] using h
  · intro h; rw [h]

attribute [simp] aux_ne_rawCell rawCell_ne_aux

theorem cost_run (b : ℕ) (G : Global → List Bool)
    (hB : G (aux .B) = List.replicate b true)
    (hw : ∀ i, G (aux (.w i)) = []) (hm : ∀ i, G (aux (.mul i)) = [])
    (hp : ∀ i, G (aux (.pw i)) = []) (hL : ∀ k, G (aux (.log k)) = [])
    (hcs : G (aux .cs) = []) (hY : G (aux .Y) = [])
    (h2 : G (rawCell 2) = []) (h3 : G (rawCell 3) = []) (h4 : G (rawCell 4) = []) :
    ∃ t ≤ costBound b,
      ((advance costProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan), costCtrl, G⟩ :
          TM2.Cfg (fun _ : Global => Bool) _ _) =
        ⟨none, costCtrl, costFinal G b⟩ := by
  set e := costExp b with he
  set m := 64 * (1 + b) with hmdef
  -- step 1: copy B → w1
  have s1 := copy_word (aux .B) (aux (.w 1)) (by simp) (by simp) (by simp)
    G (hw 1) hcs
  rw [hB] at s1
  simp only [List.length_replicate] at s1
  set B1 := Function.update G (aux (.w 1)) (List.replicate b true) with hB1
  -- step 2: push one on w1
  have s2 := push_unary (aux (.w 1)) B1 1
  have hB1w1 : B1 (aux (.w 1)) = List.replicate b true := by simp [hB1]
  rw [hB1w1, hB1, Function.update_idem, ← List.replicate_add] at s2
  set B2 := Function.update G (aux (.w 1)) (List.replicate (1 + b) true) with hB2
  -- step 3: push 64 on w0
  have s3 := push_unary (aux (.w 0)) B2 64
  have hB2w0 : B2 (aux (.w 0)) = [] := by simp [hB2, hw]
  rw [hB2w0, List.append_nil] at s3
  set B3 := Function.update B2 (aux (.w 0)) (List.replicate 64 true) with hB3
  -- step 4: multiply
  have s4 := MatrixStage4ScalarPreparationOps.multiply_run mulSlots B3 64 (1 + b)
    (by simp [mulSlots, hB3]) (by simp [mulSlots, hB3, hB2])
    (by simp [mulSlots, hB3, hB2, hm]) (by simp [mulSlots, hB3, hB2, hm])
    (by simp [mulSlots, hB3, hB2, hm])
  have hB3w2 : B3 (mulSlots 5) = [] := by simp [mulSlots, hB3, hB2, hw]
  rw [hB3w2, List.append_nil] at s4
  have hm5 : mulSlots 5 = aux (.w 2) := rfl
  rw [hm5] at s4
  set B4 := Function.update B3 (aux (.w 2)) (List.replicate (64 * (1 + b)) true) with hB4
  -- step 5: log stage
  obtain ⟨t5, ht5, s5⟩ := log_stage m B4 (by simp [hB4, hmdef])
    (by intro k; simp [hB4, hB3, hB2, hL])
    (by simp [hB4, hB3, hB2, hw]) (by simp [hB4, hB3, hB2, hcs])
  set B5 := Function.update B4 (aux (.w 3)) (List.replicate e true) with hB5
  -- step 6: copy w3 → Y
  have s6 := copy_word (aux (.w 3)) (aux .Y) (by simp) (by simp) (by simp)
    B5 (by simp [hB5, hB4, hB3, hB2, hY]) (by simp [hB5, hB4, hB3, hB2, hcs])
  have hB5w3 : B5 (aux (.w 3)) = List.replicate e true := by simp [hB5]
  rw [hB5w3] at s6
  simp only [List.length_replicate] at s6
  -- step 7: push one on Y
  have s7 := push_unary (aux .Y) (Function.update B5 (aux .Y) (List.replicate e true)) 1
  rw [Function.update_self, Function.update_idem, ← List.replicate_add] at s7
  set B7 := Function.update B5 (aux .Y) (List.replicate (1 + e) true) with hB7
  -- step 8: copy Y → raw 2
  have s8 := copy_word (aux .Y) (rawCell 2) (aux_ne_rawCell 2 _) (by simp)
    (rawCell_ne_aux 2 _) B7
    (by simp [hB7, hB5, hB4, hB3, hB2, aux_ne_rawCell, h2])
    (by simp [hB7, hB5, hB4, hB3, hB2, hcs])
  have hB7Y : B7 (aux .Y) = List.replicate (1 + e) true := by simp [hB7]
  rw [hB7Y] at s8
  simp only [List.length_replicate] at s8
  set B8 := Function.update B7 (rawCell 2) (List.replicate (1 + e) true) with hB8
  -- step 9: power e → raw 4
  obtain ⟨t9, ht9, s9⟩ := MatrixStage4ScalarPreparationOps.unary_power_run pow1Slots B8 e
    (by simp [pow1Slots, hB8, hB7, hB5, aux_ne_rawCell])
    (by simp [pow1Slots, hB8, hB7, hB5, hB4, hB3, hB2, aux_ne_rawCell, rawCell_ne_aux, h4])
    (by simp [pow1Slots, hB8, hB7, hB5, hB4, hB3, hB2, aux_ne_rawCell, hp])
    (by simp [pow1Slots, hB8, hB7, hB5, hB4, hB3, hB2, aux_ne_rawCell, hp])
  have hp1 : pow1Slots (.inl 0) = rawCell 4 := rfl
  rw [hp1] at s9
  set B9 := Function.update B8 (rawCell 4) (List.replicate (2 ^ e) true) with hB9
  -- step 10: power 2^e → raw 3
  obtain ⟨t10, ht10, s10⟩ := MatrixStage4ScalarPreparationOps.unary_power_run pow2Slots B9
    (2 ^ e)
    (by simp [pow2Slots, hB9])
    (by simp [pow2Slots, hB9, hB8, hB7, hB5, hB4, hB3, hB2, aux_ne_rawCell, rawCell_ne_aux,
      h3])
    (by simp [pow2Slots, hB9, hB8, hB7, hB5, hB4, hB3, hB2, aux_ne_rawCell, hp])
    (by simp [pow2Slots, hB9, hB8, hB7, hB5, hB4, hB3, hB2, aux_ne_rawCell, hp])
  have hp2 : pow2Slots (.inl 0) = rawCell 3 := rfl
  rw [hp2] at s10
  set B10 := Function.update B9 (rawCell 3) (List.replicate (2 ^ 2 ^ e) true) with hB10
  -- step 11: clear w0..w3
  have s11 := clear_run scratchCells scratchCells_injective B10
  have hsum : (∑ i, (B10 (scratchCells i)).length) = 64 + (1 + b) + m + e := by
    simp [Fin.sum_univ_four, scratchCells, hB10, hB9, hB8, hB7, hB5, hB4, hB3, hB2,
      aux_ne_rawCell, hmdef] <;> omega
  have hfin : BitMachineClearBank.cleared scratchCells B10 = costFinal G b := by
    have n3 : ∀ i, scratchCells i ≠ rawCell 3 := fun i => by
      fin_cases i <;> exact aux_ne_rawCell _ _
    have n4 : ∀ i, scratchCells i ≠ rawCell 4 := fun i => by
      fin_cases i <;> exact aux_ne_rawCell _ _
    have n2 : ∀ i, scratchCells i ≠ rawCell 2 := fun i => by
      fin_cases i <;> exact aux_ne_rawCell _ _
    have nY : ∀ i, scratchCells i ≠ aux .Y := fun i => by
      fin_cases i <;> simp [scratchCells, aux]
    rw [hB10, cleared_update_comm _ _ _ _ n3, hB9, cleared_update_comm _ _ _ _ n4,
      hB8, cleared_update_comm _ _ _ _ n2, hB7, cleared_update_comm _ _ _ _ nY,
      hB5, cleared_update_mem scratchCells _ (aux (.w 3)) _ ⟨3, rfl⟩, hB4, cleared_update_mem scratchCells _ (aux (.w 2)) _ ⟨2, rfl⟩,
      hB3, cleared_update_mem scratchCells _ (aux (.w 0)) _ ⟨0, rfl⟩, hB2, cleared_update_mem scratchCells _ (aux (.w 1)) _ ⟨1, rfl⟩,
      cleared_eq_self _ _ (fun i => by fin_cases i <;> simp [scratchCells, hw])]
    rfl
  rw [hfin] at s11
  -- compose, innermost first
  obtain ⟨u10, hu10, r10⟩ := BitMachineRawSequence.runs
    (MatrixStage4ScalarPreparationOps.unaryPowerProgram pow2Slots) (clearProgram scratchCells)
    (.inr false) 0 powCtrl powCtrl ((), none) ((), none) B9 B10 (costFinal G b) _ _ s10 s11
  obtain ⟨u9, hu9, r9⟩ := BitMachineRawSequence.runs
    (MatrixStage4ScalarPreparationOps.unaryPowerProgram pow1Slots) p10
    (.inr false) (BitMachineRawSequence.leftLabel (.inr false)) powCtrl powCtrl
    (powCtrl, ((), none)) (powCtrl, ((), none)) B8 B9 (costFinal G b) _ _ s9 r10
  obtain ⟨u8, hu8, r8⟩ := BitMachineRawSequence.runs cW2 p9
    .scan (BitMachineRawSequence.leftLabel (.inr false)) none none
    (powCtrl, (powCtrl, ((), none))) (powCtrl, (powCtrl, ((), none))) B7 B8 (costFinal G b)
    _ _ s8 r9
  obtain ⟨u7, hu7, r7⟩ := BitMachineRawSequence.runs
    (SourceClauseFixedUnary.program (aux .Y) 1) p8
    0 (BitMachineRawSequence.leftLabel .scan) () ()
    (none, (powCtrl, (powCtrl, ((), none)))) (none, (powCtrl, (powCtrl, ((), none))))
    (Function.update B5 (aux .Y) (List.replicate e true)) B7 (costFinal G b) _ _ s7 r8
  obtain ⟨u6, hu6, r6⟩ := BitMachineRawSequence.runs cY p7
    .scan (BitMachineRawSequence.leftLabel 0) none none
    ((), (none, (powCtrl, (powCtrl, ((), none)))))
    ((), (none, (powCtrl, (powCtrl, ((), none)))))
    B5 (Function.update B5 (aux .Y) (List.replicate e true)) (costFinal G b) _ _ s6 r7
  obtain ⟨u5, hu5, r5⟩ := BitMachineRawSequence.runs logStageProgram p6
    (BitMachineRawSequence.leftLabel (.inl .scan)) (BitMachineRawSequence.leftLabel .scan)
    (ETHParameterScaleMachineLogCopy.copyControl none, (none, ((), none)))
    (ETHParameterScaleMachineLogCopy.copyControl none, (none, ((), none)))
    (none, ((), (none, (powCtrl, (powCtrl, ((), none))))))
    (none, ((), (none, (powCtrl, (powCtrl, ((), none))))))
    B4 B5 (costFinal G b) _ _ s5 r6
  obtain ⟨u4, hu4, r4⟩ := BitMachineRawSequence.runs
    (MatrixStage4ScalarPreparationOps.multiplyProgram mulSlots) p5
    .outer (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (.inl .scan)))
    false false
    ((ETHParameterScaleMachineLogCopy.copyControl none, (none, ((), none))),
      (none, ((), (none, (powCtrl, (powCtrl, ((), none)))))))
    ((ETHParameterScaleMachineLogCopy.copyControl none, (none, ((), none))),
      (none, ((), (none, (powCtrl, (powCtrl, ((), none)))))))
    B3 B4 (costFinal G b) _ _ s4 r5
  obtain ⟨u3, hu3, r3⟩ := BitMachineRawSequence.runs
    (SourceClauseFixedUnary.program (aux (.w 0)) 64) p4
    0 (BitMachineRawSequence.leftLabel .outer) () ()
    (false, ((ETHParameterScaleMachineLogCopy.copyControl none, (none, ((), none))),
      (none, ((), (none, (powCtrl, (powCtrl, ((), none))))))))
    (false, ((ETHParameterScaleMachineLogCopy.copyControl none, (none, ((), none))),
      (none, ((), (none, (powCtrl, (powCtrl, ((), none))))))))
    B2 B3 (costFinal G b) _ _ s3 r4
  obtain ⟨u2, hu2, r2⟩ := BitMachineRawSequence.runs
    (SourceClauseFixedUnary.program (aux (.w 1)) 1) p3
    0 (BitMachineRawSequence.leftLabel 0) () ()
    ((), (false, ((ETHParameterScaleMachineLogCopy.copyControl none, (none, ((), none))),
      (none, ((), (none, (powCtrl, (powCtrl, ((), none)))))))))
    ((), (false, ((ETHParameterScaleMachineLogCopy.copyControl none, (none, ((), none))),
      (none, ((), (none, (powCtrl, (powCtrl, ((), none)))))))))
    B1 B2 (costFinal G b) _ _ s2 r3
  obtain ⟨u1, hu1, r1⟩ := BitMachineRawSequence.runs cB p2
    .scan (BitMachineRawSequence.leftLabel 0) none none
    ((), ((), (false, ((ETHParameterScaleMachineLogCopy.copyControl none, (none, ((), none))),
      (none, ((), (none, (powCtrl, (powCtrl, ((), none))))))))))
    ((), ((), (false, ((ETHParameterScaleMachineLogCopy.copyControl none, (none, ((), none))),
      (none, ((), (none, (powCtrl, (powCtrl, ((), none))))))))))
    G B1 (costFinal G b) _ _ s1 r2
  refine ⟨u1, ?_, r1⟩
  rw [hsum] at hu10
  unfold costBound
  rw [← he, ← hmdef]
  omega

#print axioms cost_run

end
end EthInapproximability.CurrentPaper.WeightedRawWords
