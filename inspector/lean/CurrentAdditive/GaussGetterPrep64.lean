import CurrentAdditive.GaussGetterReady64

/-! A concrete bank preparation for one nested matrix fetch. The matrix and
the two unary indices are retained on caller banks while a charged reset and
two charged broadcasts prepare the embedded getter's scratch stacks. -/

namespace CurrentAdditive.GaussGetterPrep64

open EthInapproximability.CurrentPaper

abbrev Stack := Fin 64

def resetState (S : Stack → List Bool) : Stack → List Bool :=
  BitMachineClearBank.cleared GaussGetterReset64.resetBank S

def rowState (row : Nat) (S : Stack → List Bool) : Stack → List Bool :=
  SourceClausePreservingBroadcast.result 15 63 [41]
    (List.replicate row true) (resetState S)

def finalState (row column : Nat) (S : Stack → List Bool) :
    Stack → List Bool :=
  SourceClausePreservingBroadcast.result 16 63 [42]
    (List.replicate column true) (rowState row S)

theorem reset_range (j : Stack) :
    (∃ i : Fin 21, GaussGetterReset64.resetBank i = j) ↔
      32 ≤ j.val ∧ j.val < 53 := by
  fin_cases j <;> decide

theorem final_ready (S : Stack → List Bool) (matrix : List Bool)
    (row column : Nat)
    (hmat : S 8 = matrix) :
    ∀ j : Fin 22,
      finalState row column S (GaussGetterSafe64.slot j) =
        GaussGetterReady64.prepared matrix row column
          (GaussGetterSafe64.slot j) := by
  intro j
  fin_cases j <;>
    simp [finalState, rowState, resetState,
      SourceClausePreservingBroadcast.result,
      BitMachineBroadcast.prepend, BitMachineClearBank.cleared,
      reset_range, GaussGetterSafe64.slot,
      GaussGetterReady64.prepared, hmat]

theorem row_preserves_low (S : Stack → List Bool) (row : Nat)
    (hrow : S 15 = List.replicate row true)
    (j : Stack) (hj : j.val < 32) :
    rowState row S j = S j := by
  by_cases h : j = 15
  · subst j
    change (SourceClausePreservingBroadcast.result 15 63 [41]
      (List.replicate row true) (resetState S)) 15 = S 15
    rw [SourceClausePreservingBroadcast.source_restored 15 63 [41]
      (by decide), ← hrow]
  · change (SourceClausePreservingBroadcast.result 15 63 [41]
      (List.replicate row true) (resetState S)) j = S j
    rw [GaussGetterCopy64.copy_preserves_other 15 41 j
      (List.replicate row true) (resetState S)
      h (by intro he; have hv := congrArg Fin.val he; omega)
      (by intro he; have hv := congrArg Fin.val he; omega)]
    exact GaussGetterReset64.reset_preserves S j (Or.inl hj)

theorem final_preserves_low (S : Stack → List Bool) (row column : Nat)
    (hrow : S 15 = List.replicate row true)
    (hcolumn : S 16 = List.replicate column true)
    (j : Stack) (hj : j.val < 32) :
    finalState row column S j = S j := by
  by_cases h : j = 16
  · subst j
    change (SourceClausePreservingBroadcast.result 16 63 [42]
      (List.replicate column true) (rowState row S)) 16 = S 16
    rw [SourceClausePreservingBroadcast.source_restored 16 63 [42]
      (by decide), ← hcolumn]
  · change (SourceClausePreservingBroadcast.result 16 63 [42]
      (List.replicate column true) (rowState row S)) j = S j
    rw [GaussGetterCopy64.copy_preserves_other 16 42 j
      (List.replicate column true) (rowState row S)
      h (by intro he; have hv := congrArg Fin.val he; omega)
      (by intro he; have hv := congrArg Fin.val he; omega)]
    exact row_preserves_low S row hrow j hj

theorem physical_preparation (S : Stack → List Bool)
    (matrix : List Bool) (row column : Nat)
    (hmat : S 8 = matrix)
    (hrow : S 15 = List.replicate row true)
    (hcolumn : S 16 = List.replicate column true)
    (htemp : S 63 = []) :
    GaussGetterReset64.run
      ((∑ i : Fin 21, (S (GaussGetterReset64.resetBank i)).length) + 22)
      ⟨some (.clear 0), ((), none), S⟩ =
        ⟨some .done, ((), none), resetState S⟩ ∧
    GaussGetterCopy64.run 15 41 (2 * row + 3)
      ⟨some .scan, ((), none), resetState S⟩ =
        ⟨none, ((), none), rowState row S⟩ ∧
    GaussGetterCopy64.run 16 42 (2 * column + 3)
      ⟨some .scan, ((), none), rowState row S⟩ =
        ⟨none, ((), none), finalState row column S⟩ ∧
    (∀ j : Fin 22,
      finalState row column S (GaussGetterSafe64.slot j) =
        GaussGetterReady64.prepared matrix row column
          (GaussGetterSafe64.slot j)) := by
  have h0row : resetState S 15 = List.replicate row true := by
    rw [resetState, GaussGetterReset64.reset_preserves S 15 (by decide)]
    exact hrow
  have h0column : resetState S 16 = List.replicate column true := by
    rw [resetState, GaussGetterReset64.reset_preserves S 16 (by decide)]
    exact hcolumn
  have h0temp : resetState S 63 = [] := by
    rw [resetState, GaussGetterReset64.reset_preserves S 63 (by decide)]
    exact htemp
  have h0rowTarget : resetState S 41 = [] := by
    simpa [resetState, GaussGetterReset64.resetBank] using
      GaussGetterReset64.reset_clears S (9 : Fin 21)
  have h0columnTarget : resetState S 42 = [] := by
    simpa [resetState, GaussGetterReset64.resetBank] using
      GaussGetterReset64.reset_clears S (10 : Fin 21)
  obtain ⟨hcopyRow, _, _, h1temp⟩ :=
    GaussGetterCopy64.copy_word 15 41 (by decide) (by decide)
      (by decide) (List.replicate row true) (resetState S)
      h0row h0temp h0rowTarget
  have h1column : rowState row S 16 = List.replicate column true := by
    rw [rowState]
    rw [GaussGetterCopy64.copy_preserves_other 15 41 16
      (List.replicate row true) (resetState S)
      (by decide) (by decide) (by decide)]
    exact h0column
  have h1columnTarget : rowState row S 42 = [] := by
    rw [rowState]
    rw [GaussGetterCopy64.copy_preserves_other 15 41 42
      (List.replicate row true) (resetState S)
      (by decide) (by decide) (by decide)]
    exact h0columnTarget
  have h1temp' : rowState row S 63 = [] := h1temp
  obtain ⟨hcopyColumn, _, _, _⟩ :=
    GaussGetterCopy64.copy_word 16 42 (by decide) (by decide)
      (by decide) (List.replicate column true) (rowState row S)
      h1column h1temp' h1columnTarget
  refine ⟨GaussGetterReset64.reset_run S,
    ?_, ?_, final_ready S matrix row column hmat⟩
  · simpa only [List.length_replicate] using hcopyRow
  · simpa only [List.length_replicate] using hcopyColumn

theorem fetch_after_preparation
    (rowPre rowSuffix cellPre cellSuffix : List (List Bool))
    (cell : List Bool) (S : Stack → List Bool)
    (hmat : S 8 = SourceListEncoding.encode
      (rowPre ++ SourceListEncoding.encode
        (cellPre ++ cell :: cellSuffix) :: rowSuffix)) :
    let row := SourceListEncoding.encode (cellPre ++ cell :: cellSuffix)
    let matrix := SourceListEncoding.encode (rowPre ++ row :: rowSuffix)
    let init := CurrentAdditive.GaussGetterIntegrated.firstFrame
      (CurrentAdditive.GaussNestedGetter.firstFrame
        (CurrentAdditive.GaussNestedGetter.inputForeign cellPre.length)
        (CurrentAdditive.CylinderContextScanStep.initial
          matrix rowPre.length))
    ∃ t ≤ 140 * (matrix.length + 1)^3,
      (GaussGetterSafe64.run t
        ⟨init.l, init.var,
          finalState rowPre.length cellPre.length S⟩).l = none ∧
      (GaussGetterSafe64.run t
        ⟨init.l, init.var,
          finalState rowPre.length cellPre.length S⟩).stk 38 = cell ∧
      (GaussGetterSafe64.run t
        ⟨init.l, init.var,
          finalState rowPre.length cellPre.length S⟩).stk 8 = matrix := by
  dsimp only
  have hready : ∀ j : Fin 22,
      (CurrentAdditive.GaussGetterIntegrated.firstFrame
        (CurrentAdditive.GaussNestedGetter.firstFrame
          (CurrentAdditive.GaussNestedGetter.inputForeign cellPre.length)
          (CurrentAdditive.CylinderContextScanStep.initial
            (SourceListEncoding.encode
              (rowPre ++ SourceListEncoding.encode
                (cellPre ++ cell :: cellSuffix) :: rowSuffix))
            rowPre.length))).stk j =
      finalState rowPre.length cellPre.length S
        (GaussGetterSafe64.slot j) := by
    intro j
    exact (GaussGetterReady64.initial_ready
      (SourceListEncoding.encode
        (rowPre ++ SourceListEncoding.encode
          (cellPre ++ cell :: cellSuffix) :: rowSuffix))
      rowPre.length cellPre.length j).trans
      ((final_ready S _ rowPre.length cellPre.length hmat j).symm)
  obtain ⟨t, ht, hh, h38, _, h8, _⟩ :=
    GaussGetterSafe64.canonical_getter_from_ready
      rowPre rowSuffix cellPre cellSuffix cell
      (finalState rowPre.length cellPre.length S) hready
  exact ⟨t, ht, hh, h38, h8⟩

#print axioms final_ready
#print axioms row_preserves_low
#print axioms final_preserves_low
#print axioms physical_preparation
#print axioms fetch_after_preparation

end CurrentAdditive.GaussGetterPrep64
