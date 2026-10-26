import CurrentAdditive.GaussGetterCopy64

/-! The exact ordinary bank layout expected by one embedded matrix fetch.
The reset and charged copy machines can establish this layout; the theorem
below removes the abstract embedding frame from the getter interface. -/

namespace CurrentAdditive.GaussGetterReady64

open EthInapproximability.CurrentPaper

abbrev Stack := Fin 64

def prepared (matrix : List Bool) (row column : Nat) : Stack → List Bool :=
  fun j => if j = 8 then matrix else if j = 41 then List.replicate row true
    else if j = 42 then List.replicate column true else []

theorem initial_ready (matrix : List Bool) (row column : Nat) :
    let init := CurrentAdditive.GaussGetterIntegrated.firstFrame
      (CurrentAdditive.GaussNestedGetter.firstFrame
        (CurrentAdditive.GaussNestedGetter.inputForeign column)
        (CurrentAdditive.CylinderContextScanStep.initial matrix row))
    ∀ j : Fin 22,
      init.stk j = prepared matrix row column
        (CurrentAdditive.GaussGetterSafe64.slot j) := by
  dsimp only
  intro j
  change BitMachineStackEmbedding.bank
      CurrentAdditive.GaussNestedGetter.firstMap
      (CurrentAdditive.GaussNestedGetter.inputForeign column)
      (CurrentAdditive.CylinderContextScanStep.initialBank matrix row) j =
    prepared matrix row column (CurrentAdditive.GaussGetterSafe64.slot j)
  by_cases h : ∃ k : CurrentAdditive.CylinderContextScanStep.Stack,
      CurrentAdditive.GaussNestedGetter.firstMap k = j
  · obtain ⟨k, hk⟩ := h
    subst j
    rw [BitMachineStackEmbedding.bank_at]
    fin_cases k <;>
      simp [CurrentAdditive.GaussNestedGetter.firstMap,
        CurrentAdditive.CylinderContextScanStep.initialBank,
        CurrentAdditive.GaussGetterSafe64.slot, prepared]
  · rw [BitMachineStackEmbedding.bank_outside _ _ _ j h]
    fin_cases j <;>
      simp_all [CurrentAdditive.GaussNestedGetter.inputForeign,
        CurrentAdditive.GaussNestedGetter.firstMap,
        CurrentAdditive.GaussGetterSafe64.slot, prepared]
    all_goals
      exfalso
      first
      | exact h 8 (by decide)
      | exact h 10 (by decide)

theorem fetch_prepared
    (rowPre rowSuffix cellPre cellSuffix : List (List Bool))
    (cell : List Bool) :
    let row := SourceListEncoding.encode (cellPre ++ cell :: cellSuffix)
    let matrix := SourceListEncoding.encode (rowPre ++ row :: rowSuffix)
    let init := CurrentAdditive.GaussGetterIntegrated.firstFrame
      (CurrentAdditive.GaussNestedGetter.firstFrame
        (CurrentAdditive.GaussNestedGetter.inputForeign cellPre.length)
        (CurrentAdditive.CylinderContextScanStep.initial
          matrix rowPre.length))
    ∃ t ≤ 140 * (matrix.length + 1)^3,
      (CurrentAdditive.GaussGetterSafe64.run t
        ⟨init.l, init.var,
          prepared matrix rowPre.length cellPre.length⟩).l = none ∧
      (CurrentAdditive.GaussGetterSafe64.run t
        ⟨init.l, init.var,
          prepared matrix rowPre.length cellPre.length⟩).stk 38 = cell ∧
      (CurrentAdditive.GaussGetterSafe64.run t
        ⟨init.l, init.var,
          prepared matrix rowPre.length cellPre.length⟩).stk 8 = matrix := by
  dsimp only
  have hready := initial_ready
    (SourceListEncoding.encode
      (rowPre ++ SourceListEncoding.encode
        (cellPre ++ cell :: cellSuffix) :: rowSuffix))
    rowPre.length cellPre.length
  obtain ⟨t, ht, hh, h38, _, h8, _⟩ :=
    CurrentAdditive.GaussGetterSafe64.canonical_getter_from_ready
      rowPre rowSuffix cellPre cellSuffix cell
      (prepared
        (SourceListEncoding.encode
          (rowPre ++ SourceListEncoding.encode
            (cellPre ++ cell :: cellSuffix) :: rowSuffix))
        rowPre.length cellPre.length) hready
  exact ⟨t, ht, hh, h38, h8⟩

#print axioms initial_ready
#print axioms fetch_prepared

end CurrentAdditive.GaussGetterReady64
