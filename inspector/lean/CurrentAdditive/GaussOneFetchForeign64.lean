import CurrentAdditive.GaussOneFetchProgram64

/-! Additive exact preservation result for the checked one-cell program.
This keeps index backups and previously fetched operands live across calls. -/

namespace CurrentAdditive.GaussOneFetchForeign64

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

theorem canonical_one_fetch_foreign
    (rowPre rowSuffix cellPre cellSuffix : List (List Bool))
    (cell : List Bool) (S : Fin 64 → List Bool)
    (hmat : S 8 = SourceListEncoding.encode
      (rowPre ++ SourceListEncoding.encode
        (cellPre ++ cell :: cellSuffix) :: rowSuffix))
    (hrow : S 15 = List.replicate rowPre.length true)
    (hcolumn : S 16 = List.replicate cellPre.length true)
    (htemp : S 63 = []) :
    let row := SourceListEncoding.encode (cellPre ++ cell :: cellSuffix)
    let matrix := SourceListEncoding.encode (rowPre ++ row :: rowSuffix)
    ∃ t ≤ GaussOneFetchProgram64.preparationClock S
        rowPre.length cellPre.length +
        140 * (matrix.length + 1)^3 + 1,
      (GaussOneFetchProgram64.run t
        (GaussOneFetchProgram64.initial S)).l = none ∧
      (GaussOneFetchProgram64.run t
        (GaussOneFetchProgram64.initial S)).stk 38 = cell ∧
      (GaussOneFetchProgram64.run t
        (GaussOneFetchProgram64.initial S)).stk 8 = matrix ∧
      (∀ j : Fin 64, j.val < 32 →
        (GaussOneFetchProgram64.run t
          (GaussOneFetchProgram64.initial S)).stk j = S j) ∧
      (GaussOneFetchProgram64.run t
        (GaussOneFetchProgram64.initial S)).stk 63 = [] := by
  dsimp only
  let matrix := SourceListEncoding.encode
    (rowPre ++ SourceListEncoding.encode
      (cellPre ++ cell :: cellSuffix) :: rowSuffix)
  let getInit := GaussGetterIntegrated.firstFrame
    (GaussNestedGetter.firstFrame
      (GaussNestedGetter.inputForeign cellPre.length)
      (CylinderContextScanStep.initial matrix rowPre.length))
  obtain ⟨tPrep, htPrep, hPrep⟩ :=
    GaussOneFetchProgram64.preparation_run S matrix
      rowPre.length cellPre.length hmat hrow hcolumn htemp
  have hready : ∀ j : Fin 22,
      getInit.stk j =
      GaussGetterPrep64.finalState rowPre.length cellPre.length S
        (GaussGetterSafe64.slot j) := by
    intro j
    exact (GaussGetterReady64.initial_ready matrix
      rowPre.length cellPre.length j).trans
      ((GaussGetterPrep64.final_ready S matrix rowPre.length
        cellPre.length hmat j).symm)
  obtain ⟨tGet, htGet, hGetHalt, hCell, _, hMatrix, hForeign⟩ :=
    GaussGetterSafe64.canonical_getter_from_ready
      rowPre rowSuffix cellPre cellSuffix cell
      (GaussGetterPrep64.finalState rowPre.length cellPre.length S)
      hready
  let getCfg : GaussGetterSafe64.Config :=
    ⟨getInit.l, getInit.var,
      GaussGetterPrep64.finalState rowPre.length cellPre.length S⟩
  let getFinal := GaussGetterSafe64.run tGet getCfg
  have hFixed := GaussOneFetchProgram64.getter_initial_fixed
    matrix rowPre.length cellPre.length
  have hGetRun :
      ((advance GaussGetterSafe64.program)^[tGet])
        (⟨some GaussOneFetchProgram64.getterStart,
          GaussOneFetchProgram64.getterControl,
          GaussGetterPrep64.finalState rowPre.length cellPre.length S⟩ :
          GaussGetterSafe64.Config) =
        ⟨none, getFinal.var, getFinal.stk⟩ := by
    rw [← hFixed.1, ← hFixed.2]
    change getFinal = ⟨none, getFinal.var, getFinal.stk⟩
    cases hfinal : getFinal with
    | mk l v T =>
        cases l with
        | none => rfl
        | some l =>
            have hh : getFinal.l = none := hGetHalt
            rw [hfinal] at hh
            contradiction
  obtain ⟨t, ht, hfull⟩ := BitMachineRawSequence.runs
    GaussOneFetchProgram64.preparationProgram
    GaussGetterSafe64.program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (.clear 0)))
    GaussOneFetchProgram64.getterStart
    ((((), none), ((), none)), ((), none))
    ((((), none), ((), none)), ((), none))
    GaussOneFetchProgram64.getterControl getFinal.var
    S (GaussGetterPrep64.finalState rowPre.length cellPre.length S)
    getFinal.stk tPrep tGet hPrep hGetRun
  have heq : GaussOneFetchProgram64.run t
      (GaussOneFetchProgram64.initial S) =
      ⟨none,
        (((((), none), ((), none)), ((), none)), getFinal.var),
        getFinal.stk⟩ := by
    simpa [GaussOneFetchProgram64.run,
      GaussOneFetchProgram64.initial,
      GaussOneFetchProgram64.program] using hfull
  refine ⟨t, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [heq]
  · rw [heq]
    exact hCell
  · rw [heq]
    exact hMatrix
  · intro j hj
    rw [heq]
    by_cases h8 : j = 8
    · subst j
      exact hMatrix.trans hmat.symm
    · exact (hForeign j (Or.inl ⟨hj, h8⟩)).trans
        (GaussGetterPrep64.final_preserves_low S
          rowPre.length cellPre.length hrow hcolumn j hj)
  · rw [heq]
    rw [hForeign 63 (Or.inr (by decide))]
    exact SourceClausePreservingBroadcast.temp_empty
      16 63 [42] (List.replicate cellPre.length true)
      (GaussGetterPrep64.rowState rowPre.length S)

#print axioms canonical_one_fetch_foreign

end CurrentAdditive.GaussOneFetchForeign64
