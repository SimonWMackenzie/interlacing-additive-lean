import Paper2.Y0LoadedParameters

/-! Full physical Yao entry from literal serialized input bits and basic
unary parameters. Two charged administrative handoffs connect the raw tape
copy, scalar loader, and frozen combined entry evaluator. -/

namespace Paper2.YaoEntryControllerJoin

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.YaoLowerBound
open Paper2.YaoLowerBound.Materialization
open Paper2.YaoLookup
open Paper2.YaoEntryParameterJoin
open Paper2.YaoParameterBank

abbrev LoadedLabel (t lambda : ℕ) :=
  BitMachineRawSequence.Label BitMachineCopy.Label (LiftLoaderLabel t lambda)
abbrev LoadedControl (t lambda : ℕ) := Option Bool × LiftLoaderControl t lambda
abbrev FullLabel (t lambda : ℕ) :=
  BitMachineRawSequence.Label (LoadedLabel t lambda)
    Paper2.YaoEntryComposition.Label
abbrev FullControl (t lambda : ℕ) :=
  LoadedControl t lambda × Paper2.YaoEntryComposition.Control

noncomputable def fullEntryProgram (t lambda : ℕ) :=
  BitMachineRawSequence.program
    (loadedParameterProgram t lambda) (embeddedEntryProgram t lambda)
    (.inl (.inr false) : Paper2.YaoEntryComposition.Label)
    (none,(loaderInitialControl t lambda,()))
    Paper2.YaoEntryComposition.initialControl

theorem physical_full_entry_controller {v e : ℕ} (t lambda : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (bits : SerializedTape t (paddedEdgeBits e) lambda)
    (vertex : Fin v)
    (z : Fin (selectorCount t (paddedEdgeBits e) lambda))
    (g : Fin (2 ^ (t - 1))) (a : Fin (paddedEdgeCount e))
    (l : Fin (payloadCount t (paddedEdgeBits e) lambda)) :
    ∃ (scalarSteps routeSteps parameterSteps copySteps loadSteps
       entrySteps total : ℕ)
      (S : PayloadStack t lambda → List Bool),
      scalarSteps ≤ scalarBudget t lambda e z.val g.val l.val
        (positionEval (paddedEdgesEval edges) a vertex).val ∧
      routeSteps ≤ 2*((z.val * fixedQ t + g.val) * paddedEdgeBits e +
        paddedEdgeBits e + payloadBaseValue t lambda e l.val
          (positionEval (paddedEdgesEval edges) a vertex).val +
        fixedK t + paddedEdgeCount e)+10 ∧
      parameterSteps ≤ scalarSteps+routeSteps+1 ∧
      copySteps ≤ 2*tapeBitCount t (paddedEdgeBits e) lambda+2 ∧
      loadSteps ≤ copySteps+parameterSteps+1 ∧
      entrySteps ≤
        Paper2.YaoEntryComposition.selectorBudget t (paddedEdgeBits e) lambda bits z g +
        Paper2.YaoEntryComposition.payloadBudget t (paddedEdgeBits e) lambda bits l
          (positionEval (paddedEdgesEval edges) a vertex) +
        (6*paddedEdgeCount e + 3*paddedEdgeBits e + 6) ∧
      total ≤ loadSteps+entrySteps+1 ∧
      total ≤
        (2*tapeBitCount t (paddedEdgeBits e) lambda+2) +
        scalarBudget t lambda e z.val g.val l.val
          (positionEval (paddedEdgesEval edges) a vertex).val +
        (2*((z.val * fixedQ t + g.val) * paddedEdgeBits e +
          paddedEdgeBits e + payloadBaseValue t lambda e l.val
            (positionEval (paddedEdgesEval edges) a vertex).val +
          fixedK t + paddedEdgeCount e)+10) +
        (Paper2.YaoEntryComposition.selectorBudget t (paddedEdgeBits e) lambda bits z g +
          Paper2.YaoEntryComposition.payloadBudget t (paddedEdgeBits e) lambda bits l
            (positionEval (paddedEdgesEval edges) a vertex) +
          (6*paddedEdgeCount e + 3*paddedEdgeBits e + 6)) + 3 ∧
      let c0 := selectorInitial t lambda e z.val g.val l.val
        (positionEval (paddedEdgesEval edges) a vertex).val
      let S₀ : PayloadStack t lambda → List Bool :=
        Sum.elim c0.stk (fun _ => [])
      let loaded : InputStack t lambda → List Bool :=
        Sum.elim (routedFinal S bits.val) (fun _ => bits.val)
      let final := entryEndBank t lambda loaded
        (Paper2.YaoEntryComposition.entryFinal t lambda edges bits vertex z g a l).stk
      ((advance (fullEntryProgram t lambda))^[total])
        (⟨some (.inl (.inl .scan)),
          ((none,(loaderInitialControl t lambda,())),
            Paper2.YaoEntryComposition.initialControl),
          tapeRawBank S₀ bits.val⟩ :
          TM2.Cfg (fun _ : InputStack t lambda => Bool)
            (FullLabel t lambda) (FullControl t lambda)) =
        ⟨none,((none,(loaderInitialControl t lambda,())),
          Paper2.YaoEntryComposition.initialControl),final⟩ ∧
      final (entryEmbed t lambda 12) =
        [matrixFromTape t lambda edges
          (readTape t (paddedEdgeBits e) lambda bits)
          (vertex,z) (g,a,l)] ∧
      final (tapeSource t lambda) = bits.val := by
  let p := positionEval (paddedEdgesEval edges) a vertex
  obtain ⟨scalarSteps,routeSteps,parameterSteps,S,hscalar,hparameter,hroute,
    hparamRun,hbank⟩ :=
    physical_routed_entry_bank t lambda edges bits vertex z g a l
  let c0 := selectorInitial t lambda e z.val g.val l.val p.val
  let S₀ : PayloadStack t lambda → List Bool := Sum.elim c0.stk (fun _ => [])
  let R := routedFinal S bits.val
  let loaded : InputStack t lambda → List Bool := Sum.elim R (fun _ => bits.val)
  let final := entryEndBank t lambda loaded
    (Paper2.YaoEntryComposition.entryFinal t lambda edges bits vertex z g a l).stk
  have hparamRun' :
      ((advance (routedParameterProgram t lambda
        (fixedStageControl t lambda) (fixedSelectorControl t lambda)))^[parameterSteps])
        (⟨some (loaderStart t lambda),loaderInitialControl t lambda,
          Sum.elim S₀ (routedForeign bits.val)⟩ :
          TM2.Cfg (fun _ : RouteStack t lambda => Bool)
            (LoaderLabel t lambda) (LoaderControl t lambda)) =
        ⟨none,loaderInitialControl t lambda,R⟩ := by
    simpa only [c0,S₀,R,p,loaderStart,loaderInitialControl,
      frame_start_control_constant,selector_start_control_constant,
      routed_program_constant] using hparamRun
  obtain ⟨copySteps,loadSteps,hcopy,hload,hloaded⟩ :=
    loaded_parameters_from_run t lambda S₀ R bits.val parameterSteps hparamRun'
  have hcopy' : copySteps ≤ 2*tapeBitCount t (paddedEdgeBits e) lambda+2 := by
    simpa only [bits.property] using hcopy
  have hentryBank (i : Fin 13) :
      loaded (entryEmbed t lambda i) =
      (Paper2.YaoEntryComposition.entryInput t lambda edges bits vertex z g a l).stk i := by
    exact congrFun hbank i
  obtain ⟨entrySteps,hentry,hentered⟩ :=
    embedded_entry_after_bank t lambda edges bits vertex z g a l
      loaded hentryBank
  obtain ⟨total,htotal,hjoined⟩ := BitMachineRawSequence.runs
    (loadedParameterProgram t lambda) (embeddedEntryProgram t lambda)
    (.inl .scan) (.inl (.inr false))
    (none,(loaderInitialControl t lambda,()))
    (none,(loaderInitialControl t lambda,()))
    Paper2.YaoEntryComposition.initialControl
    Paper2.YaoEntryComposition.initialControl
    (tapeRawBank S₀ bits.val) loaded final loadSteps entrySteps
    (by simpa only [loadedParameterProgram,loaded] using hloaded)
    (by simpa only [final] using hentered)
  have hflat : total ≤
      (2*tapeBitCount t (paddedEdgeBits e) lambda+2) +
      scalarBudget t lambda e z.val g.val l.val p.val +
      (2*((z.val * fixedQ t + g.val) * paddedEdgeBits e +
        paddedEdgeBits e + payloadBaseValue t lambda e l.val p.val +
        fixedK t + paddedEdgeCount e)+10) +
      (Paper2.YaoEntryComposition.selectorBudget t (paddedEdgeBits e) lambda bits z g +
        Paper2.YaoEntryComposition.payloadBudget t (paddedEdgeBits e) lambda bits l p +
        (6*paddedEdgeCount e + 3*paddedEdgeBits e + 6)) + 3 := by
    dsimp only [p]
    omega
  refine ⟨scalarSteps,routeSteps,parameterSteps,copySteps,loadSteps,
    entrySteps,total,S,hscalar,hroute,hparameter,hcopy',hload,hentry,htotal,hflat,?_⟩
  dsimp only
  refine ⟨?_,?_,?_⟩
  · simpa only [fullEntryProgram,c0,S₀,loaded,final,
      BitMachineRawSequence.leftLabel] using hjoined
  · exact entry_end_at t lambda loaded
      (Paper2.YaoEntryComposition.entryFinal t lambda edges bits vertex z g a l).stk 12
  · rw [entry_end_raw_tape]
    rfl

#print axioms physical_full_entry_controller

end Paper2.YaoEntryControllerJoin
