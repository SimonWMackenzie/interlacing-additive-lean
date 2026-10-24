import CurrentAdditive.GaussStepBranchRun32

/-! The raw encoded Bank4 state enters the fixed Fin32 Gauss controller. -/

namespace CurrentAdditive.GaussStepParseRun32

noncomputable section

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open Turing BitMachineEncoding
open CurrentAdditive.GaussStepFields32

def raw {m k : Nat} (s : GaussControlTrace.State m k)
    (foreign : Stack → List Bool) : GaussParsedState32.Config :=
  GaussParsedState32.frame foreign
    (parserCfg (K := 4) (some (.scan 0)) none (fun _ => [])
      (GaussControlTrace.statePacket s) [] [])

def parsed {m k : Nat} (s : GaussControlTrace.State m k)
    (foreign : Stack → List Bool) : GaussParsedState32.Config :=
  GaussParsedState32.frame foreign
    (parserCfg none (some true) (GaussControlTrace.stateBank s) [] [] [])

theorem parse_entry {m k : Nat}
    (s : GaussControlTrace.State m k)
    (foreign : Stack → List Bool) (terminal : Bool) :
    ∃ t ≤ 9 * ((GaussControlTrace.statePacket s).length+1)+1,
      run t (BitMachineInline.cfg (Label.parse terminal) eParse
        (some (.afterParse terminal)) (raw s foreign)) =
      ⟨some (.afterParse terminal), eParse none,
        (parsed s foreign).stk⟩ := by
  obtain ⟨a,ha,hparse⟩ := GaussParsedState32.parse_state s foreign
  have hstep : GaussParsedState32.run 1 (parsed s foreign) =
      ⟨none, none, (parsed s foreign).stk⟩ := by
    rfl
  have hlocal : GaussParsedState32.run (a+1) (raw s foreign) =
      ⟨none, none, (parsed s foreign).stk⟩ := by
    change ((advance GaussParsedState32.program)^[a+1])
      (raw s foreign) = _
    rw [Function.iterate_succ_apply', ← GaussParsedState32.run]
    have hp : GaussParsedState32.run a (raw s foreign) =
        parsed s foreign := by simpa [raw,parsed] using hparse
    rw [hp]
    exact hstep
  obtain ⟨u,hu,hr⟩ :=
    GaussStepPhaseLift32.parse_lift terminal (raw s foreign) (a+1)
      (by rw [hlocal])
  refine ⟨u, by omega, ?_⟩
  simpa [BitMachineInline.cfg, hlocal] using hr

theorem parsed_fields {m k : Nat}
    (s : GaussControlTrace.State m k)
    (foreign : Stack → List Bool)
    (hblank : ∀ p : Fin 4,
      foreign (GaussBranchFields32.dest p) = []) :
    GaussBranchFields32.ParsedState s (parsed s foreign).stk := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [GaussControlTrace.stateBank] using
      GaussParsedState32.parsed_field s foreign 0
  · simpa [GaussControlTrace.stateBank] using
      GaussParsedState32.parsed_field s foreign 1
  · simpa [GaussControlTrace.stateBank] using
      GaussParsedState32.parsed_field s foreign 2
  · simpa [GaussControlTrace.stateBank] using
      GaussParsedState32.parsed_field s foreign 3
  · intro p
    have h := GaussParsedState32.parsed_ambient s foreign
      (GaussBranchFields32.dest p) (by fin_cases p <;> decide)
    exact (show (parsed s foreign).stk (GaussBranchFields32.dest p) =
      foreign (GaussBranchFields32.dest p) from h) |>.trans (hblank p)
  · change (parsed s foreign).stk
        (GaussParsedState32.locate (.inr (1 : Fin 3))) = []
    unfold parsed GaussParsedState32.frame
    simp [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg,
      BitMachineStackEmbedding.bank_at,
      parserCfg, contents]

theorem raw_terminal_fields {m k : Nat}
    (s : GaussControlTrace.State m k)
    (foreign : Stack → List Bool)
    (hblank : ∀ p : Fin 4,
      foreign (GaussBranchFields32.dest p) = []) :
    ∃ t ≤ 9*((GaussControlTrace.statePacket s).length+1)+1+1+
        (GaussBranchFields32.copyClock .halted
          (parsed s foreign).stk+4),
      run t (BitMachineInline.cfg (Label.parse true) eParse
        (some (.afterParse true)) (raw s foreign)) =
        ⟨some .afterBranch,eBranch ((),none),
          GaussStepBranchRun32.adjusted .halted
            (parsed s foreign).stk⟩ ∧
      GaussBranchFields32.preparedBank
        (run t (BitMachineInline.cfg (Label.parse true) eParse
          (some (.afterParse true)) (raw s foreign))).stk =
        GaussControlTrace.stateBank s := by
  let S := (parsed s foreign).stk
  obtain ⟨a,ha,hparse⟩ := parse_entry s foreign true
  have hnext : run 1 ⟨some (.afterParse true),eParse none,S⟩ =
      ⟨some (.branch (.copy .halted 0 .scan)),eBranch ((),none),S⟩ := by
    rfl
  obtain ⟨b,hb,hbranch,hbank⟩ :=
    GaussStepBranchRun32.halted_prepared s S
      (parsed_fields s foreign hblank)
  have hfull : run (a+1+b)
      (BitMachineInline.cfg (Label.parse true) eParse
        (some (.afterParse true)) (raw s foreign)) =
      ⟨some .afterBranch,eBranch ((),none),
        GaussStepBranchRun32.adjusted .halted S⟩ := by
    rw [show a+1+b = a+(1+b) by omega,
      run_add hparse (1+b), run_add hnext b]
    exact hbranch
  refine ⟨a+1+b, ?_, ?_, ?_⟩
  · change a+1+b ≤ 9*((GaussControlTrace.statePacket s).length+1)+1+1+
      (GaussBranchFields32.copyClock .halted S+4)
    omega
  · exact hfull
  · rw [hfull]
    exact hbank

#print axioms parse_entry
#print axioms parsed_fields
#print axioms raw_terminal_fields

end
end CurrentAdditive.GaussStepParseRun32
