import Paper2.YaoAllScalarBanks
import EthInapproximability.CurrentPaper.BitMachineSubroutine

/-! Frame the actual one-program scalar chain with four basic unary label
coordinates. They enter as disjoint physical stacks and survive unchanged
while the scalar machine computes `b,H,S`. -/

namespace Paper2.YaoParameterBank

set_option maxRecDepth 8192

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineComposition
open EthInapproximability.CurrentPaper.BitMachineSubroutine
open Paper2.YaoParameterLoader
open Paper2.YaoLowerBound
open Paper2.YaoLookup

noncomputable abbrev ScalarA := logPowerMachine
noncomputable abbrev ScalarB (t lambda : ℕ) := selectorCountMachine t lambda
abbrev BaseStack (t lambda : ℕ) := BitMachineComposition.Stack ScalarA (ScalarB t lambda)
abbrev BaseLabel (t lambda : ℕ) := BitMachineComposition.Label ScalarA (ScalarB t lambda)
abbrev BaseControl (t lambda : ℕ) := BitMachineComposition.Control ScalarA (ScalarB t lambda)
abbrev FrameStack (t lambda : ℕ) := BaseStack t lambda ⊕ Fin 4
abbrev FrameLabel (t lambda : ℕ) := BaseLabel t lambda ⊕ Unit
abbrev FrameControl (t lambda : ℕ) := BaseControl t lambda × Unit
abbrev FrameConfig (t lambda : ℕ) :=
  TM2.Cfg (fun _ : FrameStack t lambda => Bool)
    (FrameLabel t lambda) (FrameControl t lambda)

noncomputable def frameProgram (t lambda : ℕ) :
    FrameLabel t lambda → TM2.Stmt (fun _ : FrameStack t lambda => Bool)
      (FrameLabel t lambda) (FrameControl t lambda)
  | .inl l => liftStmt none (program ScalarA (ScalarB t lambda) l)
  | .inr () => .halt

def labelBanks (z g ell p : ℕ) : Fin 4 → List Bool :=
  ![List.replicate z true, List.replicate g true,
    List.replicate ell true, List.replicate p true]

noncomputable def frameStart (t lambda e z g ell p : ℕ) : FrameConfig t lambda :=
  liftCfg none () (labelBanks z g ell p)
    (rawInit (.inl ScalarA.input) (.inl (ScalarA.start))
      (ScalarA.initial,(ScalarB t lambda).initial,none)
      (List.replicate e true))

noncomputable def frameRun (t lambda n : ℕ) (c : FrameConfig t lambda) : FrameConfig t lambda :=
  ((advance (frameProgram t lambda))^[n]) c

theorem framed_four_banks (t lambda e z g ell p : ℕ) :
    ∃ (a b steps : ℕ),
      a ≤ 2*e+2 + (UnaryBinaryEncoding.coefficient+6)*(e+1)^2 +
        2*paddedEdgeBits e+2 + 16*paddedEdgeCount e ∧
      b ≤ 1 + MatrixAddressMachine.exactTime (paddedEdgeCount e)
        (fixedWidth t) (fixedTail t lambda) ∧
      steps ≤ a + 2*paddedEdgeCount e+2+b ∧
      let base := ((advance (program ScalarA (ScalarB t lambda)))^[
        a + 2*paddedEdgeCount e+2+b])
          (rawInit (.inl ScalarA.input) (.inl ScalarA.start)
            (ScalarA.initial,(ScalarB t lambda).initial,none)
            (List.replicate e true))
      let final := frameRun t lambda steps (frameStart t lambda e z g ell p)
      final = liftCfg none () (labelBanks z g ell p) base ∧
      final.l = none ∧
      final.stk (.inl (.inl edgeCell)) = List.replicate e true ∧
      final.stk (.inl (.inl bitsCell)) =
        List.replicate (paddedEdgeBits e) true ∧
      final.stk (.inl (.inr (.inl (ScalarB t lambda).input))) =
        List.replicate (paddedEdgeCount e) true ∧
      final.stk (.inl (.inr (.inl (ScalarB t lambda).output))) =
        List.replicate (selectorCount t (paddedEdgeBits e) lambda) true ∧
      (∀ j : Fin 4, final.stk (.inr j) = (labelBanks z g ell p) j) := by
  obtain ⟨a,b,ha,hb,hrun,hhalt,hE,hBits,hH,hS⟩ :=
    edge_to_count_four_banks t e lambda
  let base := ((advance (program ScalarA (ScalarB t lambda)))^[
      a + 2*paddedEdgeCount e+2+b])
    (rawInit (.inl ScalarA.input) (.inl ScalarA.start)
      (ScalarA.initial,(ScalarB t lambda).initial,none)
      (List.replicate e true))
  have hbase : base.l = none := hhalt
  obtain ⟨steps,hsteps,hframe⟩ := lift_outputs
    (program ScalarA (ScalarB t lambda))
    (frameProgram t lambda) none (by intro l; rfl)
    () (labelBanks z g ell p)
    (rawInit (.inl ScalarA.input) (.inl ScalarA.start)
      (ScalarA.initial,(ScalarB t lambda).initial,none)
      (List.replicate e true))
    (a + 2*paddedEdgeCount e+2+b) hbase
  have hframe' : frameRun t lambda steps (frameStart t lambda e z g ell p) =
      liftCfg none () (labelBanks z g ell p) base := by
    simpa only [frameRun, frameStart] using hframe
  refine ⟨a,b,steps,ha,hb,hsteps,?_⟩
  dsimp only
  refine ⟨hframe', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hframe']
    simp [liftCfg, hbase]
  · rw [hframe']
    simpa only [liftCfg, Sum.elim_inl] using hE
  · rw [hframe']
    simpa only [liftCfg, Sum.elim_inl] using hBits
  · rw [hframe']
    simpa only [liftCfg, Sum.elim_inl] using hH
  · rw [hframe']
    simpa only [liftCfg, Sum.elim_inl] using hS
  · intro j
    rw [hframe']
    rfl

#print axioms framed_four_banks

end Paper2.YaoParameterBank
