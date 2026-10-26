import CurrentAdditive.GaussPivotSplitClock32
import CurrentAdditive.GaussPivotBranchForeign32

/-! Start with the actual raw Bank4 state and the pivot-search tag. The
fixed Fin32 field controller consumes both and emits the exact semantic
successor, provided its matrix bank already holds the physical rewrite. -/

namespace CurrentAdditive.GaussPivotRawClock32

noncomputable section

set_option maxHeartbeats 1000000

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.GaussStepFields32
open Turing

def rawPhaseBound {m k : Nat} (s : GaussControlTrace.State m k)
    (foreign : Stack → List Bool) : Nat :=
  9*((GaussControlTrace.statePacket s).length+1)+1+9+
    (GaussBranchFields32.copyClock .pivot
      (GaussStepTagRun32.afterActive
        (GaussStepParseRun32.parsed s foreign).stk true)+4)

def clock {m k : Nat} (s : GaussControlTrace.State m k)
    (foreign : Stack → List Bool) (hr : s.r < m) (hc : s.c < k)
    (charge : Nat) : Nat :=
  let p : Fin m × Fin k := (⟨s.r,hr⟩,⟨s.c,hc⟩)
  rawPhaseBound s foreign + 1 +
  GaussPivotSplitClock32.clock (GaussControlTrace.step s).B
    (s.c+1) s.pivots p
    (charge + GaussPivotClockGrowth32.pushConstant *
      (rawPhaseBound s foreign+1))

def inputBankCharge {m k : Nat} (s : GaussControlTrace.State m k)
    (foreign : Stack → List Bool) : Nat :=
  ∑ j : Stack, ((GaussStepParseRun32.raw s foreign).stk j).length

private theorem parsed_empty29 {m k : Nat}
    (s : GaussControlTrace.State m k) (foreign : Stack → List Bool) :
    (GaussStepParseRun32.parsed s foreign).stk 29 = [] := by
  change (BitMachineStackEmbedding.bank GaussParsedState32.locate foreign
    (BitMachineBankCodec.parserCfg none (some true)
      (GaussControlTrace.stateBank s) [] [] []).stk)
    (GaussParsedState32.locate (.inr (2 : Fin 3))) = []
  rw [BitMachineStackEmbedding.bank_at]
  rfl

private theorem parsed_empty30 {m k : Nat}
    (s : GaussControlTrace.State m k) (foreign : Stack → List Bool) :
    (GaussStepParseRun32.parsed s foreign).stk 30 = [] := by
  change (BitMachineStackEmbedding.bank GaussParsedState32.locate foreign
    (BitMachineBankCodec.parserCfg none (some true)
      (GaussControlTrace.stateBank s) [] [] []).stk)
    (GaussParsedState32.locate (.inr (0 : Fin 3))) = []
  rw [BitMachineStackEmbedding.bank_at]
  rfl

private theorem parsed_foreign {m k : Nat}
    (s : GaussControlTrace.State m k) (foreign : Stack → List Bool)
    (j : Stack)
    (hj : j ≠ 16 ∧ j ≠ 17 ∧ j ≠ 18 ∧ j ≠ 19 ∧
      j ≠ 29 ∧ j ≠ 30 ∧ j ≠ 31) :
    (GaussStepParseRun32.parsed s foreign).stk j = foreign j :=
  GaussParsedState32.parsed_ambient s foreign j hj

theorem raw_pivot_to_packet_bound {m k : Nat}
    (s : GaussControlTrace.State m k)
    (hr : s.r < m) (hc : s.c < k)
    (pivot : Fin m)
    (hp : CurrentAdditive.SequentialTotality.pivotTyped
      s.B s.r ⟨s.c,hc⟩ = some pivot)
    (hcount : s.r = s.pivots.length)
    (foreign : Stack → List Bool)
    (hblank : ∀ q : Fin 4,
      foreign (GaussBranchFields32.dest q) = [])
    (htag : foreign 20 = [true])
    (h22 : foreign 22 = GaussPhysical.encodeTypedMatrix
      (GaussControlTrace.step s).B)
    (h25 : foreign 25 = [])
    (h23 : foreign 23 = []) (h24 : foreign 24 = [])
    (h26 : foreign 26 = []) (h27 : foreign 27 = [])
    (h28 : foreign 28 = [])
    (hempty : ∀ j : Fin
      (SourceListMachineWriter.framingMachine true).stackCount,
      foreign (GaussPivotFraming32.locate j) = [])
    (charge : Nat)
    (hcharge : ∀ j : Stack,
      ((GaussStepParseRun32.raw s foreign).stk j).length ≤ charge) :
    ∃ t ≤ clock s foreign hr hc charge,
      (run t (BitMachineInline.cfg (Label.parse false) eParse
        (some (.afterParse false))
        (GaussStepParseRun32.raw s foreign))).l = some .done ∧
      (run t (BitMachineInline.cfg (Label.parse false) eParse
        (some (.afterParse false))
        (GaussStepParseRun32.raw s foreign))).stk 14 =
        GaussControlTrace.statePacket (GaussControlTrace.step s) := by
  let S := (GaussStepParseRun32.parsed s foreign).stk
  let T := GaussStepTagRun32.afterActive S true
  let W := GaussStepBranchRun32.adjusted .pivot T
  let start : Config := BitMachineInline.cfg (Label.parse false) eParse
    (some (.afterParse false)) (GaussStepParseRun32.raw s foreign)
  obtain ⟨a,ha,hrun,hfields⟩ :=
    GaussStepActiveRun32.raw_pivot_counters s
      (GaussControlTrace.step s).B foreign hblank htag h22
  have hrunA : run a start =
      ⟨some .afterBranch,eBranch ((),none),W⟩ := hrun
  have ha' : a ≤ rawPhaseBound s foreign := by
    simpa [rawPhaseBound] using ha
  simp only [hrun] at hfields
  have hW4 : W 4 = GaussPhysical.encodeTypedMatrix
      (GaussControlTrace.step s).B := by
    exact hfields.1
  have hW5 : W 5 = List.replicate (s.r+1) true := by
    exact hfields.2.1
  have hW6 : W 6 = List.replicate (s.c+1) true := by
    exact hfields.2.2
  have hT25 : T 25 = [true] := by
    change Function.update (GaussStepTagRun32.tagged S true) 20 [] 25 = _
    rw [Function.update_of_ne (by decide : (25 : Stack) ≠ 20)]
    have ht := SourceClausePreservingBroadcast.target_written
      (20 : Stack) 31 [25]
      (by decide) (by decide) (by decide)
      [true] S 25 (by simp)
    change SourceClausePreservingBroadcast.result 20 31 [25]
      [true] S 25 = _
    have hS25 : S 25 = [] :=
      (parsed_foreign s foreign 25 (by decide)).trans h25
    rw [ht,hS25]
    rfl
  have hW25 : W 25 = [true] :=
    (GaussPivotBranchForeign32.adjusted_foreign T 25
      (by decide) (by decide)).trans hT25
  let U := Function.update W 25 []
  have hnext : run 1
      ⟨some .afterBranch,eBranch ((),none),W⟩ =
      ⟨some (.split (.copy .scan)),
        eSplit (((),none),(none,none)),U⟩ := by
    simp [run,program,advance,Turing.TM2.step,
      Turing.TM2.stepAux,hW25,U]
  have hprefixRun : run (a+1) start =
      ⟨some (.split (.copy .scan)),
        eSplit (((),none),(none,none)),U⟩ := by
    rw [run_add hrunA 1]
    exact hnext
  have hchargeU : ∀ j : Stack,
      (U j).length ≤ charge +
        GaussPivotClockGrowth32.pushConstant *
          (rawPhaseBound s foreign+1) := by
    intro j
    have hg := GaussPivotClockGrowth32.bank_growth_from_charge
      start (a+1) charge (by simpa [start] using hcharge) j
    rw [hprefixRun] at hg
    have hm := Nat.mul_le_mul_left
      GaussPivotClockGrowth32.pushConstant
      (show a+1 ≤ rawPhaseBound s foreign+1 by omega)
    exact hg.trans (Nat.add_le_add_left hm charge)
  have hWforeign (j : Stack) (hj : 8 ≤ j.val)
      (hj31 : j ≠ 31)
      (hjparse : j ≠ 16 ∧ j ≠ 17 ∧ j ≠ 18 ∧ j ≠ 19 ∧
        j ≠ 29 ∧ j ≠ 30 ∧ j ≠ 31)
      (hj20 : j ≠ 20) (hj25 : j ≠ 25) :
      W j = foreign j := by
    calc
      W j = T j := GaussPivotBranchForeign32.adjusted_foreign T j hj hj31
      _ = S j := GaussStepTagRun32.afterActive_preserves S true j
        hj20 hj25 hj31
      _ = foreign j := parsed_foreign s foreign j hjparse
  have hUother (j : Stack) (hj : j ≠ 25) : U j = W j :=
    by simp [U,hj]
  let p : Fin m × Fin k := (⟨s.r,hr⟩,⟨s.c,hc⟩)
  have h4U : U 4 = GaussPhysical.encodeTypedMatrix
      (GaussControlTrace.step s).B := by
    rw [hUother 4 (by decide)]
    exact hW4
  have h5U : U 5 = List.replicate
      (s.pivots ++ [p]).length true := by
    rw [hUother 5 (by decide),hW5]
    simp [p,hcount]
  have h6U : U 6 = List.replicate (s.c+1) true := by
    rw [hUother 6 (by decide)]
    exact hW6
  have hTparsed : GaussBranchFields32.ParsedState s T :=
    GaussStepTagRun32.afterActive_parsed s S true
      (GaussStepParseRun32.parsed_fields s foreign hblank)
  have h17U : U 17 = List.replicate p.1.val true := by
    rw [hUother 17 (by decide)]
    change GaussStepBranchRun32.adjusted .pivot T 17 = _
    rw [GaussPivotBranchForeign32.adjusted_foreign T 17
      (by decide) (by decide)]
    exact hTparsed.row
  have h18U : U 18 = List.replicate p.2.val true := by
    rw [hUother 18 (by decide)]
    change GaussStepBranchRun32.adjusted .pivot T 18 = _
    rw [GaussPivotBranchForeign32.adjusted_foreign T 18
      (by decide) (by decide)]
    exact hTparsed.column
  have h19U : U 19 = GaussControlTrace.pivotsPacket s.pivots := by
    rw [hUother 19 (by decide)]
    change GaussStepBranchRun32.adjusted .pivot T 19 = _
    rw [GaussPivotBranchForeign32.adjusted_foreign T 19
      (by decide) (by decide)]
    exact hTparsed.pivots
  have h23U : U 23 = [] := by
    rw [hUother 23 (by decide),
      hWforeign 23 (by decide) (by decide)
        (by decide) (by decide) (by decide)]
    exact h23
  have h24U : U 24 = [] := by
    rw [hUother 24 (by decide),
      hWforeign 24 (by decide) (by decide)
        (by decide) (by decide) (by decide)]
    exact h24
  have h25U : U 25 = [] := by simp [U]
  have h26U : U 26 = [] := by
    rw [hUother 26 (by decide),
      hWforeign 26 (by decide) (by decide)
        (by decide) (by decide) (by decide)]
    exact h26
  have h27U : U 27 = [] := by
    rw [hUother 27 (by decide),
      hWforeign 27 (by decide) (by decide)
        (by decide) (by decide) (by decide)]
    exact h27
  have h28U : U 28 = [] := by
    rw [hUother 28 (by decide),
      hWforeign 28 (by decide) (by decide)
        (by decide) (by decide) (by decide)]
    exact h28
  have h29U : U 29 = [] := by
    rw [hUother 29 (by decide)]
    change GaussStepBranchRun32.adjusted .pivot T 29 = _
    rw [GaussPivotBranchForeign32.adjusted_foreign T 29
        (by decide) (by decide)]
    change GaussStepTagRun32.afterActive S true 29 = _
    rw [GaussStepTagRun32.afterActive_preserves S true 29
      (by decide) (by decide) (by decide)]
    exact parsed_empty29 s foreign
  have h30U : U 30 = [] := by
    rw [hUother 30 (by decide)]
    change GaussStepBranchRun32.adjusted .pivot T 30 = _
    rw [GaussPivotBranchForeign32.adjusted_foreign T 30
        (by decide) (by decide)]
    change GaussStepTagRun32.afterActive S true 30 = _
    rw [GaussStepTagRun32.afterActive_preserves S true 30
      (by decide) (by decide) (by decide)]
    exact parsed_empty30 s foreign
  have h31U : U 31 = [] := by
    rw [hUother 31 (by decide)]
    exact GaussPivotBranchForeign32.adjusted_scratch T
  have hemptyU : ∀ j : Fin
      (SourceListMachineWriter.framingMachine true).stackCount,
      U (GaussPivotFraming32.locate j) = [] := by
    intro j
    let q := GaussPivotFraming32.locate j
    rw [hUother q (by fin_cases j <;> decide),
      hWforeign q (by fin_cases j <;> decide)
        (by fin_cases j <;> decide)
        (by fin_cases j <;> decide)
        (by fin_cases j <;> decide)
        (by fin_cases j <;> decide)]
    exact hempty j
  obtain ⟨b,hb,hend,hpacket⟩ :=
    GaussPivotSplitClock32.split_to_packet_bound
      (GaussControlTrace.step s).B (s.c+1) s.pivots p U
      h4U h5U h6U h17U h18U h19U h23U h24U
      h25U h26U h27U h28U h29U h30U h31U hemptyU
      (charge + GaussPivotClockGrowth32.pushConstant *
        (rawPhaseBound s foreign+1)) hchargeU
  have htarget :
      (⟨(GaussControlTrace.step s).B,
        (s.pivots ++ [p]).length,s.c+1,s.pivots ++ [p]⟩ :
        GaussControlTrace.State m k) = GaussControlTrace.step s := by
    simp only [GaussControlTrace.step,hr,hc,hp]
    simp [p,hcount]
  rw [htarget] at hpacket
  refine ⟨a+1+b, ?_, ?_, ?_⟩
  · change a+1+b ≤ rawPhaseBound s foreign+1+
      GaussPivotSplitClock32.clock (GaussControlTrace.step s).B
        (s.c+1) s.pivots p
        (charge + GaussPivotClockGrowth32.pushConstant *
          (rawPhaseBound s foreign+1))
    omega
  · rw [show a+1+b = a+(1+b) by omega,
      run_add hrunA (1+b),run_add hnext b]
    exact hend
  · rw [show a+1+b = a+(1+b) by omega,
      run_add hrunA (1+b),run_add hnext b]
    exact hpacket

#print axioms raw_pivot_to_packet_bound

end
end CurrentAdditive.GaussPivotRawClock32
