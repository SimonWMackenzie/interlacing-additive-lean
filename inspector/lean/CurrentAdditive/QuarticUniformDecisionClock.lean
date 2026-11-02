import CurrentAdditive.QuarticAnyPhysicalOutput

/-! One decision-time cap independent of the selected tape values. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open EthInapproximability.CurrentPaper

noncomputable def uniformAtoms27
    (C : Paper2.SelectedTape.Algorithm) (Φ : EncodedCNF.Formula)
    (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph)
    (hg : g.Valid) (hn : 0 < g.vertices)
    (Ttwo Tcut Tprint Y : ℕ) : ℕ :=
  let k := Paper2.Unit4Shell.Asymptotics.kOf Φ.variables
  let edge := CanonicalEdgeTape.graphEdge g hg
  (EncodedCNF.encode Φ).length + (Paper2.AEth3.fOut Φ).length +
    Paper2.AEth3.cutLen Φ + 2 ^ C.cR * Paper2.AEth3.cutLen Φ +
    inputBankLength27 Δ γ g hg hn k +
    squareEncodedLength27 hn edge Δ γ k +
    headerLength27 hn edge Δ γ k +
    Ttwo + Tcut + Tprint + Y +
    squareHeaderClock27 hn edge Δ γ Φ

theorem sourceDecisionClock_uniform27
    (C : Paper2.SelectedTape.Algorithm) (Φ : EncodedCNF.Formula)
    (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph)
    (hg : g.Valid) (hn : 0 < g.vertices)
    (t : (select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ
      (Paper2.Unit4Shell.Asymptotics.kOf Φ.variables)).Tape)
    (tape : List Bool) (Ttwo Tcut Tprint Y : ℕ) :
    let k := Paper2.Unit4Shell.Asymptotics.kOf Φ.variables
    let edge := CanonicalEdgeTape.graphEdge g hg
    let raw := tape.take (Paper2.AEth3.cutLen Φ)
    let block := (tape.take (2 ^ C.cR * Paper2.AEth3.cutLen Φ)).drop
      (Paper2.AEth3.cutLen Φ)
    let bank := BitMachineBankCodec.encode
      (QuarticDispatchSpec.inputBank27 Δ γ g hg hn k t)
    let i := selectedInstance27 hn edge Δ γ k t
    let w := Paper2.HeaderWordRun.headeredWord k
      (Paper2.ASquare.squareInstance i)
    let Z := uniformAtoms27 C Φ Δ γ g hg hn Ttwo Tcut Tprint Y
    let Ttail := Tcut + 2 * (EncodedComplexity.pair
      (EncodedCNF.encode Φ) bank).length + 2 +
      headerClock27 Φ bank i
        ((EncodedCNF.encode Φ).length + 2 + 2 * bank.length + 2 + Tprint)
    sourceDecisionClock27 C (EncodedCNF.encode Φ) (Paper2.AEth3.fOut Φ)
      raw block w Ttwo (sourceCoreClock27 Φ raw Ttail) Y ≤
      5000 * (Z + 1) + Paper2.AEth5.clsTime C Z Z := by
  intro k edge raw block bank i w Z Ttail
  have hbank := inputBank_encoded_length27 Δ γ g hg hn k t
  have hsquare := squareEncodedLength_eq27 hn edge Δ γ k t
  have hword := headerWord_length27 hn edge Δ γ k t
  have hheader := squareHeaderClock_eq27 hn edge Δ γ Φ t
  change bank.length = inputBankLength27 Δ γ g hg hn k at hbank
  change (EncodedCommunication.encodeInstance
    (Paper2.ASquare.squareInstance i)).length =
      squareEncodedLength27 hn edge Δ γ k at hsquare
  change w.length = headerLength27 hn edge Δ γ k at hword
  change Paper2.AEth4.KHeader.clock Φ
    (Paper2.ASquare.squareInstance i) =
      squareHeaderClock27 hn edge Δ γ Φ at hheader
  simp only [k, edge] at hbank hsquare hword hheader
  have hraw : raw.length ≤ Paper2.AEth3.cutLen Φ :=
    List.length_take_le _ _
  have hblock : block.length ≤ 2 ^ C.cR * Paper2.AEth3.cutLen Φ := by
    have htake := List.length_take_le
      (2 ^ C.cR * Paper2.AEth3.cutLen Φ) tape
    dsimp [block]
    rw [List.length_drop]
    omega
  apply sourceDecisionClock27_le C Φ raw block bank w i Ttwo Tcut Tprint Y Z
  all_goals dsimp only [Z, uniformAtoms27, k, edge]
  all_goals omega

#print axioms sourceDecisionClock_uniform27

end Paper2.CurrentAdditive.QuarticClassEndpoint
