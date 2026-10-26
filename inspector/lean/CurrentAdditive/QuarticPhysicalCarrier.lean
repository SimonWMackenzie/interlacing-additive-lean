import CurrentAdditive.QuarticPairUniformBank
import CurrentAdditive.QuarticPrefixCarrier

/-! Turn a uniform pointwise v27 machine run into one R20 tape algorithm.
The extension proof uses injectivity of the literal selector bits. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.AEth2 Paper2.AEth4
open Paper2.CurrentAdditive.QuarticConstructor
open Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

def sourceSelector27
    (Dsrc : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Dsrc))
    (K N₁ : ℕ) (hN₁ : 1 ≤ N₁) (x : List Bool) :=
  let Φ := routedV K N₁ hN₁ x
  select27 (t10_vertices_pos Dsrc Bsrc Φ)
    (CanonicalEdgeTape.graphEdge (t10Graph Dsrc Bsrc Φ)
      (t10Graph_valid Dsrc Bsrc Φ))
    Bsrc.degreeBound (sourceGap Dsrc Bsrc) (kOf Φ.val.variables)

def sourceHeader27
    (Dsrc : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Dsrc))
    (K N₁ : ℕ) (hN₁ : 1 ≤ N₁) (x : List Bool)
    (a : (sourceSelector27 Dsrc Bsrc K N₁ hN₁ x).Tape) : List Bool :=
  let Φ := routedV K N₁ hN₁ x
  let g := t10Graph Dsrc Bsrc Φ
  let hg := t10Graph_valid Dsrc Bsrc Φ
  let hn := t10_vertices_pos Dsrc Bsrc Φ
  let edge := CanonicalEdgeTape.graphEdge g hg
  let k := kOf Φ.val.variables
  HeaderWordRun.headeredWord k
    (ASquare.squareInstance
      (selectedInstance27 hn edge Bsrc.degreeBound (sourceGap Dsrc Bsrc) k a))

def pointwisePhysical27
    (Dsrc : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Dsrc))
    (C : SelectedTape.Algorithm) (K N₁ : ℕ) (hN₁ : 1 ≤ N₁)
    (M : BitMachine.Machine) (T : List Bool → ℕ)
    (x tape : List Bool) : Prop :=
  let Φ := routedV K N₁ hN₁ x
  let o := sourceSelector27 Dsrc Bsrc K N₁ hN₁ x
  ∃ a : o.Tape,
    o.tapeBits a = tape.take o.inputBits ∧
    M.OutputsWithin (EncodedComplexity.pair x tape)
      (C.output (sourceHeader27 Dsrc Bsrc K N₁ hN₁ x a)
        ((tape.drop (Paper2.AEth3.cutLen Φ.val)).take
          (C.tapeLength (sourceHeader27 Dsrc Bsrc K N₁ hN₁ x a))))
      (T x)

def physicalCarrier27
    (Dsrc : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Dsrc))
    (C : SelectedTape.Algorithm) (K N₁ : ℕ) (hN₁ : 1 ≤ N₁)
    (M : BitMachine.Machine) (T : List Bool → ℕ)
    (hfit : ∀ x : List Bool,
      ∀ a : (sourceSelector27 Dsrc Bsrc K N₁ hN₁ x).Tape,
      (sourceSelector27 Dsrc Bsrc K N₁ hN₁ x).inputBits ≤
        tapeCA (phiLen N₁) (8 + C.cR) x.length ∧
      Paper2.AEth3.cutLen (routedV K N₁ hN₁ x).val +
        C.tapeLength (sourceHeader27 Dsrc Bsrc K N₁ hN₁ x a) ≤
          tapeCA (phiLen N₁) (8 + C.cR) x.length)
    (hpoint : ∀ x tape, tapeCA (phiLen N₁) (8 + C.cR) x.length ≤
      tape.length → pointwisePhysical27 Dsrc Bsrc C K N₁ hN₁ M T x tape) :
    ETape.Algorithm where
  tapeLen := tapeCA (phiLen N₁) (8 + C.cR)
  lenMachine := CAMachine (phiLen N₁) (8 + C.cR)
  lenTime := CAtime (phiLen N₁) (8 + C.cR)
  lenC := (BT + 30) * (phiLen N₁ + 1) ^ 2
  lenE := 2
  lenRuns := CAMachine_outputs (phiLen N₁) (8 + C.cR)
  lenPoly := CAtime_poly (phiLen N₁) (8 + C.cR)
  tapeSubexp := tapeCA_subexp (phiLen N₁) (8 + C.cR)
  machine := M
  time := T
  output := fun x tape =>
    ((M.run (T x) (M.init (EncodedComplexity.pair x tape))).stk M.output)
  runs := by
    intro x tape
    have hL : tapeCA (phiLen N₁) (8 + C.cR) x.length ≤
        (List.ofFn tape).length := by rw [List.length_ofFn]
    obtain ⟨a, hbits, hrun⟩ := hpoint x (List.ofFn tape) hL
    have hout := (BitMachine.outputsWithin_at_bound M hrun).2
    rw [hout]
    exact hrun
  extend := by
    intro x tape u htape
    let L := tapeCA (phiLen N₁) (8 + C.cR) x.length
    have hL : L ≤ tape.length := by rw [htape]
    have hLu : L ≤ (tape ++ u).length := by
      rw [List.length_append]
      omega
    obtain ⟨a₁, hb₁, hr₁⟩ := hpoint x tape hL
    obtain ⟨a₂, hb₂, hr₂⟩ := hpoint x (tape ++ u) hLu
    let o := sourceSelector27 Dsrc Bsrc K N₁ hN₁ x
    have hI : o.inputBits ≤ tape.length :=
      (hfit x a₁).1.trans hL
    have ha : a₂ = a₁ := by
      apply selected_tapeBits_injective27
      change (sourceSelector27 Dsrc Bsrc K N₁ hN₁ x).tapeBits a₂ =
        (sourceSelector27 Dsrc Bsrc K N₁ hN₁ x).tapeBits a₁
      rw [hb₂, hb₁, List.take_append_of_le_length hI]
    subst a₂
    let s := C.tapeLength (sourceHeader27 Dsrc Bsrc K N₁ hN₁ x a₁)
    let cut := Paper2.AEth3.cutLen (routedV K N₁ hN₁ x).val
    have hC : cut + s ≤ tape.length := (hfit x a₁).2.trans hL
    have hblock : ((tape ++ u).drop cut).take s =
        (tape.drop cut).take s := by
      rw [List.drop_append_of_le_length (by omega : cut ≤ tape.length),
        List.take_append_of_le_length (by rw [List.length_drop]; omega)]
    have hout := (BitMachine.outputsWithin_at_bound M hr₁).2
    show M.OutputsWithin (EncodedComplexity.pair x (tape ++ u))
      (((M.run (T x) (M.init (EncodedComplexity.pair x tape))).stk M.output))
      (T x)
    rw [hout]
    rw [hblock] at hr₂
    exact hr₂

#print axioms physicalCarrier27

end
end Paper2.CurrentAdditive.QuarticClassEndpoint
