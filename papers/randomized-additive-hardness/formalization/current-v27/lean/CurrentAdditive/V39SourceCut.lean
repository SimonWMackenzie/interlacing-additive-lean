import CurrentAdditive.V39SourceFrame
import Paper2.E6Cut

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

namespace CurrentAdditive.V39SourceFront
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
  {S : Type} [Fintype S] [DecidableEq S]
  (gPort kPort tPort : S) (hgk : gPort ≠ kPort) (hgt : gPort ≠ tPort) (hkt : kPort ≠ tPort)

/-- Only these bounded blocks reach the source compiler and later classifier. -/
def cutWord (K cutoff j : ℕ) (hcutoff : 1 ≤ cutoff) (w tape : List Bool) : List Bool :=
  let F := AEth4.routed4 K cutoff w
  let L := AEth5.L1 K cutoff w
  EncodedComplexity.pair
    (BitMachineBankCodec.encode (framedBank D B gPort kPort tPort hgk hgt hkt hcutoff
      (EncodedCNF.encode F) (tape.take L)))
    ((tape.take (2^j*L)).drop L)

def cutScale (K cutoff j : ℕ) (w : List Bool) : ℕ :=
  2*(AEth3.fOut (AEth4.routed4 K cutoff w)).length+1+2^j*AEth5.L1 K cutoff w

/-- Physical prefix cutting precedes every transfer of tape. The clock
mentions the routed formula and fixed cut request, never the raw tape. -/
theorem all_input_cut_framed (K cutoff j : ℕ) (hcutoff : 1 ≤ cutoff) :
    ∃ (M : BitMachine.Machine) (C E p : ℕ), ∀ w tape : List Bool,
      M.OutputsWithin (EncodedComplexity.pair w tape)
        (cutWord D B gPort kPort tPort hgk hgt hkt K cutoff j hcutoff w tape)
        (AEth5.twoCutTime K cutoff j w + 30*cutScale K cutoff j w+30+
          C*(cutScale K cutoff j w+1)^E*(1+2*p)) := by
  obtain ⟨MF,C,E,hF⟩ := all_input_framed D B gPort kPort tPort hgk hgt hkt hcutoff
  let Strip := Unit4Shell.PairMap.machine (Unit4Shell.PairMap.machine AEth3.Fst.machine)
  refine ⟨BitMachineComposition.composition (AEth5.twoCut K cutoff j)
    (BitMachineComposition.composition Strip (Unit4Shell.PairMap.machine MF)),C,E,MF.pushBound,?_⟩
  intro w tape
  let F := AEth4.routed4 K cutoff w
  let L := AEth5.L1 K cutoff w
  let a := tape.take L
  let b := (tape.take (2^j*L)).drop L
  let x := EncodedComplexity.pair (AEth3.fOut F) a
  let y := EncodedComplexity.pair (EncodedCNF.encode F) a
  let z := BitMachineBankCodec.encode
    (framedBank D B gPort kPort tPort hgk hgt hkt hcutoff (EncodedCNF.encode F) a)
  let R := cutScale K cutoff j w
  have hcut := AEth5.twoCut_outputs K cutoff j hcutoff w tape
  have hfst := AEth3.Fst.machine_outputs (EncodedCNF.encode F)
    (EncodedComplexity.pair (List.replicate (AEth.expLen F.variables) true) [])
  have hs1 := Unit4Shell.PairMap.machine_outputs (M:=AEth3.Fst.machine)
    (AEth3.fOut F) (EncodedCNF.encode F) a _ hfst
  have hs2 := Unit4Shell.PairMap.machine_outputs (M:=Unit4Shell.PairMap.machine AEth3.Fst.machine)
    x y b _ hs1
  have hf := hF (EncodedCNF.encode F) a
  have hp := Unit4Shell.PairMap.machine_outputs (M:=MF) y z b _ hf
  have hc := BitMachineComposition.composition_outputsWithin _ _ hcut
    (BitMachineComposition.composition_outputsWithin _ _ hs2 hp)
  apply BitMachine.outputsWithin_mono _ hc
  have hlF : (EncodedCNF.encode F).length ≤ (AEth3.fOut F).length := by
    rw [AEth3.fOut_length]; omega
  have hLa : a.length ≤ L := List.length_take_le _ _
  have hLb : b.length ≤ 2^j*L :=
    by
      dsimp only [b]; rw [List.length_drop]
      have := List.length_take_le (2^j*L) tape
      omega
  have hLj : L ≤ 2^j*L := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos j)
  have hxy : x.length ≤ R ∧ y.length ≤ R := by
    dsimp only [x,y,R,cutScale,F,L] at *
    simp only [EncodedComplexity.pair_length]
    omega
  have houter : (EncodedComplexity.pair x b).length ≤ 3*R := by
    simp only [EncodedComplexity.pair_length]
    dsimp only [R,cutScale,F,L] at *
    omega
  have hyouter : (EncodedComplexity.pair y b).length ≤ 3*R := by
    simp only [EncodedComplexity.pair_length]
    dsimp only [R,cutScale,F,L] at *
    omega
  have hpow : C*(y.length+1)^E ≤ C*(R+1)^E :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hz := BitMachine.output_length_bound MF hf
  change z.length ≤ y.length+C*(y.length+1)^E*MF.pushBound at hz
  have hz' : z.length ≤ R+C*(R+1)^E*MF.pushBound := by
    have := Nat.mul_le_mul_right MF.pushBound hpow
    omega
  dsimp only [R] at hxy houter hyouter hpow hz'
  simp only [EncodedComplexity.pair_length] at *
  dsimp only [x,y] at *
  dsimp only [cutScale] at *
  dsimp only [x,y,a,b,F,L] at *
  simp only [EncodedComplexity.pair_length] at *
  nlinarith

/-- The same effective length-only carrier covers every routed cut. -/
theorem cut_fits_carrier (K cutoff j : ℕ) (hcutoff : 1 ≤ cutoff) (w : List Bool) :
    2^j*AEth5.L1 K cutoff w ≤ AEth4.tapeCA (AEth4.phiLen cutoff) (7+j) w.length :=
  AEth5.twoCut_fit K cutoff j hcutoff w

/-- Exact independent segment law; this is a law of the physical cut of
uniform bits, without invoking any older sampler distribution. -/
theorem cut_blocks_law {I L s R j : ℕ} (hI : I ≤ L) (hs : L+s ≤ 2^j*L)
    (hR : 2^j*L ≤ R) (event : List Bool → List Bool → Prop) :
    (Unit4Shell.Definitions.uniformTape R).prob
      (fun t => event (((List.ofFn t).take L).take I)
        ((((List.ofFn t).take (2^j*L)).drop L).take s)) =
      ((Unit4Shell.Definitions.uniformTape I).prod (Unit4Shell.Definitions.uniformTape s)).prob
        (fun x => event (List.ofFn x.1) (List.ofFn x.2)) :=
  AEth5.blocks_law hI hs hR event

end
end CurrentAdditive.V39SourceFront
#print axioms CurrentAdditive.V39SourceFront.all_input_cut_framed
#print axioms CurrentAdditive.V39SourceFront.cut_blocks_law
