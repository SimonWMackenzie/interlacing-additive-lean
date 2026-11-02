import Paper2.E6Cls
import Paper2.E6Size
-- root successor copy (30 September 2026, for the R22 batch): the header line and the paragraph describing `decAlg`/`decAlg_output`, which are declared in E6Join (readback:a-eth-6 defect D3) corrected; no other change.
-- a-eth-owner-6 copy of the UNCHECKED, unpinned a-eth-owner-5/E5Dec.lean (SHA-256 53dbb3210cc8c0ca38479b17947265caff2ace3149ce9c5d2b787e125ee2a013), re-checked here: import lines renamed E5Cls/E5Size -> E6Cls/E6Size; the ETape-dependent tail (`decAlg`, `decAlg_output`, lines 239-281) moved to E6Join; nothing else changed.

/-!
# Paper A (lock v12), lane `owner:a-eth-6` (re-checked copy of the a-eth-owner-5 segment-4 draft): the composite growing-gap decider machine

ONE fixed machine `decMachine D B C K N₁` =
`twoCut K N₁ C.cR ; PairMap (PairMap Fst ; hdTail) ; clsStage C`, where `hdTail` is the part of the
a-eth-owner-4 header machine after its front cut (`Pack ; PairMap (MF ; GS) ; Swap ; PairConcat ; KHeader`).
On EVERY word `w` and every tape `t` with `2^cR · L1 ≤ |t|` (for `N₁` beyond one cutoff and `2 ≤ K N₁`) it prints
`C.output (hwOf D B Φ' t') ((t.drop L1).take (C.tapeLength (hwOf D B Φ' t')))`, where `Φ' = routedV K N₁ hN₁ w`,
`L1 = cutLen Φ'`, and `t'` is the typed selected tape whose bits are `t.take inputBits` (`dec_outputs_all`), within
the explicit clock `decTime` that never mentions the tape.

The R20 carrier `ETape.Algorithm` built on this machine (`decAlg`, with tape `tapeCA (phiLen N₁) (7 + C.cR)`, the
length machine `CAMachine`, `lenPoly` = `CAtime_poly`, `tapeSubexp` = `tapeCA_subexp`, the clock `decTime`, and the
output DEFINED as what the machine prints at its clock) and its output identity `decAlg_output` are declared in
`E6Join`, which imports this module. This module imports NO `ETape`.

No ledger row is closed. Nothing here is admitted.
-/

noncomputable section

namespace Paper2.AEth5

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open Paper2.AEth4
open Paper2.AEth3 (MF CF EF GS cut0 inputBits_fit cutLen cutLen_eq cutLen_ge fOut)

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- The header machine after its front cut (a-eth-owner-4 `hdMachine4` minus `frontCut4`). -/
def hdTail : BitMachine.Machine :=
  BitMachineComposition.composition Pack.machine
    (BitMachineComposition.composition
      (Paper2.Unit4Shell.PairMap.machine (BitMachineComposition.composition (MF D B) (GS D B)))
      (BitMachineComposition.composition Paper2.Unit4Shell.KofLoops.Swap.machine
        (BitMachineComposition.composition PairConcat.machine KHeader.machine)))

/-- The tail clock (the a-eth-owner-4 `hdTime4` without its front-cut part). -/
def tailTime (Φ : ValidFormula) : ℕ :=
  let eL := (EncodedCNF.encode Φ.val).length
  let XL := 2 * eL + 1 + cutLen Φ.val
  let ob := obLen D B Φ
  8 * (XL + 2) + 2 * (2 * XL + 4 * eL + 4) + 2 +
    ((2 * XL + mgTime D B Φ + 2 * ob + 6) + 2 * (2 * ob + 4 * eL + 4) + 2 +
      (3 * (2 * ob + 4 * eL + 5) + 2 * (2 * ob + 4 * eL + 4) + 2 +
        (3 * (2 * ob + 4 * eL + 5) + 2 * (2 * eL + 1 + ob) + 2 + khTime D B Φ)))

/-- **The header tail on the reduction block.** -/
theorem tail_outputs (Φ : ValidFormula) (hk : 1 ≤ kOf Φ.val.variables)
    (hN : cut0 D B ≤ Φ.val.variables) (c : List Bool) (hcl : c.length ≤ cutLen Φ.val)
    (hIc : (Sel D B Φ).inputBits ≤ c.length) :
    ∃ t' : (Sel D B Φ).Tape, (Sel D B Φ).tapeBits t' = c.take (Sel D B Φ).inputBits ∧
      (hdTail D B).OutputsWithin (EncodedComplexity.pair (EncodedCNF.encode Φ.val) c)
        (hwOf D B Φ t') (tailTime D B Φ) := by
  obtain ⟨t', ht', hmg⟩ := mg_outputs D B Φ hk hN c hcl hIc
  refine ⟨t', ht', ?_⟩
  set e := EncodedCNF.encode Φ.val with he
  set ob := EncodedSelectedOutput.outputBits (t10_vertices_pos D B Φ)
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    B.degreeBound (sourceGap D B) (kOf Φ.val.variables) t' with hob
  set i := EncodedSelectedOutput.selectedInstance (t10_vertices_pos D B Φ)
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    B.degreeBound (sourceGap D B) (kOf Φ.val.variables) t' with hi
  have hobi : ob = EncodedCommunication.encodeInstance i := rfl
  have h2 := Pack.outputs e c
  have h3 := Paper2.Unit4Shell.PairMap.machine_outputs
    (M := BitMachineComposition.composition (MF D B) (GS D B)) (EncodedComplexity.pair e c) ob
    (EncodedComplexity.pair (EncodedCommunication.field e) []) _ hmg
  have h4 := Paper2.Unit4Shell.KofLoops.Swap.machine_outputs ob (EncodedCommunication.field e) []
  have h5 := PairConcat.outputs
    (EncodedComplexity.pair (EncodedCommunication.field e) (EncodedComplexity.pair ob []))
  rw [PairConcat.concat_pair] at h5
  have h6 := KHeader.machine_outputs Φ.val hk i
  rw [← hobi, khTime_eq D B Φ t'] at h6
  have hfe : EncodedCommunication.field e ++ ob = EncodedComplexity.pair e ob := rfl
  rw [hfe] at h5
  have hC := BitMachineComposition.composition_outputsWithin _ _ h2
    (BitMachineComposition.composition_outputsWithin _ _ h3
      (BitMachineComposition.composition_outputsWithin _ _ h4
        (BitMachineComposition.composition_outputsWithin _ _ h5 h6)))
  refine BitMachine.outputsWithin_mono _ hC ?_
  have hobl : ob.length = obLen D B Φ := outputBits_length D B Φ t'
  simp only [tailTime, EncodedComplexity.pair_length, EncodedCommunication.field_length,
    List.length_nil, hobl]
  rw [← he]
  omega

/-- The first-component machine: project `fOut Φ'` to the formula word, then the header tail. -/
def M1 : BitMachine.Machine :=
  BitMachineComposition.composition (Paper2.Unit4Shell.PairMap.machine Paper2.AEth3.Fst.machine)
    (hdTail D B)

/-- The tape-independent length of the printed header word. -/
def hwLen (Φ : ValidFormula) : ℕ :=
  (EncodedCommunication.natField (2 * (Sel D B Φ).budget + kOf Φ.val.variables)).length +
    ((EncodedCommunication.natField (Sel D B Φ).rows).length +
      (EncodedCommunication.natField (Sel D B Φ).cols).length + (Sel D B Φ).rows * (Sel D B Φ).cols)

theorem hw_length_eq (Φ : ValidFormula) (t' : (Sel D B Φ).Tape) :
    (hwOf D B Φ t').length = hwLen D B Φ := by
  have hT := ((Sel D B Φ).table t').length
  unfold hwOf hwLen
  simp only [Paper2.HeaderWordRun.headeredWord, Paper2.HeaderWordRun.matrix,
    EncodedSelectedOutput.selectedInstance, EncodedSelectedOutput.instanceOf,
    AFront.Projection.matrixWord, List.length_append]
  rw [hT]

/-- THE fixed composite decision machine. -/
def decMachine (C : Paper2.SelectedTape.Algorithm) (K N₁ : ℕ) : BitMachine.Machine :=
  BitMachineComposition.composition (twoCut K N₁ C.cR)
    (BitMachineComposition.composition (Paper2.Unit4Shell.PairMap.machine (M1 D B)) (clsStage C))

/-- The composite clock, in `|w|` and the routed formula only (never in the tape). -/
def decTime (C : Paper2.SelectedTape.Algorithm) (K N₁ : ℕ) (hN₁ : 1 ≤ N₁) (w : List Bool) : ℕ :=
  let Φ := routedV K N₁ hN₁ w
  let eL := (EncodedCNF.encode Φ.val).length
  let fL := (fOut Φ.val).length
  let L := cutLen Φ.val
  let Y := 2 ^ C.cR * L
  let hL := hwLen D B Φ
  twoCutTime K N₁ C.cR w + 2 * (2 * (2 * fL + 1 + L) + 1 + Y) + 2 +
    ((2 * (2 * fL + 1 + L) +
        ((2 * fL + (2 * eL + 3) + 2 * eL + 6) + 2 * (2 * eL + 1 + L) + 2 + tailTime D B Φ) +
        2 * hL + 6) +
      2 * (2 * hL + 1 + Y) + 2 + clsTime C hL Y)

set_option maxHeartbeats 1600000 in
/-- **Segment 4: the composite on EVERY word.** -/
theorem dec_outputs_all (C : Paper2.SelectedTape.Algorithm) (K : ℕ) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N₁ (hN₁ : 1 ≤ N₁), N₀ ≤ N₁ → 2 ≤ K * N₁ →
      ∀ (w t : List Bool), 2 ^ C.cR * L1 K N₁ w ≤ t.length →
      1 ≤ kOf (routedV K N₁ hN₁ w).val.variables ∧
      ∃ t' : (Sel D B (routedV K N₁ hN₁ w)).Tape,
        (Sel D B (routedV K N₁ hN₁ w)).tapeBits t' =
          t.take (Sel D B (routedV K N₁ hN₁ w)).inputBits ∧
        (Sel D B (routedV K N₁ hN₁ w)).inputBits ≤ L1 K N₁ w ∧
        C.tapeLength (hwOf D B (routedV K N₁ hN₁ w) t') ≤
          C.cR * Paper2.AEth.expLen (routedV K N₁ hN₁ w).val.variables ∧
        (decMachine D B C K N₁).OutputsWithin (EncodedComplexity.pair w t)
          (C.output (hwOf D B (routedV K N₁ hN₁ w) t')
            ((t.drop (L1 K N₁ w)).take (C.tapeLength (hwOf D B (routedV K N₁ hN₁ w) t'))))
          (decTime D B C K N₁ hN₁ w) := by
  obtain ⟨N₂, hN₂⟩ := inputBits_fit D B K
  obtain ⟨N₃, hN₃⟩ := classifier_fit D B K C
  refine ⟨max 1 (max N₂ (max N₃ (cut0 D B))), le_max_left _ _, ?_⟩
  intro N₁ hN₁ hle hK w t ht
  set Φ := routedV K N₁ hN₁ w with hΦ
  have hvars : N₁ ≤ Φ.val.variables := routed4_variables K N₁ w
  have hsp : Φ.val.clauses.length ≤ K * Φ.val.variables := routed4_sparse K N₁ hK w
  have hN2 : N₂ ≤ Φ.val.variables := by
    have : N₂ ≤ max 1 (max N₂ (max N₃ (cut0 D B))) := le_trans (le_max_left _ _) (le_max_right _ _)
    omega
  have hN3' : N₃ ≤ Φ.val.variables := by
    have : N₃ ≤ max 1 (max N₂ (max N₃ (cut0 D B))) :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    omega
  have hN4 : cut0 D B ≤ Φ.val.variables := by
    have : cut0 D B ≤ max 1 (max N₂ (max N₃ (cut0 D B))) :=
      le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    omega
  obtain ⟨hk, hI⟩ := hN₂ Φ hsp hN2
  have hI' : (Sel D B Φ).inputBits ≤ Paper2.AEth.expLen Φ.val.variables := hI
  have hge := cutLen_ge Φ.val
  have hLdef : L1 K N₁ w = cutLen Φ.val := rfl
  have hpow : L1 K N₁ w ≤ 2 ^ C.cR * L1 K N₁ w := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  -- stage 1: the two-block cut
  have h1 := twoCut_outputs K N₁ C.cR hN₁ w t
  set c1 := t.take (L1 K N₁ w) with hc1
  set c2 := (t.take (2 ^ C.cR * L1 K N₁ w)).drop (L1 K N₁ w) with hc2
  have hc1l : c1.length = cutLen Φ.val := by
    rw [hc1, List.length_take, hLdef]; exact Nat.min_eq_left (by omega)
  have hc2l : c2.length = 2 ^ C.cR * L1 K N₁ w - L1 K N₁ w := by
    rw [hc2, List.length_drop, List.length_take, Nat.min_eq_left ht]
  -- stage 2: the header on the reduction block
  have hIc : (Sel D B Φ).inputBits ≤ c1.length := by rw [hc1l]; omega
  obtain ⟨t', ht', htail⟩ := tail_outputs D B Φ hk hN4 c1 (by rw [hc1l]) hIc
  have hfst := Paper2.AEth3.Fst.machine_outputs (EncodedCNF.encode Φ.val)
    (EncodedComplexity.pair (List.replicate (Paper2.AEth.expLen Φ.val.variables) true) [])
  have hfst' : Paper2.AEth3.Fst.machine.OutputsWithin (fOut Φ.val) (EncodedCNF.encode Φ.val)
      (2 * (EncodedCNF.encode Φ.val).length + 3) := hfst
  have hp1 := Paper2.Unit4Shell.PairMap.machine_outputs (M := Paper2.AEth3.Fst.machine)
    (fOut Φ.val) (EncodedCNF.encode Φ.val) c1 _ hfst'
  have hM1 := BitMachineComposition.composition_outputsWithin _ _ hp1 htail
  have hpm := Paper2.Unit4Shell.PairMap.machine_outputs (M := M1 D B)
    (EncodedComplexity.pair (fOut Φ.val) c1) (hwOf D B Φ t') c2 _ hM1
  -- stage 3: the classifier on the classifier block
  have hfit := (hN₃ Φ hsp hN3' t').1
  have hsb := second_block_fit C.cR Φ.val
  have hs2 : C.tapeLength (hwOf D B Φ t') ≤ c2.length := by
    rw [hc2l, hLdef]; rw [hLdef] at hpow; omega
  have hY : c2.length ≤ 2 ^ C.cR * L1 K N₁ w := by rw [hc2l]; omega
  have hcls := clsStage_outputs C (hwOf D B Φ t') c2 (2 ^ C.cR * L1 K N₁ w) hY hs2
  have hblk : c2.take (C.tapeLength (hwOf D B Φ t')) =
      (t.drop (L1 K N₁ w)).take (C.tapeLength (hwOf D B Φ t')) :=
    (blocks_eq (L1 K N₁ w) C.cR 0 _ t (Nat.zero_le _) (by rw [hLdef]; omega)).2
  rw [hblk] at hcls
  refine ⟨hk, t', ?_, by rw [hLdef]; omega, hfit, ?_⟩
  · rw [ht', hc1, List.take_take, Nat.min_eq_left (by rw [hLdef]; omega)]
  have hC := BitMachineComposition.composition_outputsWithin _ _ h1
    (BitMachineComposition.composition_outputsWithin _ _ hpm hcls)
  refine BitMachine.outputsWithin_mono _ hC ?_
  have hhw := hw_length_eq D B Φ t'
  simp only [decTime, EncodedComplexity.pair_length, hhw]
  rw [← hΦ]
  have hc1le : c1.length ≤ cutLen Φ.val := by omega
  have hfL : (fOut Φ.val).length + 1 = cutLen Φ.val := rfl
  have hy : clsTime C (hwLen D B Φ) (2 ^ C.cR * L1 K N₁ w) =
      clsTime C (hwLen D B Φ) (2 ^ C.cR * cutLen Φ.val) := rfl
  have hu : (fOut (routed4 K N₁ w)).length = (fOut Φ.val).length := rfl
  have hm : 2 ^ C.cR * L1 K N₁ w - L1 K N₁ w = 2 ^ C.cR * cutLen Φ.val - cutLen Φ.val := rfl
  have hp : 2 ^ C.cR * L1 K N₁ w = 2 ^ C.cR * cutLen Φ.val := rfl
  omega

/-- The cutoff of `dec_outputs_all`. -/
def N0 (C : Paper2.SelectedTape.Algorithm) (K : ℕ) : ℕ := Classical.choose (dec_outputs_all D B C K)

theorem N0_spec (C : Paper2.SelectedTape.Algorithm) (K : ℕ) :
    1 ≤ N0 D B C K ∧ ∀ N₁ (hN₁ : 1 ≤ N₁), N0 D B C K ≤ N₁ → 2 ≤ K * N₁ →
      ∀ (w t : List Bool), 2 ^ C.cR * L1 K N₁ w ≤ t.length →
      1 ≤ kOf (routedV K N₁ hN₁ w).val.variables ∧
      ∃ t' : (Sel D B (routedV K N₁ hN₁ w)).Tape,
        (Sel D B (routedV K N₁ hN₁ w)).tapeBits t' =
          t.take (Sel D B (routedV K N₁ hN₁ w)).inputBits ∧
        (Sel D B (routedV K N₁ hN₁ w)).inputBits ≤ L1 K N₁ w ∧
        C.tapeLength (hwOf D B (routedV K N₁ hN₁ w) t') ≤
          C.cR * Paper2.AEth.expLen (routedV K N₁ hN₁ w).val.variables ∧
        (decMachine D B C K N₁).OutputsWithin (EncodedComplexity.pair w t)
          (C.output (hwOf D B (routedV K N₁ hN₁ w) t')
            ((t.drop (L1 K N₁ w)).take (C.tapeLength (hwOf D B (routedV K N₁ hN₁ w) t'))))
          (decTime D B C K N₁ hN₁ w) :=
  Classical.choose_spec (dec_outputs_all D B C K)

end Paper2.AEth5

end

#print axioms Paper2.AEth5.tail_outputs
#print axioms Paper2.AEth5.hw_length_eq
#print axioms Paper2.AEth5.dec_outputs_all
#print axioms Paper2.AEth5.N0_spec
