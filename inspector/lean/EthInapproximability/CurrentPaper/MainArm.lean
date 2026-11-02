import EthInapproximability.CurrentPaper.Bridges
import EthInapproximability.CurrentPaper.SourceListMachineOuterFramed
import EthInapproximability.CurrentPaper.SignedMidpointApproxActualMapper
import EthInapproximability.CurrentPaper.SignedMidpointApproxCanonical
import EthInapproximability.CurrentPaper.SourceOriginalBranchPackets

/-!
# The main arm over H-B1 and the per-branch item interface (unit 4, B4-S7, main-arm assembly)

Source: frozen v8 `06-eth.tex:204-243`. The main arm is ONE fixed machine

`composition Msrc (composition (SourceListMachineOuterFramed.machine Titem) (satMachine M))`

where `Msrc` is the H-B1 source-list machine and `Titem` the per-branch item machine
(B4-S3 → H-B2 → B4-S4 → B4-S5). This module proves, for every valid `f` with `1 ≤ n` and
`1 ≤ L n`, that it outputs `[satAnswer (encode f)]` within an explicit (unsimplified) time, from:

* `hsrc`: the H-B1 run on `encode f` (map §1.5 form, one formula);
* `hitem`: the item interface: on the item word of each sparse branch `g`, `Titem` outputs
  exactly `SignedMidpointApproxCanonical.packet M (branchOf g).table (branchOf g).threshold (L n)`;
* the admitted estimator callback (`hM`, `herr`) from `approximation_supplies_callback`.

Correctness uses `Unit4Bridges.branches_semantics` and the admitted
`SignedMidpointApproxActualMapper.sat_outputs_linear`. The time is NOT absorbed into the budget
shape here (that is B4-S6e).
-/

namespace EthInapproximability.CurrentPaper.Unit4MainArm

open EncodedETHSource EncodedETHSourceComposition Unit4Bridges

variable {η : ℚ} (S : Sparsification η) (D : DinurReduction)
  (B : BOTReduction (booleanOccurrence D))

/-- The H-B1 list item of a sparse branch: original `n`, then the literal graph bytes. -/
noncomputable def itemWord (n : ℕ) (g : ValidFormula) : List Bool :=
  SourceOriginalBranchPackets.packet n
    (EncodedGraph.encode (B.output (booleanFormula D g).val (booleanFormula D g).property n))

theorem sourceList_eq (f : ValidFormula) :
    (sourceGraphs S D B f).map
        (fun g => SourceOriginalBranchPackets.packet f.val.variables (EncodedGraph.encode g.val)) =
      (S.branches f).map (itemWord D B f.val.variables) := by
  simp [sourceGraphs, BOTReduction.graphList, booleanBranches, itemWord, List.map_map,
    Function.comp_def]

variable (c A d : ℕ) (M : BitMachine.Machine)

open Classical in
/-- The item function realized by `Titem` on the item words (classical selection of a branch
with that item word; well defined by `BitMachine.outputsWithin_unique`). -/
noncomputable def itemFun (f : ValidFormula) (k : ℕ) (x : List Bool) : List Bool :=
  if h : ∃ g ∈ S.branches f, itemWord D B f.val.variables g = x then
    SignedMidpointApproxCanonical.packet M
      (branchOf D B c A d f.val.variables (Classical.choose h)).table
      (branchOf D B c A d f.val.variables (Classical.choose h)).threshold k
  else []

theorem itemFun_eq (f : ValidFormula) (k : ℕ) (Titem : BitMachine.Machine)
    (bound : List Bool → ℕ)
    (hitem : ∀ g ∈ S.branches f, Titem.OutputsWithin (itemWord D B f.val.variables g)
      (SignedMidpointApproxCanonical.packet M (branchOf D B c A d f.val.variables g).table
        (branchOf D B c A d f.val.variables g).threshold k)
      (bound (itemWord D B f.val.variables g)))
    (g : ValidFormula) (hg : g ∈ S.branches f) :
    itemFun S D B c A d M f k (itemWord D B f.val.variables g) =
      SignedMidpointApproxCanonical.packet M (branchOf D B c A d f.val.variables g).table
        (branchOf D B c A d f.val.variables g).threshold k := by
  have h : ∃ g' ∈ S.branches f, itemWord D B f.val.variables g' = itemWord D B f.val.variables g :=
    ⟨g, hg, rfl⟩
  unfold itemFun
  rw [dif_pos h]
  obtain ⟨hg', heq⟩ := Classical.choose_spec h
  have h1 := hitem _ hg'
  rw [heq] at h1
  exact BitMachine.outputsWithin_unique Titem h1 (hitem g hg)

/-- B4-S5 list lemma: the framed list mapper over the item machine produces exactly the
estimator back end's input word `packetList M k (branches ...)`. -/
theorem item_list (f : ValidFormula) (k : ℕ) (Titem : BitMachine.Machine)
    (bound : List Bool → ℕ)
    (hitem : ∀ g ∈ S.branches f, Titem.OutputsWithin (itemWord D B f.val.variables g)
      (SignedMidpointApproxCanonical.packet M (branchOf D B c A d f.val.variables g).table
        (branchOf D B c A d f.val.variables g).threshold k)
      (bound (itemWord D B f.val.variables g))) :
    (SourceListMachineOuterFramed.machine Titem).OutputsWithin
      (SourceListEncoding.encode ((S.branches f).map (itemWord D B f.val.variables)))
      (SignedMidpointApproxCanonical.packetList M k (branches S D B c A d f))
      (SourceListMachineOuter.canonicalBound (SourceListMachineOuterFramed.itemMachine Titem)
        ((S.branches f).map (itemWord D B f.val.variables))
        (SourceListMachineOuterFramed.framedOutput (itemFun S D B c A d M f k))
        (SourceListMachineOuterFramed.framedBound (itemFun S D B c A d M f k) bound)) := by
  have hM : ∀ x ∈ (S.branches f).map (itemWord D B f.val.variables),
      Titem.OutputsWithin x (itemFun S D B c A d M f k x) (bound x) := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    rw [itemFun_eq S D B c A d M f k Titem bound hitem g hg]
    exact hitem g hg
  have h := SourceListMachineOuterFramed.outputsWithin Titem _ _ bound hM
  have hl : ((S.branches f).map (itemWord D B f.val.variables)).map (itemFun S D B c A d M f k) =
      (branches S D B c A d f).map
        (fun b => SignedMidpointApproxCanonical.packet M b.table b.threshold k) := by
    rw [List.map_map, branches, List.map_map]
    apply List.map_congr_left
    intro g hg
    exact itemFun_eq S D B c A d M f k Titem bound hitem g hg
  rw [hl] at h
  exact h

/-- **Main-arm assembly.** Correctness and explicit time of the fixed main arm on every valid
formula with `1 ≤ n` and `1 ≤ L n`, from H-B1 (`hsrc`), the item interface (`hitem`) and the
admitted estimator callback. -/
theorem main_arm_outputs (c' d' : ℕ) (answer : List Bool → ℤ)
    (hM : M.ComputesWithin (fun table => EncodedETHTail.encodeInteger (answer table))
      (fun n => c' * (n + 1) ^ d'))
    (herr : ∀ b : EncodedETHTail.Branch, |answer b.table - (b.cost : ℤ)| ≤
      (FinalPadding.allowance (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
        (sourceSizeExponent S D B)) b.table.length : ℤ))
    (hsource : 2 ^ 44 * (B.degreeBound : ℚ) / sourceGap D B ≤ c)
    (Msrc Titem : BitMachine.Machine) (bound : List Bool → ℕ) (T1 : ℕ)
    (f : ValidFormula) (hn : 1 ≤ f.val.variables)
    (hk : 1 ≤ ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
      (sourceSizeExponent S D B) f.val.variables)
    (hsrc : Msrc.OutputsWithin (EncodedCNF.encode f.val)
      (SourceListEncoding.encode ((sourceGraphs S D B f).map fun g =>
        SourceOriginalBranchPackets.packet f.val.variables (EncodedGraph.encode g.val))) T1)
    (hitem : ∀ g ∈ S.branches f, Titem.OutputsWithin (itemWord D B f.val.variables g)
      (SignedMidpointApproxCanonical.packet M
        (branchOf D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
          f.val.variables g).table
        (branchOf D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
          f.val.variables g).threshold
        (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
          (sourceSizeExponent S D B) f.val.variables))
      (bound (itemWord D B f.val.variables g))) :
    (BitMachineComposition.composition Msrc
      (BitMachineComposition.composition (SourceListMachineOuterFramed.machine Titem)
        (SignedMidpointApproxActualMapper.satMachine M))).OutputsWithin
      (EncodedCNF.encode f.val) [EncodedETHTail.satAnswer (EncodedCNF.encode f.val)]
      (T1 + 2 * (SourceListEncoding.encode ((S.branches f).map
          (itemWord D B f.val.variables))).length + 2 +
        (SourceListMachineOuter.canonicalBound (SourceListMachineOuterFramed.itemMachine Titem)
            ((S.branches f).map (itemWord D B f.val.variables))
            (SourceListMachineOuterFramed.framedOutput
              (itemFun S D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B) M f
                (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
                  (sourceSizeExponent S D B) f.val.variables)))
            (SourceListMachineOuterFramed.framedBound
              (itemFun S D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B) M f
                (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
                  (sourceSizeExponent S D B) f.val.variables)) bound) +
          2 * (SignedMidpointApproxCanonical.packetList M
            (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
              (sourceSizeExponent S D B) f.val.variables)
            (branches S D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B) f)).length
            + 2 +
          (SignedMidpointApproxActualMapper.mapTime M c' d'
            (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
              (sourceSizeExponent S D B) f.val.variables)
            (branches S D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B) f) +
            18 * (branches S D B c (2 ^ sourceSizeExponent S D B)
              (sourceSizeExponent S D B) f).length + 6))) := by
  obtain ⟨herr', hgap, hyes, hno⟩ := branches_semantics S D B c f hn hk hsource answer herr
  have hsat := SignedMidpointApproxActualMapper.sat_outputs_linear M c' d' answer hM
    (EncodedCNF.encode f.val)
    (branches S D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B) f)
    (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
      (sourceSizeExponent S D B) f.val.variables) _ herr' hgap hyes hno
  have hlist := item_list S D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B) M f
    (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
      (sourceSizeExponent S D B) f.val.variables) Titem bound hitem
  rw [sourceList_eq] at hsrc
  have h2 := BitMachineComposition.composition_outputsWithin
    (SourceListMachineOuterFramed.machine Titem) (SignedMidpointApproxActualMapper.satMachine M)
    hlist hsat
  exact BitMachineComposition.composition_outputsWithin Msrc _ hsrc h2

end EthInapproximability.CurrentPaper.Unit4MainArm
