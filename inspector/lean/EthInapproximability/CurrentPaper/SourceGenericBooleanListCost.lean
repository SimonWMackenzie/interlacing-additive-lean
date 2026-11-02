import EthInapproximability.CurrentPaper.SourceGenericBooleanListMapper

/-!
# The branch iterator of the Boolean stage: original-`n` per-branch envelopes

Paper B, locked v8 Section 6 and Appendix B; CP-SOURCE-EFFECTIVE.

`BooleanListMapper.machine D` is the admitted framed list controller, i.e. the
physical branch iterator over the sparse branch list `S.branches f`. Its clock
`mapTime D S f` is bounded here with every per-branch cost replaced by an
envelope in the ORIGINAL variable count `n = f.val.variables` only, so that the
number of branches enters exclusively as an outer count multiplier
(`mapTime_le_source`, instantiating the admitted
`SourceListMachineOuter.canonicalBound_le_source`).
-/

namespace EthInapproximability.CurrentPaper.SourceGenericComposite.BooleanListMapper

open BitMachine BitMachineEncoding EncodedCommunication
open SourceGenericComposite.Converter

variable {η : ℚ} (S : EncodedETHSource.Sparsification η)
  (D : EncodedETHSource.DinurReduction)

/-- Input packet (Dinur-stage output) envelope: the admitted Dinur one. -/
noncomputable def inEnv (n : Nat) : Nat := SourceOriginalDinurListMapper.outputEnvelope S D n

noncomputable def boundEnv (n : Nat) : Nat :=
  7 * (inEnv S D n + 2) +
    (1 + 4 * (convMachine D).pushBound) * (convC D.alphabet D.arity * (inEnv S D n + 1) ^ 27)

noncomputable def outEnv (n : Nat) : Nat :=
  inEnv S D n + boundEnv S D n * (itemMachine D).pushBound

noncomputable def framedEnv (n : Nat) : Nat := 3 * outEnv S D n + 1

noncomputable def framedTimeEnv (n : Nat) : Nat :=
  boundEnv S D n + 2 * outEnv S D n + 2 +
    (UnaryBinaryEncoding.coefficient + 7) * (outEnv S D n + 1) ^ 2

noncomputable def itemEnv (n : Nat) : Nat :=
  let F := SourceListMachineOuterFramed.itemMachine (itemMachine D)
  let L := inEnv S D n
  let R := framedEnv S D n
  let T := framedTimeEnv S D n
  20*(L+1)*(L+1)+T+4*L+R+F.stackCount*(L+T*F.pushBound+1)+9

theorem input_length_le (f : EncodedETHSource.ValidFormula) (hn : 1 ≤ f.val.variables)
    (g : EncodedETHSource.ValidFormula) (hg : g ∈ S.branches f) :
    (SourceOriginalDinurListMapper.cspPacket D f.val.variables g).length ≤
      inEnv S D f.val.variables := by
  have h := SourceOriginalDinurListMapper.output_length_le S D f hn g hg
  rw [SourceOriginalDinurListMapper.itemOutput_eq D g f.val.variables] at h
  exact h

theorem itemBound_mono {x y : List Bool} (h : x.length ≤ y.length) :
    itemBound D x ≤ itemBound D y := by
  unfold itemBound
  have hp := Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 27
  have hm := Nat.mul_le_mul_left (convC D.alphabet D.arity) hp
  have hm2 := Nat.mul_le_mul_left (1 + 4 * (convMachine D).pushBound) hm
  omega

theorem bound_le (f : EncodedETHSource.ValidFormula) (hn : 1 ≤ f.val.variables)
    (g : EncodedETHSource.ValidFormula) (hg : g ∈ S.branches f) :
    itemBound D (SourceOriginalDinurListMapper.cspPacket D f.val.variables g) ≤
      boundEnv S D f.val.variables := by
  have hi := input_length_le S D f hn g hg
  unfold itemBound boundEnv
  have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hi 1) 27
  have hm := Nat.mul_le_mul_left (convC D.alphabet D.arity) hp
  have hm2 := Nat.mul_le_mul_left (1 + 4 * (convMachine D).pushBound) hm
  omega

theorem output_length_le (f : EncodedETHSource.ValidFormula) (hn : 1 ≤ f.val.variables)
    (g : EncodedETHSource.ValidFormula) (hg : g ∈ S.branches f) :
    (boolPacket D f.val.variables g).length ≤ outEnv S D f.val.variables := by
  have ho := BitMachine.output_length_bound (itemMachine D) (item_run D f.val.variables g)
  have hi := input_length_le S D f hn g hg
  have ht := bound_le S D f hn g hg
  have hp := Nat.mul_le_mul_right (itemMachine D).pushBound ht
  unfold outEnv
  omega

theorem itemOutput_length_le (f : EncodedETHSource.ValidFormula) (hn : 1 ≤ f.val.variables)
    (g : EncodedETHSource.ValidFormula) (hg : g ∈ S.branches f) :
    (itemOutput D (SourceOriginalDinurListMapper.cspPacket D f.val.variables g)).length ≤
      outEnv S D f.val.variables := by
  rw [itemOutput_eq D f.val.variables g]
  exact output_length_le S D f hn g hg

theorem framed_length_le (f : EncodedETHSource.ValidFormula) (hn : 1 ≤ f.val.variables)
    (g : EncodedETHSource.ValidFormula) (hg : g ∈ S.branches f) :
    (SourceListMachineOuterFramed.framedOutput (itemOutput D)
      (SourceOriginalDinurListMapper.cspPacket D f.val.variables g)).length ≤
      framedEnv S D f.val.variables := by
  have ho := itemOutput_length_le S D f hn g hg
  have hf := EncodedGraph.natField_length_upper
    (itemOutput D (SourceOriginalDinurListMapper.cspPacket D f.val.variables g)).length
  unfold SourceListMachineOuterFramed.framedOutput framedEnv
  simp only [List.length_append]
  omega

theorem framed_bound_le (f : EncodedETHSource.ValidFormula) (hn : 1 ≤ f.val.variables)
    (g : EncodedETHSource.ValidFormula) (hg : g ∈ S.branches f) :
    SourceListMachineOuterFramed.framedBound (itemOutput D) (itemBound D)
      (SourceOriginalDinurListMapper.cspPacket D f.val.variables g) ≤
      framedTimeEnv S D f.val.variables := by
  have ho := itemOutput_length_le S D f hn g hg
  have ht := bound_le S D f hn g hg
  have hp := Nat.pow_le_pow_left
    (show (itemOutput D (SourceOriginalDinurListMapper.cspPacket D f.val.variables g)).length + 1 ≤
      outEnv S D f.val.variables + 1 by omega) 2
  unfold SourceListMachineOuterFramed.framedBound framedTimeEnv
  have hmul := Nat.mul_le_mul_left (UnaryBinaryEncoding.coefficient + 7) hp
  omega

theorem itemCost_le (f : EncodedETHSource.ValidFormula) (hn : 1 ≤ f.val.variables) :
    ∀ x ∈ inputItems D f.val.variables (S.branches f),
      SourceListMachineWork.itemCost (SourceListMachineOuterFramed.itemMachine (itemMachine D)) x
        (SourceListMachineOuterFramed.framedOutput (itemOutput D) x)
        (SourceListMachineOuterFramed.framedBound (itemOutput D) (itemBound D) x) ≤
      itemEnv S D f.val.variables := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
  exact SourceListMachineWork.itemCost_le_envelope _ _ _ _
    (inEnv S D f.val.variables) (framedEnv S D f.val.variables)
    (framedTimeEnv S D f.val.variables)
    (input_length_le S D f hn g hg) (framed_length_le S D f hn g hg)
    (framed_bound_le S D f hn g hg)

theorem framedOut_le (f : EncodedETHSource.ValidFormula) (hn : 1 ≤ f.val.variables) :
    ∀ x ∈ inputItems D f.val.variables (S.branches f),
      (SourceListMachineOuterFramed.framedOutput (itemOutput D) x).length ≤
        framedEnv S D f.val.variables := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
  exact framed_length_le S D f hn g hg

/-- The branch iterator's literal clock, per-branch terms in the original `n`. -/
theorem mapTime_le_count (f : EncodedETHSource.ValidFormula) (hn : 1 ≤ f.val.variables) :
    mapTime D S f ≤
      5*(S.branches f).length.bits.length+7 +
      ((S.branches f).length*itemEnv S D f.val.variables +
        (S.branches f).length*(4*(S.branches f).length.bits.length+7)) +
      (4*(S.branches f).length.bits.length+
        (natField (S.branches f).length).length+
        (S.branches f).length*framedEnv S D f.val.variables+9) := by
  have h := SourceListMachineOuter.canonicalBound_le_count
    (SourceListMachineOuterFramed.itemMachine (itemMachine D))
    (inputItems D f.val.variables (S.branches f))
    (SourceListMachineOuterFramed.framedOutput (itemOutput D))
    (SourceListMachineOuterFramed.framedBound (itemOutput D) (itemBound D))
    (itemEnv S D f.val.variables) (framedEnv S D f.val.variables)
    (itemCost_le S D f hn) (framedOut_le S D f hn)
  simpa only [mapTime, listTime, inputItems, List.length_map] using h

/-- Branches enter only as an outer count multiplier: for any branch-count cap
and digit cap in the original `n`. -/
theorem mapTime_le_source (f : EncodedETHSource.ValidFormula) (hn : 1 ≤ f.val.variables)
    (branchCap digitCap : Nat → Nat)
    (hcount : (S.branches f).length ≤ branchCap f.val.variables)
    (hdigits : (S.branches f).length.bits.length ≤ digitCap f.val.variables) :
    mapTime D S f ≤
      branchCap f.val.variables *
          (itemEnv S D f.val.variables + 4*digitCap f.val.variables + 7 +
            framedEnv S D f.val.variables) +
        11*digitCap f.val.variables + 17 := by
  have h := SourceListMachineOuter.canonicalBound_le_source
    (SourceListMachineOuterFramed.itemMachine (itemMachine D))
    (inputItems D f.val.variables (S.branches f))
    (SourceListMachineOuterFramed.framedOutput (itemOutput D))
    (SourceListMachineOuterFramed.framedBound (itemOutput D) (itemBound D))
    f.val.variables branchCap digitCap (itemEnv S D) (framedEnv S D)
    (by simpa only [inputItems, List.length_map] using hcount)
    (by simpa only [inputItems, List.length_map] using hdigits)
    (itemCost_le S D f hn) (framedOut_le S D f hn)
  simpa only [mapTime, listTime] using h

/-- Length of the Boolean-stage list (the BOT stage input). -/
theorem booleanPacketList_length_le (f : EncodedETHSource.ValidFormula)
    (hn : 1 ≤ f.val.variables) :
    (SourceOriginalBOTSourceTarget.booleanPacketList S D f).length ≤
      3*(S.branches f).length*(outEnv S D f.val.variables+1)+1 := by
  rw [← output_is_bot_input]
  exact SourceListEncoding.encode_map_length_le (S.branches f)
    (boolPacket D f.val.variables) (outEnv S D f.val.variables)
    (fun g hg => output_length_le S D f hn g hg)

/-- The uniform encoded word cap of every Boolean branch (BOT stage input word). -/
theorem boolean_word_le (f : EncodedETHSource.ValidFormula) (hn : 1 ≤ f.val.variables) :
    ∀ g ∈ EncodedETHSourceComposition.booleanBranches S D f,
      (EncodedCNF.encode g.val).length ≤ outEnv S D f.val.variables := by
  intro g' hg'
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
  have h := output_length_le S D f hn g hg
  unfold boolPacket SourceOriginalBranchPackets.sparsePacket at h
  rw [SourceOriginalBranchPackets.packet_length] at h
  omega

#print axioms input_length_le
#print axioms output_length_le
#print axioms mapTime_le_count
#print axioms mapTime_le_source
#print axioms booleanPacketList_length_le
#print axioms boolean_word_le

end EthInapproximability.CurrentPaper.SourceGenericComposite.BooleanListMapper
