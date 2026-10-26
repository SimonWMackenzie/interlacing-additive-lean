import EthInapproximability.CurrentPaper.U4PhysBridges
import EthInapproximability.CurrentPaper.MainArm
import EthInapproximability.CurrentPaper.SourceGenericSourceEndpoint

/-!
# Unit-4 main arm over the unit-1 endpoint, H-B2 (`HB2Physical`) and the post stage

Lane owner:b-unit4-shell-2 (Paper B, v8 `06-eth.tex:204-243`, proof of `thm:main`).

* `hsrc` (H-B1) is discharged by the admitted unit-1 endpoint
  `SourceGenericComposite.SourceEndpoint.source_effective` (its machine, constants, first and
  second conjuncts), imported by exact production name.
* The item machine is ONE fixed composition `composition Mtab Mpost`: `Mtab` is the machine of
  `PhysicalLevelRun.HB2Physical` (H-B2, imported definition, kept as a hypothesis through the
  definitional unfolding `hb2_iff`, proved by `Iff.rfl`), and `Mpost` is the post stage
  (B4-S3 exponent `p = n / (2 max 1 k)` from H-B2's unary `n`, `k` fields; B4-S4 padded table;
  B4-S5 width-changing framer into `SignedMidpointApproxCanonical.packet M`). The post stage is
  NOT built in this lane; its exact contract is the named interface `PostBody`/`PostPhysical`.
* The branch objects are those of the physical run (`Unit4PhysBridges`), since H-B2 produces
  the table of `physRun`.

Nothing here absorbs the time into the consumer budget (B4-S6e is not done).
-/

namespace EthInapproximability.CurrentPaper.Unit4ItemAssembly

open EncodedETHSource EncodedETHSourceComposition EffectiveIteration
open Unit4Bridges Unit4PhysBridges Unit4MainArm
open EthInapproximability.ParameterizedNP.GuardedSourceGraph

-- The same local instance as `EncodedETHSource.lean:34-35` and `Bridges.lean:27`.
local instance (n : ℕ) (p : Fin n → Prop) [DecidablePred p] : Decidable (∃ i, p i) :=
  Fintype.decidableExistsFintype

/-! ## H-B2, unfolded (same definition) -/

/-- The body of `PhysicalLevelRun.HB2Physical` for a named machine and named constants. -/
def HB2Body (c A d Δ : ℕ) (γ : ℚ) (Mtab : BitMachine.Machine) (C₂ E₂ F₂ : ℕ) : Prop :=
  ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) (n : ℕ),
    G.SourceCommon γ Δ → n ≤ Fintype.card E →
    Fintype.card E ≤ A * n * sourceDepth n ^ d →
    1 ≤ ETHTailGrowth.repetitions c A d n →
    let k := ETHTailGrowth.repetitions c A d n
    let b := sourceDepth n
    let st := PhysicalLevelRun.physRun G c b (Iteration.seedState b) k
    let w := SourceOriginalBranchPackets.packet n
      (EncodedGraph.encode (EncodedETHSource.serializeGraph G))
    Mtab.OutputsWithin w
      (BitMachineBankCodec.encode ![List.replicate n true, List.replicate k true,
        List.replicate st.matrix.rows true, List.replicate st.matrix.columns true,
        MatrixMaterialization.rowMajor st.matrix.entry, List.replicate st.budget true])
      (C₂ * (w.length + 1) ^ E₂ *
        FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ F₂)

/-- `HB2Physical` is literally the existential closure of `HB2Body`. -/
theorem hb2_iff (c A d Δ : ℕ) (γ : ℚ) :
    PhysicalLevelRun.HB2Physical c A d Δ γ ↔
      ∃ (Mtab : BitMachine.Machine) (C₂ E₂ F₂ : ℕ), HB2Body c A d Δ γ Mtab C₂ E₂ F₂ :=
  Iff.rfl

/-! ## The post stage interface (B4-S3 + B4-S4 + B4-S5; NOT built here) -/

/-- H-B2's output bank word, as a function of its six fields. -/
def hb2Word (n k m r y : ℕ) (R : List Bool) : List Bool :=
  BitMachineBankCodec.encode ![List.replicate n true, List.replicate k true,
    List.replicate m true, List.replicate r true, R, List.replicate y true]

/-- Contract of the post stage for a named machine: from H-B2's six-field bank word, compute
`p = n / (2 max 1 k)` (B4-S3), write the padded table `FinalPadding.table R p` (B4-S4) and frame
it with the unary threshold `y` and unary `k` into the estimator back end's packet of width
`M.stackCount + 4` (B4-S5); time polynomial in the input length and in `2^(2p)`. -/
def PostBody (M Mpost : BitMachine.Machine) (Cp Ep : ℕ) : Prop :=
  ∀ (n k m r y : ℕ) (R : Fin m → Fin r → Bool) (hm : 0 < m) (hr : 0 < r),
    Mpost.OutputsWithin (hb2Word n k m r y (MatrixMaterialization.rowMajor R))
      (SignedMidpointApproxCanonical.packet M
        (FinalPadding.table R (n / (2 * max 1 k)) hm hr) y k)
      (Cp * ((hb2Word n k m r y (MatrixMaterialization.rowMajor R)).length + 1) ^ Ep *
        (2 ^ (2 * (n / (2 * max 1 k)))) ^ Ep)

/-- The post stage exists (named interface, NOT proved in this lane). -/
def PostPhysical (M : BitMachine.Machine) : Prop :=
  ∃ (Mpost : BitMachine.Machine) (Cp Ep : ℕ), PostBody M Mpost Cp Ep

/-- Per-item time of `composition Mtab Mpost`, as a function of the item word only (for fixed
`T`, the table size). -/
def itemBound (Mtab : BitMachine.Machine) (C₂ E₂ F₂ Cp Ep T : ℕ) (x : List Bool) : ℕ :=
  C₂ * (x.length + 1) ^ E₂ * T ^ F₂ +
    2 * (x.length + C₂ * (x.length + 1) ^ E₂ * T ^ F₂ * Mtab.pushBound) + 2 +
    Cp * (x.length + C₂ * (x.length + 1) ^ E₂ * T ^ F₂ * Mtab.pushBound + 1) ^ Ep * T ^ Ep

section Item

variable {η : ℚ} (S : Sparsification η) (D : DinurReduction)
  (B : BOTReduction (booleanOccurrence D)) (c : ℕ) (M : BitMachine.Machine)

/-- **Item assembly.** On the item word of every sparse branch, the ONE fixed machine
`composition Mtab Mpost` outputs exactly the estimator packet of the physical branch at
`k = L n`, within `itemBound`. -/
theorem item_run (hsource : 2 ^ 44 * (B.degreeBound : ℚ) / sourceGap D B ≤ c)
    (Mtab : BitMachine.Machine) (C₂ E₂ F₂ : ℕ)
    (htab : HB2Body c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
      B.degreeBound (sourceGap D B) Mtab C₂ E₂ F₂)
    (Mpost : BitMachine.Machine) (Cp Ep : ℕ) (hpost : PostBody M Mpost Cp Ep)
    (f : ValidFormula) (hn : 1 ≤ f.val.variables)
    (hk : 1 ≤ ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
      (sourceSizeExponent S D B) f.val.variables)
    (g : ValidFormula) (hg : g ∈ S.branches f) :
    (BitMachineComposition.composition Mtab Mpost).OutputsWithin
      (itemWord D B f.val.variables g)
      (SignedMidpointApproxCanonical.packet M
        (physBranchOf D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
          f.val.variables g).table
        (physBranchOf D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
          f.val.variables g).threshold
        (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
          (sourceSizeExponent S D B) f.val.variables))
      (itemBound Mtab C₂ E₂ F₂ Cp Ep
        (FinalPadding.tableSize (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
          (sourceSizeExponent S D B)) f.val.variables)
        (itemWord D B f.val.variables g)) := by
  obtain ⟨hcommon, hlower0, hupper0⟩ := branch_source_facts S D B f hn g hg
  rw [output_eq_serialize, serializeGraph_edges] at hlower0 hupper0
  have h1 : Mtab.OutputsWithin (itemWord D B f.val.variables g)
      (hb2Word f.val.variables
        (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
          (sourceSizeExponent S D B) f.val.variables)
        (physState D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
          f.val.variables g).matrix.rows
        (physState D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
          f.val.variables g).matrix.columns
        (physState D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
          f.val.variables g).budget
        (MatrixMaterialization.rowMajor
          (physState D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
            f.val.variables g).matrix.entry))
      (C₂ * ((itemWord D B f.val.variables g).length + 1) ^ E₂ *
        FinalPadding.tableSize (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
          (sourceSizeExponent S D B)) f.val.variables ^ F₂) :=
    htab (branchGraph D B f.val.variables g) f.val.variables hcommon hlower0 hupper0 hk
  have h2 := hpost f.val.variables
    (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
      (sourceSizeExponent S D B) f.val.variables)
    (physState D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
      f.val.variables g).matrix.rows
    (physState D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
      f.val.variables g).matrix.columns
    (physState D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
      f.val.variables g).budget
    (physState D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
      f.val.variables g).matrix.entry
    (physState D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
      f.val.variables g).matrix.rows_pos
    (physState D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
      f.val.variables g).matrix.columns_pos
  have hlen := BitMachine.output_length_bound Mtab h1
  have h := BitMachineComposition.composition_outputsWithin Mtab Mpost h1 h2
  apply BitMachine.outputsWithin_mono _ h
  unfold itemBound
  set x := itemWord D B f.val.variables g
  set T := FinalPadding.tableSize (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
    (sourceSizeExponent S D B)) f.val.variables
  set t1 := C₂ * (x.length + 1) ^ E₂ * T ^ F₂
  set mid := hb2Word f.val.variables
        (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
          (sourceSizeExponent S D B) f.val.variables)
        (physState D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
          f.val.variables g).matrix.rows
        (physState D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
          f.val.variables g).matrix.columns
        (physState D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
          f.val.variables g).budget
        (MatrixMaterialization.rowMajor
          (physState D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
            f.val.variables g).matrix.entry)
  have hT : 2 ^ (2 * (f.val.variables / (2 * max 1 (ETHTailGrowth.repetitions c
      (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B) f.val.variables)))) = T := rfl
  rw [hT]
  have hp : (mid.length + 1) ^ Ep ≤ (x.length + t1 * Mtab.pushBound + 1) ^ Ep :=
    Nat.pow_le_pow_left (by omega) Ep
  have hq := Nat.mul_le_mul_right (T ^ Ep) (Nat.mul_le_mul_left Cp hp)
  omega

end Item

/-! ## The main arm on the physical branches -/

section Arm

variable {η : ℚ} (S : Sparsification η) (D : DinurReduction)
  (B : BOTReduction (booleanOccurrence D)) (c A d : ℕ) (M : BitMachine.Machine)

open Classical in
/-- The item function realized on the item words (classical selection of a branch with that
item word; well defined by `BitMachine.outputsWithin_unique`). Used only inside the stated time
expression; not a machine. -/
noncomputable def physItemFun (f : ValidFormula) (k : ℕ) (x : List Bool) : List Bool :=
  if h : ∃ g ∈ S.branches f, itemWord D B f.val.variables g = x then
    SignedMidpointApproxCanonical.packet M
      (physBranchOf D B c A d f.val.variables (Classical.choose h)).table
      (physBranchOf D B c A d f.val.variables (Classical.choose h)).threshold k
  else []

theorem physItemFun_eq (f : ValidFormula) (k : ℕ) (Titem : BitMachine.Machine)
    (bound : List Bool → ℕ)
    (hitem : ∀ g ∈ S.branches f, Titem.OutputsWithin (itemWord D B f.val.variables g)
      (SignedMidpointApproxCanonical.packet M (physBranchOf D B c A d f.val.variables g).table
        (physBranchOf D B c A d f.val.variables g).threshold k)
      (bound (itemWord D B f.val.variables g)))
    (g : ValidFormula) (hg : g ∈ S.branches f) :
    physItemFun S D B c A d M f k (itemWord D B f.val.variables g) =
      SignedMidpointApproxCanonical.packet M (physBranchOf D B c A d f.val.variables g).table
        (physBranchOf D B c A d f.val.variables g).threshold k := by
  have h : ∃ g' ∈ S.branches f, itemWord D B f.val.variables g' =
      itemWord D B f.val.variables g := ⟨g, hg, rfl⟩
  unfold physItemFun
  rw [dif_pos h]
  obtain ⟨hg', heq⟩ := Classical.choose_spec h
  have h1 := hitem _ hg'
  rw [heq] at h1
  exact BitMachine.outputsWithin_unique Titem h1 (hitem g hg)

theorem phys_item_list (f : ValidFormula) (k : ℕ) (Titem : BitMachine.Machine)
    (bound : List Bool → ℕ)
    (hitem : ∀ g ∈ S.branches f, Titem.OutputsWithin (itemWord D B f.val.variables g)
      (SignedMidpointApproxCanonical.packet M (physBranchOf D B c A d f.val.variables g).table
        (physBranchOf D B c A d f.val.variables g).threshold k)
      (bound (itemWord D B f.val.variables g))) :
    (SourceListMachineOuterFramed.machine Titem).OutputsWithin
      (SourceListEncoding.encode ((S.branches f).map (itemWord D B f.val.variables)))
      (SignedMidpointApproxCanonical.packetList M k (physBranches S D B c A d f))
      (SourceListMachineOuter.canonicalBound (SourceListMachineOuterFramed.itemMachine Titem)
        ((S.branches f).map (itemWord D B f.val.variables))
        (SourceListMachineOuterFramed.framedOutput (physItemFun S D B c A d M f k))
        (SourceListMachineOuterFramed.framedBound (physItemFun S D B c A d M f k) bound)) := by
  have hM : ∀ x ∈ (S.branches f).map (itemWord D B f.val.variables),
      Titem.OutputsWithin x (physItemFun S D B c A d M f k x) (bound x) := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    rw [physItemFun_eq S D B c A d M f k Titem bound hitem g hg]
    exact hitem g hg
  have h := SourceListMachineOuterFramed.outputsWithin Titem _ _ bound hM
  have hl : ((S.branches f).map (itemWord D B f.val.variables)).map
      (physItemFun S D B c A d M f k) =
      (physBranches S D B c A d f).map
        (fun b => SignedMidpointApproxCanonical.packet M b.table b.threshold k) := by
    rw [List.map_map, physBranches, List.map_map]
    apply List.map_congr_left
    intro g hg
    exact physItemFun_eq S D B c A d M f k Titem bound hitem g hg
  rw [hl] at h
  exact h

/-- The explicit (unabsorbed) time of the main arm with item machine `Titem`, per-item bound
`bound`, source time `T1`, estimator polynomial `(c', d')`, at `A = 2^e`, `d = e`. -/
noncomputable def armTime (c' d' : ℕ) (Titem : BitMachine.Machine) (bound : List Bool → ℕ)
    (T1 : ℕ) (f : ValidFormula) : ℕ :=
  T1 + 2 * (SourceListEncoding.encode ((S.branches f).map
      (itemWord D B f.val.variables))).length + 2 +
    (SourceListMachineOuter.canonicalBound (SourceListMachineOuterFramed.itemMachine Titem)
        ((S.branches f).map (itemWord D B f.val.variables))
        (SourceListMachineOuterFramed.framedOutput
          (physItemFun S D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B) M f
            (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
              (sourceSizeExponent S D B) f.val.variables)))
        (SourceListMachineOuterFramed.framedBound
          (physItemFun S D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B) M f
            (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
              (sourceSizeExponent S D B) f.val.variables)) bound) +
      2 * (SignedMidpointApproxCanonical.packetList M
        (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
          (sourceSizeExponent S D B) f.val.variables)
        (physBranches S D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B) f)).length
        + 2 +
      (SignedMidpointApproxActualMapper.mapTime M c' d'
        (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
          (sourceSizeExponent S D B) f.val.variables)
        (physBranches S D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B) f) +
        18 * (physBranches S D B c (2 ^ sourceSizeExponent S D B)
          (sourceSizeExponent S D B) f).length + 6))

/-- Main arm on the physical branches, over a supplied source run and item interface
(the physical-run analogue of the frozen `Unit4MainArm.main_arm_outputs`). -/
theorem phys_main_arm_outputs (c' d' : ℕ) (answer : List Bool → ℤ)
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
        (physBranchOf D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
          f.val.variables g).table
        (physBranchOf D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
          f.val.variables g).threshold
        (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
          (sourceSizeExponent S D B) f.val.variables))
      (bound (itemWord D B f.val.variables g))) :
    (BitMachineComposition.composition Msrc
      (BitMachineComposition.composition (SourceListMachineOuterFramed.machine Titem)
        (SignedMidpointApproxActualMapper.satMachine M))).OutputsWithin
      (EncodedCNF.encode f.val) [EncodedETHTail.satAnswer (EncodedCNF.encode f.val)]
      (armTime S D B c M c' d' Titem bound T1 f) := by
  obtain ⟨herr', hgap, hyes, hno⟩ := phys_branches_semantics S D B c f hn hk hsource answer herr
  have hsat := SignedMidpointApproxActualMapper.sat_outputs_linear M c' d' answer hM
    (EncodedCNF.encode f.val)
    (physBranches S D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B) f)
    (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
      (sourceSizeExponent S D B) f.val.variables) _ herr' hgap hyes hno
  have hlist := phys_item_list S D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
    M f (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
      (sourceSizeExponent S D B) f.val.variables) Titem bound hitem
  rw [sourceList_eq] at hsrc
  have h2 := BitMachineComposition.composition_outputsWithin
    (SourceListMachineOuterFramed.machine Titem) (SignedMidpointApproxActualMapper.satMachine M)
    hlist hsat
  exact BitMachineComposition.composition_outputsWithin Msrc _ hsrc h2

/-- **hsrc discharged.** One fixed source machine from the admitted unit-1 endpoint
`source_effective`; for it, every H-B2 machine `Mtab` (`HB2Body`) and post machine `Mpost`
(`PostBody`) yield the ONE fixed main arm
`composition Msrc (composition (framed list mapper over composition Mtab Mpost) (satMachine M))`
answering `satAnswer` on every valid `f` with `1 ≤ n` and `1 ≤ L n`, within the explicit
`armTime` with `T1 = Csrc ⌈2^(η n)⌉ (|encode f|+1)^Esrc`. -/
theorem main_arm_endpoint :
    ∃ (Msrc : BitMachine.Machine) (Csrc Esrc : ℕ),
      ∀ (c : ℕ) (M : BitMachine.Machine) (c' d' : ℕ) (answer : List Bool → ℤ),
        M.ComputesWithin (fun table => EncodedETHTail.encodeInteger (answer table))
          (fun n => c' * (n + 1) ^ d') →
        (∀ b : EncodedETHTail.Branch, |answer b.table - (b.cost : ℤ)| ≤
          (FinalPadding.allowance (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
            (sourceSizeExponent S D B)) b.table.length : ℤ)) →
        2 ^ 44 * (B.degreeBound : ℚ) / sourceGap D B ≤ c →
        ∀ (Mtab : BitMachine.Machine) (C₂ E₂ F₂ : ℕ),
        HB2Body c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
          B.degreeBound (sourceGap D B) Mtab C₂ E₂ F₂ →
        ∀ (Mpost : BitMachine.Machine) (Cp Ep : ℕ), PostBody M Mpost Cp Ep →
        ∀ f : ValidFormula, 1 ≤ f.val.variables →
          1 ≤ ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
            (sourceSizeExponent S D B) f.val.variables →
          (BitMachineComposition.composition Msrc
            (BitMachineComposition.composition
              (SourceListMachineOuterFramed.machine
                (BitMachineComposition.composition Mtab Mpost))
              (SignedMidpointApproxActualMapper.satMachine M))).OutputsWithin
            (EncodedCNF.encode f.val) [EncodedETHTail.satAnswer (EncodedCNF.encode f.val)]
            (armTime S D B c M c' d' (BitMachineComposition.composition Mtab Mpost)
              (itemBound Mtab C₂ E₂ F₂ Cp Ep
                (FinalPadding.tableSize (ETHTailGrowth.repetitions c
                  (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)) f.val.variables))
              (Csrc * ⌈(2 : ℝ) ^ ((η : ℝ) * f.val.variables)⌉₊ *
                ((EncodedCNF.encode f.val).length + 1) ^ Esrc) f) := by
  obtain ⟨Msrc, Csrc, Esrc, hend⟩ := SourceGenericComposite.SourceEndpoint.source_effective S D B
  refine ⟨Msrc, Csrc, Esrc, ?_⟩
  intro c M c' d' answer hM herr hsource Mtab C₂ E₂ F₂ htab Mpost Cp Ep hpost f hn hk
  obtain ⟨hrun, heq, -, -, -⟩ := hend f hn
  rw [heq] at hrun
  exact phys_main_arm_outputs S D B c M c' d' answer hM herr hsource Msrc
    (BitMachineComposition.composition Mtab Mpost) _ _ f hn hk hrun
    (fun g hg => item_run S D B c M hsource Mtab C₂ E₂ F₂ htab Mpost Cp Ep hpost f hn hk g hg)

end Arm

end EthInapproximability.CurrentPaper.Unit4ItemAssembly
