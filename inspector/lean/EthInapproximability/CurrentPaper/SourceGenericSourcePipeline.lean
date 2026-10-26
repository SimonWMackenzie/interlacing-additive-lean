import EthInapproximability.CurrentPaper.SourceGenericBooleanListMapper
import EthInapproximability.CurrentPaper.SourceOriginalDinurPrefixMachine

/-!
# The composed source pipeline: sparsification, Dinur, Boolean, BOT, normalization

Paper B, locked v8 Section 6 (`thm:paper-sparse-gap-source`) and Appendix B;
CP-SOURCE-EFFECTIVE. The ledger's required path
`S.branches -> Dinur -> Boolean CSP-to-three-CNF -> BOT -> normalization`
as ONE fixed composed `BitMachine.Machine`, fixed by `(S, D, B)` before the
input formula:

1. admitted `SourceOriginalDinurPrefixMachine.machine S D` (cited sparsifier,
   original-`n` packetizer, cited Dinur machine per branch);
2. `BooleanListMapper.machine D` (the fixed generic converter at
   `(D.alphabet, D.arity)` per branch, on proved-valid Dinur outputs only);
3. admitted `SourceOriginalBOTCanonicalListMapper.machine B` (cited BOT machine
   and the checked ordered normalizer at the original `n`, per branch).

Every handoff is the admitted `BitMachineComposition.composition` transfer,
charged `2*|middle|+2` steps. The output is literally the consumer object
`EncodedETHSourceComposition.sourceGraphs S D B f`, serialized as original-`n`
packets. Segment 2 bank facts (list header, packet banks, original `n`,
actual graph bytes) are proved below.
-/

namespace EthInapproximability.CurrentPaper.SourceGenericComposite.SourcePipeline

open BitMachine BitMachineEncoding EncodedCommunication

variable {η : ℚ} (S : EncodedETHSource.Sparsification η)
  (D : EncodedETHSource.DinurReduction)
  (B : EncodedETHSource.BOTReduction (EncodedETHSourceComposition.booleanOccurrence D))

noncomputable def tailMachine : BitMachine.Machine :=
  BitMachineComposition.composition (BooleanListMapper.machine D)
    (SourceOriginalBOTCanonicalListMapper.machine B)

/-- THE fixed source-pipeline machine. -/
noncomputable def machine : BitMachine.Machine :=
  BitMachineComposition.composition (SourceOriginalDinurPrefixMachine.machine S D)
    (tailMachine D B)

noncomputable def tailTime (f : EncodedETHSource.ValidFormula) : Nat :=
  BooleanListMapper.mapTime D S f +
    2 * (SourceOriginalBOTSourceTarget.booleanPacketList S D f).length + 2 +
    SourceOriginalBOTCanonicalListMapper.mapTime B f.val.variables
      (EncodedETHSourceComposition.booleanBranches S D f)

noncomputable def totalTime (f : EncodedETHSource.ValidFormula) : Nat :=
  SourceOriginalDinurPrefixMachine.totalTime S D f +
    2 * (SourceOriginalDinurListMapper.outputList S D f).length + 2 +
    tailTime S D B f

theorem tail_outputs (f : EncodedETHSource.ValidFormula) :
    (tailMachine D B).OutputsWithin
      (SourceOriginalDinurListMapper.outputList S D f)
      (SourceOriginalBOTSourceTarget.normalizedGraphPacketList S D B f)
      (tailTime S D B f) :=
  BitMachineComposition.composition_outputsWithin _ _
    (BooleanListMapper.mapped_outputs D S f)
    (SourceOriginalBOTSourceTarget.canonical_map S D B f)

/-- One fixed machine: original CNF bits to the normalized original-`n`
graph packet list of every sparse branch. -/
theorem pipeline_outputs (f : EncodedETHSource.ValidFormula) :
    (machine S D B).OutputsWithin (EncodedCNF.encode f.val)
      (SourceOriginalBOTSourceTarget.normalizedGraphPacketList S D B f)
      (totalTime S D B f) :=
  BitMachineComposition.composition_outputsWithin _ _
    (SourceOriginalDinurPrefixMachine.canonical_outputsWithin S D f)
    (tail_outputs S D B f)

/-- The output packet list of the consumer object itself. -/
noncomputable def graphPackets (f : EncodedETHSource.ValidFormula) : List (List Bool) :=
  (EncodedETHSourceComposition.sourceGraphs S D B f).map fun g =>
    SourceOriginalBranchPackets.packet f.val.variables (EncodedGraph.encode g.val)

theorem pipeline_sourceGraphs (f : EncodedETHSource.ValidFormula) :
    (machine S D B).OutputsWithin (EncodedCNF.encode f.val)
      (SourceListEncoding.encode (graphPackets S D B f)) (totalTime S D B f) := by
  have h := pipeline_outputs S D B f
  rwa [SourceOriginalBOTSourceTarget.normalizedGraphPacketList_sourceGraphs] at h

/-! ## Segment 2: raw headers, actual graph bytes, original `n` (bank facts) -/

theorem graphPackets_length (f : EncodedETHSource.ValidFormula) :
    (graphPackets S D B f).length = (S.branches f).length := by
  simp [graphPackets, EncodedETHSourceComposition.sourceGraphs,
    EncodedETHSource.BOTReduction.graphList_count,
    EncodedETHSourceComposition.booleanBranches]

/-- The raw list header is the binary field of the ORIGINAL formula's sparse
branch count, followed by the framed packets. -/
theorem output_header (f : EncodedETHSource.ValidFormula) :
    SourceListEncoding.encode (graphPackets S D B f) =
      natField (S.branches f).length ++ SourceListEncoding.fields (graphPackets S D B f) := by
  rw [SourceListEncoding.encode, graphPackets_length]

theorem output_decode (f : EncodedETHSource.ValidFormula) :
    SourceListEncoding.decode (SourceListEncoding.encode (graphPackets S D B f)) =
      some (graphPackets S D B f) :=
  SourceListEncoding.decode_encode _

theorem bank_zero (n : Nat) (word : List Bool) :
    SourceOriginalBranchPackets.bank n word 0 = List.replicate n true := rfl

theorem bank_one (n : Nat) (word : List Bool) :
    SourceOriginalBranchPackets.bank n word 1 = word := rfl

/-- Original-`n` preservation and actual graph bytes, as a bank fact on every
output packet: field 0 is `true^n` for the ORIGINAL variable count
`n = f.val.variables` (not a branch-local or graph-local count), field 1 is
the literal `EncodedGraph.encode` of the consumer graph, which parses back. -/
theorem output_packet_banks (f : EncodedETHSource.ValidFormula) :
    ∀ x ∈ graphPackets S D B f,
      ∃ g ∈ EncodedETHSourceComposition.sourceGraphs S D B f,
        BitMachineBankCodec.decode 2 x =
          some (SourceOriginalBranchPackets.bank f.val.variables (EncodedGraph.encode g.val)) ∧
        SourceOriginalBranchPackets.bank f.val.variables (EncodedGraph.encode g.val) 0 =
          List.replicate f.val.variables true ∧
        SourceOriginalBranchPackets.bank f.val.variables (EncodedGraph.encode g.val) 1 =
          EncodedGraph.encode g.val ∧
        EncodedGraph.decode (EncodedGraph.encode g.val) = some g.val := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
  exact ⟨g, hg, SourceOriginalBranchPackets.packet_decode _ _, rfl, rfl,
    EncodedGraph.decode_encode g.val g.property⟩

/-- The same original `n` is carried through all three stages: the Dinur
stage (cited CSP bits), the Boolean stage (the consumer `booleanFormula`)
and the BOT/normalization stage (normalized at that same `n`). -/
theorem stage_packet_banks (f : EncodedETHSource.ValidFormula)
    (g : EncodedETHSource.ValidFormula) :
    BitMachineBankCodec.decode 2 (SourceOriginalDinurListMapper.cspPacket D f.val.variables g) =
        some (SourceOriginalBranchPackets.bank f.val.variables
          (EncodedETHSource.constraintBits (D.reduce g))) ∧
      BitMachineBankCodec.decode 2 (BooleanListMapper.boolPacket D f.val.variables g) =
        some (SourceOriginalBranchPackets.bank f.val.variables
          (EncodedCNF.encode (EncodedETHSourceComposition.booleanFormula D g).val)) ∧
      BitMachineBankCodec.decode 2 (SourceOriginalBOTListMapper.normalizedPacket B
          f.val.variables (EncodedETHSourceComposition.booleanFormula D g)) =
        some (SourceOriginalBranchPackets.bank f.val.variables
          (EncodedGraph.encode (B.output (EncodedETHSourceComposition.booleanFormula D g).val
            (EncodedETHSourceComposition.booleanFormula D g).property f.val.variables))) :=
  ⟨SourceOriginalBranchPackets.packet_decode _ _,
   SourceOriginalBranchPackets.packet_decode _ _,
   SourceOriginalBranchPackets.packet_decode _ _⟩

/-- The graph list really is the consumer's ordered list: the `i`-th output
packet is the `i`-th sparse branch, through Dinur, Boolean and BOT, normalized
at the original `n`. -/
theorem graphPackets_eq (f : EncodedETHSource.ValidFormula) :
    graphPackets S D B f =
      (S.branches f).map fun g =>
        SourceOriginalBOTListMapper.normalizedPacket B f.val.variables
          (EncodedETHSourceComposition.booleanFormula D g) := by
  simp only [graphPackets, EncodedETHSourceComposition.sourceGraphs,
    EncodedETHSource.BOTReduction.graphList, EncodedETHSourceComposition.booleanBranches,
    List.map_map]
  rfl

#print axioms tail_outputs
#print axioms pipeline_outputs
#print axioms pipeline_sourceGraphs
#print axioms graphPackets_length
#print axioms output_header
#print axioms output_decode
#print axioms output_packet_banks
#print axioms stage_packet_banks
#print axioms graphPackets_eq

end EthInapproximability.CurrentPaper.SourceGenericComposite.SourcePipeline
