import EthInapproximability.CurrentPaper.SourceGenericBooleanListMapper
import EthInapproximability.CurrentPaper.SourceOriginalDinurListMapper
import EthInapproximability.CurrentPaper.SourceOriginalBOTListMapper
import Paper2.A4T10Finite

/-!
# Unit 4 (Paper A), segment A4-S3 (machine part): the T10 packet chain through Paper B's
# generic-alphabet converter

Owner lane `owner:a-unit4-shell` (private, 25 September 2026). Compiled with the frozen
private objects of `b-source-generic-composite-owner-2` on LEAN_PATH (its `BooleanListMapper`
item machine is the lifted `ConverterMachine.machine D.alphabet D.arity D.arity_pos`, the
generic fixed-alphabet converter proved by `ConverterMachine.machine_dinur`; never `a = 2`).
Those objects are frozen, unaudited and not admitted.

One fixed machine per pair of cited records `(D, B)` (X03/X04, author decision D-A7), no
sparsifier: `(n, Φ) ↦ (n, CSP of D) ↦ (n, Boolean 3-CNF) ↦ (n, normalized BOT graph)`, each
handoff charged by `BitMachineComposition.composition_outputsWithin`. Input and output are the
two-field packets of `SourceOriginalBranchPackets` (field 0 = unary `n`, field 1 = bytes);
`n = Φ.variables` is the padding target of the normalization. The output graph is literally
`T10Finite.t10Graph D B Φ`.

NOT covered here (remaining, named): the front packetizer `encode Φ ↦ packet n (encode Φ)`
and malformed-input routing (validator B4-S1), the polynomial envelope of `chainTime` in
`|encode Φ|`, and the hand-off of the graph bytes into H-A3's input layout.

**None of these statements closes a ledger row** (T10, U18, X03, X04 stay open).
-/

namespace Paper2.Unit4Shell.T10Machine

open EthInapproximability.CurrentPaper

variable (D : EncodedETHSource.DinurReduction)
  (B : EncodedETHSource.BOTReduction (EncodedETHSourceComposition.booleanOccurrence D))

/-- The fixed T10 packet chain (DRAFT name). -/
noncomputable def chain : BitMachine.Machine :=
  BitMachineComposition.composition (SourceDinurPacketMachine.machine D)
    (BitMachineComposition.composition (SourceGenericComposite.BooleanListMapper.itemMachine D)
      (SourceBOTNormalizedPacketMachine.machine B))

/-- The literal charged clock: three stage clocks plus both charged handoffs. -/
noncomputable def chainTime (Φ : EncodedETHSource.ValidFormula) : ℕ :=
  SourceOriginalDinurListMapper.itemBound D
      (SourceOriginalBranchPackets.sparsePacket Φ.val.variables Φ) +
    2 * (SourceOriginalDinurListMapper.cspPacket D Φ.val.variables Φ).length + 2 +
    (SourceGenericComposite.BooleanListMapper.itemBound D
        (SourceOriginalDinurListMapper.cspPacket D Φ.val.variables Φ) +
      2 * (SourceGenericComposite.BooleanListMapper.boolPacket D Φ.val.variables Φ).length + 2 +
      SourceOriginalBOTListMapper.itemBound B
        (SourceGenericComposite.BooleanListMapper.boolPacket D Φ.val.variables Φ))

/-- **T10 packet chain.** On the packet of any valid 3-CNF `Φ`, the one fixed machine
`chain D B` outputs exactly the packet of the semantic T10 graph `t10Graph D B Φ` (whose
finite source properties are `T10Finite.t10_source`) within the literal charged clock.
Does not close a ledger row. -/
theorem chain_outputs (Φ : EncodedETHSource.ValidFormula) :
    (chain D B).OutputsWithin
      (SourceOriginalBranchPackets.packet Φ.val.variables (EncodedCNF.encode Φ.val))
      (SourceOriginalBranchPackets.packet Φ.val.variables
        (EncodedGraph.encode (T10Finite.t10Graph D B Φ)))
      (chainTime D B Φ) := by
  have h1 := SourceOriginalDinurListMapper.item_run D Φ Φ.val.variables
  have h2 := SourceGenericComposite.BooleanListMapper.item_run D Φ.val.variables Φ
  have h3 := SourceOriginalBOTListMapper.item_run B
    (EncodedETHSourceComposition.booleanFormula D Φ) Φ.val.variables
  exact BitMachineComposition.composition_outputsWithin _ _ h1
    (BitMachineComposition.composition_outputsWithin _ _ h2 h3)

end Paper2.Unit4Shell.T10Machine
