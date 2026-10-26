import Paper2.A4T10Envelope
import Paper2.A4Shells

/-!
# Unit 4 (Paper A), segment A4-S3 residue: the T10 front reduced to generic glue

Owner lane `owner:a-unit4-shell-2` (private, 25 September 2026). Compiled `-WithB` (imports the
predecessor's frozen `A4T10Machine` through `A4T10Envelope`).

The predecessor's HYP interface `Shells.H_T10Front D B k` (charged glue from
`pair (encode Φ) tape` to the H-A3 bank `![encode (t10Graph D B Φ), 1^k, tape]`) is DERIVED here
from the checked chain `T10Machine.chain D B` (the D/B-specific part, charged by
`chain_outputs` and bounded by `T10Envelope.chainTime_poly`) and three GENERIC glue
contracts that mention neither `D`, `B`, nor any author decision:

* `H_PairMap` — the generic bit-machine combinator `pair x t ↦ pair (M x) t` (run a machine on
  the self-delimiting first field, keep the raw second field), with a polynomial clock in
  `M`'s time and the input length. It is NOT banked (the predecessor's A4-S6 notes the same
  missing combinator for `ReductionClosed`).
* `H_Packetizer` — one fixed machine `encode Φ ↦ packet Φ.variables (encode Φ)` on valid CNF
  (capture is banked: `SourceOriginalVariableCapture.canonical_outputs`; the packet writer is
  banked as a stack program: `SourceOriginalPacketWriter.unary_packet_run`; their join as one
  machine is not built).
* `H_BankOut k` — one fixed machine per `k`:
  `pair (packet n w) t ↦ encode ![w, 1^k, t]` (drop the unary field, add unary `k`).

All handoffs are charged by `BitMachineComposition.composition_outputsWithin`; every middle
word is bounded (packet/pair length identities and the banked `output_length_bound`).

**None of these statements closes a ledger row** (T10, T01 stay open).
-/

namespace Paper2.Unit4Shell.T10Front

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell.Poly
open Paper2.Unit4Shell.T10Finite

/-- GENERIC glue contract (machine model): the pair-map combinator. -/
def H_PairMap : Prop :=
  ∀ M : BitMachine.Machine, ∃ (M' : BitMachine.Machine) (C E : ℕ),
    ∀ (x y t : List Bool) (T : ℕ), M.OutputsWithin x y T →
      M'.OutputsWithin (EncodedComplexity.pair x t) (EncodedComplexity.pair y t)
        (C * (T + (EncodedComplexity.pair x t).length + 1) ^ E)

/-- GENERIC glue contract: one fixed packetizer on valid CNF. -/
def H_Packetizer : Prop :=
  ∃ (MP : BitMachine.Machine) (CP EP : ℕ), ∀ Φ : ValidFormula,
    MP.OutputsWithin (EncodedCNF.encode Φ.val)
      (SourceOriginalBranchPackets.packet Φ.val.variables (EncodedCNF.encode Φ.val))
      (CP * ((EncodedCNF.encode Φ.val).length + 1) ^ EP)

/-- GENERIC glue contract: one fixed bank assembler per `k`. -/
def H_BankOut (k : ℕ) : Prop :=
  ∃ (MB : BitMachine.Machine) (CB EB : ℕ), ∀ (n : ℕ) (w t : List Bool),
    MB.OutputsWithin (EncodedComplexity.pair (SourceOriginalBranchPackets.packet n w) t)
      (BitMachineBankCodec.encode ![w, List.replicate k true, t])
      (CB * ((EncodedComplexity.pair (SourceOriginalBranchPackets.packet n w) t).length + 1) ^ EB)

/-- Pull a `PolyIn` bound back along a map that does not increase size. -/
theorem polyIn_comp {ι κ : Type*} {szι : ι → ℕ} {szκ : κ → ℕ} (f : ι → κ) {a : κ → ℕ}
    (ha : PolyIn szκ a) (hf : ∀ i, szκ (f i) ≤ szι i) : PolyIn szι (fun i => a (f i)) := by
  obtain ⟨C, E, h⟩ := ha
  exact ⟨C, E, fun i => (h (f i)).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := hf i; omega) E))⟩

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- Size of the front input. -/
def X (p : ValidFormula × List Bool) : ℕ :=
  (EncodedComplexity.pair (EncodedCNF.encode p.1.val) p.2).length

theorem L_le_X (p : ValidFormula × List Bool) : T10Envelope.L p.1 ≤ X p := by
  simp only [X, T10Envelope.L, EncodedComplexity.pair_length]; omega

theorem tape_le_X (p : ValidFormula × List Bool) : p.2.length ≤ X p := by
  simp only [X, EncodedComplexity.pair_length]; omega

/-- **Front composition (fixed `k`).** From the three generic glue contracts and the checked
T10 chain, the predecessor's HYP interface `H_T10Front D B k` holds. Does not close a ledger
row. -/
theorem front_of_glue (hPM : H_PairMap) (hP : H_Packetizer) (k : ℕ) (hB : H_BankOut k) :
    Shells.H_T10Front D B k := by
  obtain ⟨MP, CP, EP, hMP⟩ := hP
  obtain ⟨M1, C1, E1, hM1⟩ := hPM MP
  obtain ⟨M2, C2, E2, hM2⟩ := hPM (T10Machine.chain D B)
  obtain ⟨MB, CB, EB, hMB⟩ := hB
  -- the middle words
  let mid1 : ValidFormula × List Bool → List Bool := fun p =>
    EncodedComplexity.pair
      (SourceOriginalBranchPackets.packet p.1.val.variables (EncodedCNF.encode p.1.val)) p.2
  let mid2 : ValidFormula × List Bool → List Bool := fun p =>
    EncodedComplexity.pair (SourceOriginalBranchPackets.packet p.1.val.variables
      (EncodedGraph.encode (t10Graph D B p.1))) p.2
  let T1 : ValidFormula × List Bool → ℕ := fun p =>
    C1 * (CP * ((EncodedCNF.encode p.1.val).length + 1) ^ EP + X p + 1) ^ E1
  let T2 : ValidFormula × List Bool → ℕ := fun p =>
    C2 * (T10Machine.chainTime D B p.1 + (mid1 p).length + 1) ^ E2
  let T3 : ValidFormula × List Bool → ℕ := fun p => CB * ((mid2 p).length + 1) ^ EB
  let total : ValidFormula × List Bool → ℕ := fun p =>
    T1 p + 2 * (mid1 p).length + 2 + (T2 p + 2 * (mid2 p).length + 2 + T3 p)
  -- polynomial bounds in X
  have hL : PolyIn X (fun p => T10Envelope.L p.1) := mono (fun p => L_le_X p) self
  have htape : PolyIn X (fun p => p.2.length) := mono (fun p => tape_le_X p) self
  have hx0 : PolyIn X (fun p => (SourceOriginalBranchPackets.sparsePacket p.1.val.variables
      p.1).length) := polyIn_comp Prod.fst T10Envelope.x0_poly (fun p => L_le_X p)
  have hmid1 : PolyIn X (fun p => (mid1 p).length) := by
    refine mono (fun p => ?_) (add (add (mul (const 2) hx0) (const 1)) htape)
    simp only [mid1, EncodedComplexity.pair_length, SourceOriginalBranchPackets.sparsePacket]
    omega
  have hout : PolyIn X (fun p => (SourceOriginalBranchPackets.packet p.1.val.variables
      (EncodedGraph.encode (t10Graph D B p.1))).length) :=
    polyIn_comp Prod.fst (T10Envelope.chainOutput_poly D B) (fun p => L_le_X p)
  have hmid2 : PolyIn X (fun p => (mid2 p).length) := by
    refine mono (fun p => ?_) (add (add (mul (const 2) hout) (const 1)) htape)
    simp only [mid2, EncodedComplexity.pair_length]
    omega
  have hchain : PolyIn X (fun p => T10Machine.chainTime D B p.1) :=
    polyIn_comp Prod.fst (T10Envelope.chainTime_poly D B) (fun p => L_le_X p)
  have hT1 : PolyIn X T1 :=
    mul (const _) (pow (add (add (mul (const _) (pow (add hL (const 1)) EP)) self) (const 1)) E1)
  have hT2 : PolyIn X T2 := mul (const _) (pow (add (add hchain hmid1) (const 1)) E2)
  have hT3 : PolyIn X T3 := mul (const _) (pow (add hmid2 (const 1)) EB)
  have htotal : PolyIn X total :=
    add (add (add hT1 (mul (const 2) hmid1)) (const 2))
      (add (add (add hT2 (mul (const 2) hmid2)) (const 2)) hT3)
  obtain ⟨CF, EF, hCF⟩ := htotal
  refine ⟨BitMachineComposition.composition M1 (BitMachineComposition.composition M2 MB),
    CF, EF, fun Φ t => ?_⟩
  set tb := (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    B.degreeBound (sourceGap D B) k).tapeBits t
  have h1 := hM1 (EncodedCNF.encode Φ.val)
    (SourceOriginalBranchPackets.packet Φ.val.variables (EncodedCNF.encode Φ.val)) tb _ (hMP Φ)
  have h2 := hM2 (SourceOriginalBranchPackets.packet Φ.val.variables (EncodedCNF.encode Φ.val))
    (SourceOriginalBranchPackets.packet Φ.val.variables (EncodedGraph.encode (t10Graph D B Φ)))
    tb _ (T10Machine.chain_outputs D B Φ)
  have h3 := hMB Φ.val.variables (EncodedGraph.encode (t10Graph D B Φ)) tb
  have hC := BitMachineComposition.composition_outputsWithin M1
    (BitMachineComposition.composition M2 MB) h1
    (BitMachineComposition.composition_outputsWithin M2 MB h2 h3)
  apply BitMachine.outputsWithin_mono _ hC
  exact hCF (Φ, tb)

end Paper2.Unit4Shell.T10Front
