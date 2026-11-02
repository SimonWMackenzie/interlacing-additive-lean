import Paper2.A4ShellsTight
import Paper2.A4BankOutU

/-!
# Unit 4 (Paper A), N-4: the `k`-UNIFORM T10 front and the `k`-uniform T01 machine

Owner lane `owner:a-unit4-shell-4` (private, 26 September 2026).

Lock v12 `thm:uniform-reduction` (06-reduction.tex:26-41): ONE algorithm taking `k` as input,
running time and random bits `n^{O(k+1)}` "with an absolute exponent independent of k". The
admitted fixed-`k` interface `Shells.H_T10Front D B k` has one machine per `k` (through
`BankOut.machine k`). This module states and proves the NEW interface `H_T10FrontUniform D B`:
ONE fixed machine `MF` and absolute `CF`, `EF` such that for EVERY `k`, every valid `Φ` and
every tape `t` of the selected law at gap `k`, on the literal word
`pair (encode Φ) (pair (1^k) (tapeBits t))` it prints the literal H-A3 bank
`encode ![encode (t10Graph D B Φ), 1^k, tapeBits t]` within `CF·(|input| + 1)^EF`.

Input layout (a PROPOSAL of this lane, not an author decision D-A*): the unary gap `k` is the
self-delimiting field between the formula field and the raw tape bits. It is literally the
bank layout that H-A3 already consumes (`1^k` as a field), so no conversion is hidden.

Machine: `composition (PairMap packetizer) (composition (PairMap (T10Machine.chain D B))
BankOutU.machine)`. The two `PairMap` stages keep the raw suffix `pair (1^k) tape` in place;
`BankOutU.machine` READS the unary `k` from its input. Every handoff is charged by the admitted
`BitMachineComposition.composition_outputsWithin`; every middle word is bounded.

Composed with the unit-3 endpoint `H_A3` (a HYPOTHESIS, whose machine is already `k`-uniform
with clock `CA·(n+2)^(EA·(k+1))`), `T01_uniform` gives ONE machine for all `k ≥ 1` with clock
`(C0 + CA·CS^(EA·(k+1)))·(|input|+1)^(E0 + ES·(EA·(k+1)))`, every constant absolute.

**No ledger row is closed.** `D` (X03), `B` (X04) are parameters (D-A7); valid `Φ` only; the
tape law is the constructor's `select` law (D-A1 untouched).
-/

namespace Paper2.Unit4Shell.FrontUniform

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell.Poly
open Paper2.Unit4Shell.T10Finite

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- NEW interface (N-4): the `k`-uniform charged T10 front. ONE machine for every `k`. -/
def H_T10FrontUniform : Prop :=
  ∃ (MF : BitMachine.Machine) (CF EF : ℕ), ∀ (k : ℕ) (Φ : ValidFormula)
    (t : (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
      B.degreeBound (sourceGap D B) k).Tape),
    MF.OutputsWithin
      (EncodedComplexity.pair (EncodedCNF.encode Φ.val)
        (EncodedComplexity.pair (List.replicate k true)
          ((TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
            (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
            B.degreeBound (sourceGap D B) k).tapeBits t)))
      (BitMachineBankCodec.encode ![EncodedGraph.encode (t10Graph D B Φ),
        List.replicate k true,
        (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
          (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
          B.degreeBound (sourceGap D B) k).tapeBits t])
      (CF * ((EncodedComplexity.pair (EncodedCNF.encode Φ.val)
        (EncodedComplexity.pair (List.replicate k true)
          ((TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
            (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
            B.degreeBound (sourceGap D B) k).tapeBits t))).length + 1) ^ EF)

/-- **Raw-suffix form of the uniform front.** ONE machine; for every `k`, every valid `Φ` and
EVERY raw suffix `tb`, `pair (encode Φ) (pair (1^k) tb) ↦ encode ![encode (t10Graph D B Φ),
1^k, tb]` within `CF·(|input|+1)^EF`. Does not close a ledger row. -/
theorem front_uniform_raw :
    ∃ (MF : BitMachine.Machine) (CF EF : ℕ), ∀ (k : ℕ) (Φ : ValidFormula) (tb : List Bool),
      MF.OutputsWithin
        (EncodedComplexity.pair (EncodedCNF.encode Φ.val)
          (EncodedComplexity.pair (List.replicate k true) tb))
        (BitMachineBankCodec.encode ![EncodedGraph.encode (t10Graph D B Φ),
          List.replicate k true, tb])
        (CF * ((EncodedComplexity.pair (EncodedCNF.encode Φ.val)
          (EncodedComplexity.pair (List.replicate k true) tb)).length + 1) ^ EF) := by
  obtain ⟨MP, CP, EP, hMP⟩ := PairMapGlue.H_Packetizer_holds
  obtain ⟨M1, C1, E1, hM1⟩ := PairMap.pair_map MP
  obtain ⟨M2, C2, E2, hM2⟩ := PairMap.pair_map (T10Machine.chain D B)
  -- the middle words, for an arbitrary raw suffix `p.2`
  let mid1 : ValidFormula × List Bool → List Bool := fun p =>
    EncodedComplexity.pair
      (SourceOriginalBranchPackets.packet p.1.val.variables (EncodedCNF.encode p.1.val)) p.2
  let mid2 : ValidFormula × List Bool → List Bool := fun p =>
    EncodedComplexity.pair (SourceOriginalBranchPackets.packet p.1.val.variables
      (EncodedGraph.encode (t10Graph D B p.1))) p.2
  let T1 : ValidFormula × List Bool → ℕ := fun p =>
    C1 * (CP * ((EncodedCNF.encode p.1.val).length + 1) ^ EP + T10Front.X p + 1) ^ E1
  let T2 : ValidFormula × List Bool → ℕ := fun p =>
    C2 * (T10Machine.chainTime D B p.1 + (mid1 p).length + 1) ^ E2
  let T3 : ValidFormula × List Bool → ℕ := fun p => 10 * ((mid2 p).length + 1)
  let total : ValidFormula × List Bool → ℕ := fun p =>
    T1 p + 2 * (mid1 p).length + 2 + (T2 p + 2 * (mid2 p).length + 2 + T3 p)
  have hL : PolyIn T10Front.X (fun p => T10Envelope.L p.1) :=
    mono (fun p => T10Front.L_le_X p) self
  have htape : PolyIn T10Front.X (fun p => p.2.length) := mono (fun p => T10Front.tape_le_X p) self
  have hx0 : PolyIn T10Front.X (fun p => (SourceOriginalBranchPackets.sparsePacket
      p.1.val.variables p.1).length) :=
    T10Front.polyIn_comp Prod.fst T10Envelope.x0_poly (fun p => T10Front.L_le_X p)
  have hmid1 : PolyIn T10Front.X (fun p => (mid1 p).length) := by
    refine mono (fun p => ?_) (add (add (mul (const 2) hx0) (const 1)) htape)
    simp only [mid1, EncodedComplexity.pair_length, SourceOriginalBranchPackets.sparsePacket]
    omega
  have hout : PolyIn T10Front.X (fun p => (SourceOriginalBranchPackets.packet p.1.val.variables
      (EncodedGraph.encode (t10Graph D B p.1))).length) :=
    T10Front.polyIn_comp Prod.fst (T10Envelope.chainOutput_poly D B)
      (fun p => T10Front.L_le_X p)
  have hmid2 : PolyIn T10Front.X (fun p => (mid2 p).length) := by
    refine mono (fun p => ?_) (add (add (mul (const 2) hout) (const 1)) htape)
    simp only [mid2, EncodedComplexity.pair_length]
    omega
  have hchain : PolyIn T10Front.X (fun p => T10Machine.chainTime D B p.1) :=
    T10Front.polyIn_comp Prod.fst (T10Envelope.chainTime_poly D B) (fun p => T10Front.L_le_X p)
  have hT1 : PolyIn T10Front.X T1 :=
    mul (const _) (pow (add (add (mul (const _) (pow (add hL (const 1)) EP)) self) (const 1)) E1)
  have hT2 : PolyIn T10Front.X T2 := mul (const _) (pow (add (add hchain hmid1) (const 1)) E2)
  have hT3 : PolyIn T10Front.X T3 := mul (const _) (add hmid2 (const 1))
  have htotal : PolyIn T10Front.X total :=
    add (add (add hT1 (mul (const 2) hmid1)) (const 2))
      (add (add (add hT2 (mul (const 2) hmid2)) (const 2)) hT3)
  obtain ⟨CF, EF, hCF⟩ := htotal
  refine ⟨BitMachineComposition.composition M1
    (BitMachineComposition.composition M2 BankOutU.machine), CF, EF, fun k Φ tb => ?_⟩
  set s := EncodedComplexity.pair (List.replicate k true) tb with hs
  have h1 := hM1 (EncodedCNF.encode Φ.val)
    (SourceOriginalBranchPackets.packet Φ.val.variables (EncodedCNF.encode Φ.val)) s _ (hMP Φ)
  have h2 := hM2 (SourceOriginalBranchPackets.packet Φ.val.variables (EncodedCNF.encode Φ.val))
    (SourceOriginalBranchPackets.packet Φ.val.variables (EncodedGraph.encode (t10Graph D B Φ)))
    s _ (T10Machine.chain_outputs D B Φ)
  have h3 := BankOutU.machine_outputs k Φ.val.variables (EncodedGraph.encode (t10Graph D B Φ)) tb
  have hC := BitMachineComposition.composition_outputsWithin M1
    (BitMachineComposition.composition M2 BankOutU.machine) h1
    (BitMachineComposition.composition_outputsWithin M2 BankOutU.machine h2 h3)
  apply BitMachine.outputsWithin_mono _ hC
  exact hCF (Φ, s)

/-- **N-4 closed at the interface level: the `k`-uniform T10 front holds.** Does not close a
ledger row. -/
theorem H_T10FrontUniform_holds : H_T10FrontUniform D B := by
  obtain ⟨MF, CF, EF, h⟩ := front_uniform_raw D B
  exact ⟨MF, CF, EF, fun k Φ t => h k Φ _⟩

private theorem pow_mono_base {a b e : ℕ} (h : a ≤ b) : a ^ e ≤ b ^ e := Nat.pow_le_pow_left h e

private theorem pow_le_pow_of_le {x a b : ℕ} (h : a ≤ b) : (x + 1) ^ a ≤ (x + 1) ^ b :=
  Nat.pow_le_pow_right (Nat.succ_pos x) h

/-- Pure arithmetic of the composed clock (verbatim copy of the private `Shells.budget` of the
admitted `A4Shells`, renamed; private declarations are not importable). -/
theorem budgetU (x y m V CF EF pb CA CS ES EA k : ℕ)
    (hxy : y ≤ x) (hm : m ≤ x + CF * (x + 1) ^ EF * pb)
    (hV : V + 2 ≤ CS * (y + 1) ^ ES) :
    CF * (x + 1) ^ EF + 2 * m + 2 + CA * (V + 2) ^ (EA * (k + 1)) ≤
      (CF + 2 * (1 + CF * pb) + 2 + CA * CS ^ (EA * (k + 1))) *
        (x + 1) ^ (EF + ES * (EA * (k + 1)) + 1) := by
  set E := EF + ES * (EA * (k + 1)) + 1
  have hP1 : (x + 1) ^ EF ≤ (x + 1) ^ E := pow_le_pow_of_le (by omega)
  have hPx : x + 1 ≤ (x + 1) ^ E := by
    calc x + 1 = (x + 1) ^ 1 := (pow_one _).symm
      _ ≤ (x + 1) ^ E := pow_le_pow_of_le (by omega)
  have hV' : V + 2 ≤ CS * (x + 1) ^ ES :=
    hV.trans (Nat.mul_le_mul_left _ (pow_mono_base (by omega)))
  have hVpow : (V + 2) ^ (EA * (k + 1)) ≤ CS ^ (EA * (k + 1)) * (x + 1) ^ E := by
    calc (V + 2) ^ (EA * (k + 1))
        ≤ (CS * (x + 1) ^ ES) ^ (EA * (k + 1)) := pow_mono_base hV'
      _ = CS ^ (EA * (k + 1)) * (x + 1) ^ (ES * (EA * (k + 1))) := by
        rw [mul_pow, ← pow_mul]
      _ ≤ CS ^ (EA * (k + 1)) * (x + 1) ^ E :=
        Nat.mul_le_mul_left _ (pow_le_pow_of_le (by omega))
  have hF' : CF * (x + 1) ^ EF ≤ CF * (x + 1) ^ E := Nat.mul_le_mul_left _ hP1
  have hFpb : CF * (x + 1) ^ EF * pb ≤ CF * pb * (x + 1) ^ E := by
    have := Nat.mul_le_mul_right pb hF'
    calc CF * (x + 1) ^ EF * pb ≤ CF * (x + 1) ^ E * pb := this
      _ = CF * pb * (x + 1) ^ E := by ring
  have hm' : m ≤ (1 + CF * pb) * (x + 1) ^ E := by
    calc m ≤ x + CF * (x + 1) ^ EF * pb := hm
      _ ≤ (x + 1) ^ E + CF * pb * (x + 1) ^ E := by omega
      _ = (1 + CF * pb) * (x + 1) ^ E := by ring
  have hA' : CA * (V + 2) ^ (EA * (k + 1)) ≤ CA * CS ^ (EA * (k + 1)) * (x + 1) ^ E := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hVpow
  have h1E : 1 ≤ (x + 1) ^ E := Nat.one_le_pow _ _ (Nat.succ_pos x)
  have hexp : (CF + 2 * (1 + CF * pb) + 2 + CA * CS ^ (EA * (k + 1))) * (x + 1) ^ E =
      CF * (x + 1) ^ E + 2 * ((1 + CF * pb) * (x + 1) ^ E) + 2 * (x + 1) ^ E +
        CA * CS ^ (EA * (k + 1)) * (x + 1) ^ E := by ring
  rw [hexp]
  omega

/-- **T01, `k`-uniform machine side (HYP on H-A3 only).** ONE fixed machine `M` and ABSOLUTE
constants `C0 CA CS E0 ES EA` (independent of `k`) such that for every `k ≥ 1`, every valid `Φ`
and every tape `t` of the selected law at gap `k`, on the literal word
`pair (encode Φ) (pair (1^k) (tapeBits t))` the machine prints exactly
`EncodedSelectedOutput.outputBits … k t` within
`(C0 + CA·CS^(EA·(k+1)))·(|input| + 1)^(E0 + ES·(EA·(k+1)))`, i.e. `n^{O(k+1)}` with an absolute
exponent. The YES/NO guarantees are those of `ShellsTight.T01_tight` at the same `k` (same
`outputBits`, same `select` law). Remaining hypothesis: `hA3` (unit 3). Does not close a ledger
row (T01, T23). -/
theorem T01_uniform (hA3 : Shells.H_A3 B.degreeBound (sourceGap D B)) :
    ∃ (M : BitMachine.Machine) (C0 CA CS E0 ES EA : ℕ), ∀ (k : ℕ), 1 ≤ k →
      ∀ (Φ : ValidFormula) (t : (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
        B.degreeBound (sourceGap D B) k).Tape),
      M.OutputsWithin
        (EncodedComplexity.pair (EncodedCNF.encode Φ.val)
          (EncodedComplexity.pair (List.replicate k true)
            ((TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
              (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
              B.degreeBound (sourceGap D B) k).tapeBits t)))
        (EncodedSelectedOutput.outputBits (t10_vertices_pos D B Φ)
          (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
          B.degreeBound (sourceGap D B) k t)
        ((C0 + CA * CS ^ (EA * (k + 1))) *
          ((EncodedComplexity.pair (EncodedCNF.encode Φ.val)
            (EncodedComplexity.pair (List.replicate k true)
              ((TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
                (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
                B.degreeBound (sourceGap D B) k).tapeBits t))).length + 1) ^
            (E0 + ES * (EA * (k + 1)))) := by
  obtain ⟨MA, CA, EA, hMA⟩ := hA3
  obtain ⟨MF, CF, EF, hMF⟩ := H_T10FrontUniform_holds D B
  obtain ⟨CS, ES, hS⟩ := T10Size.H_T10Size_holds D B
  refine ⟨BitMachineComposition.composition MF MA, CF + 2 * (1 + CF * MF.pushBound) + 2,
    CA, CS, EF + 1, ES, EA, fun k hk Φ t => ?_⟩
  obtain ⟨hm, _, hinc, hdeg, _, _, _⟩ := t10_source D B Φ
  have hF := hMF k Φ t
  have hA := hMA (t10Graph D B Φ) (t10Graph_valid D B Φ) (t10_vertices_pos D B Φ) k hk
    hinc hdeg t
  have hC := BitMachineComposition.composition_outputsWithin MF MA hF hA
  apply BitMachine.outputsWithin_mono _ hC
  have hb := budgetU _ _ _ _ CF EF MF.pushBound CA CS ES EA k
    (by simp only [EncodedComplexity.pair_length]; omega)
    (BitMachine.output_length_bound MF hF) (hS Φ)
  have he : EF + ES * (EA * (k + 1)) + 1 = EF + 1 + ES * (EA * (k + 1)) := by ring
  rw [he] at hb
  exact hb

#print axioms front_uniform_raw
#print axioms H_T10FrontUniform_holds
#print axioms budgetU
#print axioms T01_uniform

end Paper2.Unit4Shell.FrontUniform
