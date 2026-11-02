import EthInapproximability.CurrentPaper.SourceGenericPipelineClock

/-!
# Unit 1 endpoint against the named consumer (segment 5)

Paper B, locked v8 Section 6 (`thm:paper-sparse-gap-source`) and Appendix B;
CP-SOURCE-EFFECTIVE.

Quantifier order (the paper's): the cited records `S` (sparsification at `η`),
`D` (Dinur), `B` (BOT at `booleanOccurrence D`) are fixed first; then ONE machine
and its constants are chosen; only then the input formula `f`. The Boolean
stage outputs the consumer object `EncodedETHSourceComposition.booleanFormula D g`
itself for every branch `g`, and the whole source machine outputs the literal
ordered list `EncodedETHSourceComposition.sourceGraphs S D B f` (normalized at the
ORIGINAL `n`), about which the admitted finite theorems `source_count`,
`source_yes`, `source_no` speak — the same object.
-/

namespace EthInapproximability.CurrentPaper.SourceGenericComposite.SourceEndpoint

open EncodedETHSource

variable {η : ℚ} (S : Sparsification η) (D : DinurReduction)
  (B : BOTReduction (EncodedETHSourceComposition.booleanOccurrence D))

/-- The Boolean stage alone: one fixed machine at `(D.alphabet, D.arity)`,
clock in the ORIGINAL (sparse-branch) formula length through `D.polytime`. -/
theorem boolean_stage :
    ∃ (M : BitMachine.Machine) (C E : ℕ), ∀ f : ValidFormula,
      M.OutputsWithin (D.bitFunction (EncodedCNF.encode f.val))
        (EncodedCNF.encode (EncodedETHSourceComposition.booleanFormula D f).val)
        (C * ((EncodedCNF.encode f.val).length + 1) ^ E) := by
  obtain ⟨N, c, d, hN⟩ := D.polytime
  refine ⟨ConverterMachine.machine D.alphabet D.arity D.arity_pos,
    Converter.convC D.alphabet D.arity * (1 + c * N.pushBound) ^ 27, 27 * (d + 1),
    fun f => ?_⟩
  have hrun := ConverterMachine.machine_dinur_bits D f
  apply BitMachine.outputsWithin_mono _ hrun
  set x := EncodedCNF.encode f.val
  set y := D.bitFunction x
  have hlen : y.length ≤ x.length + c * (x.length + 1) ^ d * N.pushBound :=
    BitMachine.output_length_bound N (hN x)
  have hX : 1 ≤ x.length + 1 := by omega
  have h1 : x.length + 1 ≤ (x.length + 1) ^ (d + 1) := by
    calc x.length + 1 = (x.length + 1) ^ 1 := (pow_one _).symm
      _ ≤ (x.length + 1) ^ (d + 1) := Nat.pow_le_pow_right hX (by omega)
  have h2 : (x.length + 1) ^ d ≤ (x.length + 1) ^ (d + 1) :=
    Nat.pow_le_pow_right hX (by omega)
  have hy : y.length + 1 ≤ (1 + c * N.pushBound) * (x.length + 1) ^ (d + 1) := by
    have h3 : c * (x.length + 1) ^ d * N.pushBound ≤
        c * N.pushBound * (x.length + 1) ^ (d + 1) := by
      calc c * (x.length + 1) ^ d * N.pushBound = c * N.pushBound * (x.length + 1) ^ d := by
            ring
        _ ≤ c * N.pushBound * (x.length + 1) ^ (d + 1) := Nat.mul_le_mul_left _ h2
    have e : (1 + c * N.pushBound) * (x.length + 1) ^ (d + 1) =
        (x.length + 1) ^ (d + 1) + c * N.pushBound * (x.length + 1) ^ (d + 1) := by ring
    rw [e]
    omega
  calc Converter.convC D.alphabet D.arity * (y.length + 1) ^ 27
      ≤ Converter.convC D.alphabet D.arity *
          ((1 + c * N.pushBound) * (x.length + 1) ^ (d + 1)) ^ 27 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hy 27)
    _ = Converter.convC D.alphabet D.arity * (1 + c * N.pushBound) ^ 27 *
          (x.length + 1) ^ (27 * (d + 1)) := by
        rw [mul_pow, ← pow_mul]; ring

/-- **Unit 1 endpoint (CP-SOURCE-EFFECTIVE, cited composition).** For the fixed
cited records, one fixed machine and constants exist such that every valid
formula with at least one variable is mapped, within
`C * ceil(2^(eta*n)) * (|input|+1)^E` steps, to the ordered original-`n` packet
list whose `i`-th item is the BOT-normalized graph of the consumer object
`booleanFormula D g` for the `i`-th sparse branch `g`; this is literally the
packet list of `sourceGraphs S D B f`, whose count, YES and NO properties are
the admitted finite theorems. -/
theorem source_effective :
    ∃ (M : BitMachine.Machine) (C E : ℕ), ∀ f : ValidFormula, 1 ≤ f.val.variables →
      M.OutputsWithin (EncodedCNF.encode f.val)
        (SourceListEncoding.encode ((S.branches f).map fun g =>
          SourceOriginalBOTListMapper.normalizedPacket B f.val.variables
            (EncodedETHSourceComposition.booleanFormula D g)))
        (C * ⌈(2 : ℝ) ^ ((η : ℝ) * f.val.variables)⌉₊ *
          ((EncodedCNF.encode f.val).length + 1) ^ E) ∧
      ((S.branches f).map fun g =>
          SourceOriginalBOTListMapper.normalizedPacket B f.val.variables
            (EncodedETHSourceComposition.booleanFormula D g)) =
        (EncodedETHSourceComposition.sourceGraphs S D B f).map (fun g =>
          SourceOriginalBranchPackets.packet f.val.variables (EncodedGraph.encode g.val)) ∧
      (((EncodedETHSourceComposition.sourceGraphs S D B f).length : ℝ) ≤
        (2 : ℝ) ^ ((η : ℝ) * f.val.variables)) ∧
      (EncodedCNF.Satisfiable f.val →
        ∃ g ∈ EncodedETHSourceComposition.sourceGraphs S D B f,
          (rawGraph g.val g.property).Colourable) ∧
      (¬ EncodedCNF.Satisfiable f.val →
        ∀ g ∈ EncodedETHSourceComposition.sourceGraphs S D B f,
          (rawGraph g.val g.property).Gap (EncodedETHSourceComposition.sourceGap D B)) := by
  obtain ⟨C, E, h⟩ := PipelineClock.pipeline_outputs_clock S D B
  refine ⟨SourcePipeline.machine S D B, C, E, fun f hn => ?_⟩
  have heq := SourcePipeline.graphPackets_eq S D B f
  refine ⟨?_, heq.symm, EncodedETHSourceComposition.source_count S D B f,
    EncodedETHSourceComposition.source_yes S D B f,
    EncodedETHSourceComposition.source_no S D B f⟩
  have hr := h f hn
  rw [heq] at hr
  exact hr

#print axioms boolean_stage
#print axioms source_effective

end EthInapproximability.CurrentPaper.SourceGenericComposite.SourceEndpoint
