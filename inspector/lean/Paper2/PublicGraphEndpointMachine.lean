import EthInapproximability.CurrentPaper.SourceNormalizationMachineDecode
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import Paper2.CanonicalEdgeTape

/-! Public encoded graph to the canonical unary endpoint tape, using the
existing physical graph decoder. -/

namespace Paper2.PublicGraphEndpointMachine

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.SourceNormalizationMachineDecode
open Paper2.CanonicalEdgeTape
open Turing EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding


private theorem fields_values (g : EncodedGraph.Graph) (hg : g.Valid) :
    (fields (graphEdge g hg)).map Fin.val =
      g.edges.flatMap (fun p => [p.1, p.2]) := by
  unfold fields
  rw [List.map_ofFn, List.ofFn_mul']
  simp only [List.ofFn_succ]
  change (List.ofFn (fun i : Fin g.edges.length =>
      [(endpointField (graphEdge g hg) ⟨2 * i.val, by omega⟩).val,
       (endpointField (graphEdge g hg) ⟨2 * i.val + 1, by omega⟩).val])).flatten =
    (g.edges.map (fun p => [p.1, p.2])).flatten
  congr 1
  rw [← List.ofFn_getElem_eq_map]
  apply congrArg List.ofFn
  funext i
  simp only [endpoint_even, endpoint_odd, graphEdge_false, graphEdge_true,
    List.get_eq_getElem]

theorem endpoint_word_eq (g : EncodedGraph.Graph) (hg : g.Valid) :
    endpointStream g = word (graphEdge g hg) := by
  unfold endpointStream word Paper2.UnaryFieldListParserScratch.tokens
  rw [← fields_values g hg]
  simp only [List.flatMap_map]
  apply List.flatMap_congr
  intro x hx
  rfl

abbrev Stack := SourceNormalizationMachineDecode.Stack ⊕ Fin 2

def parserSlots : SourceNormalizationMachineDecode.Stack ↪ Stack where
  toFun := Sum.inl
  inj' := by intro a b h; exact Sum.inl.inj h

def copySlots : Fin 3 ↪ Stack where
  toFun := fun i => if i = 0 then .inl (.inl 0)
    else if i = 1 then .inr 0 else .inr 1
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

def initialBank (input : List Bool) : Stack → List Bool :=
  Sum.elim (SourceNormalizationMachineDecode.start input).stk ![[], []]

def sourceBank (input : List Bool) : Stack → List Bool :=
  Sum.elim (SourceNormalizationMachineDecode.start input).stk ![input, []]

def copyProgram := MatrixStage4ScalarPreparationOps.copyProgram copySlots
def parserProgram : SourceNormalizationMachineDecode.Label → TM2.Stmt (fun _ : Stack => Bool)
    SourceNormalizationMachineDecode.Label SourceNormalizationMachineDecode.Control :=
  fun l => stackStmt parserSlots (SourceNormalizationMachineDecode.program l)

def parserControl : SourceNormalizationMachineDecode.Control :=
  (SourceNormalizationMachineField.initialControl, .count, none)

def program := BitMachineRawSequence.program copyProgram parserProgram
  (.inr .capScan) (none : Option Bool) parserControl

def start (input : List Bool) :=
  (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
    (none, parserControl), initialBank input⟩ :
      TM2.Cfg (fun _ : Stack => Bool)
        (BitMachineRawSequence.Label BitMachineCopy.Label SourceNormalizationMachineDecode.Label)
        (BitMachineRawSequence.Control (Option Bool) SourceNormalizationMachineDecode.Control))

def run (t : ℕ) (c : TM2.Cfg (fun _ : Stack => Bool)
    (BitMachineRawSequence.Label BitMachineCopy.Label SourceNormalizationMachineDecode.Label)
    (BitMachineRawSequence.Control (Option Bool) SourceNormalizationMachineDecode.Control)) :=
  ((advance program)^[t]) c

def resultCfg (g : EncodedGraph.Graph) (hg : g.Valid) :
    SourceNormalizationMachineDecode.Config :=
  SourceNormalizationMachineDecode.cfg none (doneControl true) {}
    (List.replicate g.vertices true) (List.replicate g.edges.length true)
    [] [] (word (graphEdge g hg)) []

def resultBank (g : EncodedGraph.Graph) (hg : g.Valid) : Stack → List Bool :=
  Sum.elim (resultCfg g hg).stk ![EncodedGraph.encode g, []]

private theorem framed (input : List Bool)
    (c : SourceNormalizationMachineDecode.Config) :
    stackCfg parserSlots (sourceBank input) c =
      ⟨c.l, c.var, Sum.elim c.stk ![input, []]⟩ := by
  dsimp [stackCfg]
  congr 1
  funext k
  cases k with
  | inl j => exact bank_at parserSlots (sourceBank input) c.stk j
  | inr j =>
      have h : ¬ ∃ x, parserSlots x = Sum.inr j := by
        simp [parserSlots]
      rw [bank_outside parserSlots (sourceBank input) c.stk (.inr j) h]
      fin_cases j <;> rfl

theorem copy_run (input : List Bool) :
    ((advance copyProgram)^[2 * input.length + 2])
      (⟨some .scan, none, initialBank input⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, sourceBank input⟩ := by
  have hsource : initialBank input (copySlots 0) = input := by
    simp [initialBank, copySlots, SourceNormalizationMachineDecode.start]
  have hscratch : initialBank input (copySlots 2) = [] := by
    simp [initialBank, copySlots]
  have hbank : Function.update (initialBank input) (copySlots 1)
      (initialBank input (copySlots 0) ++ initialBank input (copySlots 1)) =
      sourceBank input := by
    funext k
    cases k with
    | inl j => simp [initialBank, sourceBank, copySlots,
        SourceNormalizationMachineDecode.start]
    | inr j => fin_cases j <;> simp [initialBank, sourceBank, copySlots,
        SourceNormalizationMachineDecode.start]
  have h := MatrixStage4ScalarPreparationOps.copy_run copySlots
    (initialBank input) hscratch
  rw [hbank] at h
  simpa only [copyProgram, hsource] using h

theorem parser_run (g : EncodedGraph.Graph) (hg : g.Valid) :
    ∃ t ≤ graphCost g,
      ((advance parserProgram)^[t])
        (⟨some (.inr .capScan), parserControl, sourceBank (EncodedGraph.encode g)⟩ :
          TM2.Cfg (fun _ : Stack => Bool) SourceNormalizationMachineDecode.Label
            SourceNormalizationMachineDecode.Control) =
        ⟨none, doneControl true, resultBank g hg⟩ := by
  obtain ⟨t, ht, hr⟩ := decode_valid_run g hg
  refine ⟨t, ht, ?_⟩
  have hf := BitMachineStackRun.run parserSlots (sourceBank (EncodedGraph.encode g))
    SourceNormalizationMachineDecode.program
    (SourceNormalizationMachineDecode.start (EncodedGraph.encode g)) t
  change ((advance parserProgram)^[t])
    (stackCfg parserSlots (sourceBank (EncodedGraph.encode g))
      (SourceNormalizationMachineDecode.start (EncodedGraph.encode g))) =
    stackCfg parserSlots (sourceBank (EncodedGraph.encode g))
      (SourceNormalizationMachineDecode.run t
        (SourceNormalizationMachineDecode.start (EncodedGraph.encode g))) at hf
  rw [framed, hr, framed] at hf
  simpa only [SourceNormalizationMachineDecode.start, parserControl,
    sourceBank, resultBank, resultCfg, endpoint_word_eq g hg] using hf

/-- One fixed physical controller copies the public source, then runs the
existing graph parser. Its output bank has raw unary n/m and precisely the
canonical 2m terminated-unary endpoint tape; all parser work is blank. -/
theorem physical_run (g : EncodedGraph.Graph) (hg : g.Valid) :
    ∃ t ≤ 2 * (EncodedGraph.encode g).length + 3 + graphCost g,
      run t (start (EncodedGraph.encode g)) =
        ⟨none, (none, doneControl true), resultBank g hg⟩ := by
  let input := EncodedGraph.encode g
  obtain ⟨tp, htp, hp⟩ := parser_run g hg
  have hc := copy_run input
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs
    copyProgram parserProgram .scan (.inr .capScan)
    (none : Option Bool) (none : Option Bool)
    parserControl (doneControl true)
    (initialBank input) (sourceBank input) (resultBank g hg)
    (2 * input.length + 2) tp hc hp
  refine ⟨t, by dsimp [input] at ht; omega, ?_⟩
  simpa only [run, start, program, input] using h

theorem physical_run_public (g : EncodedGraph.Graph) (hg : g.Valid) :
    ∃ t ≤ 103 * ((EncodedGraph.encode g).length + 1)^3,
      run t (start (EncodedGraph.encode g)) =
        ⟨none, (none, doneControl true), resultBank g hg⟩ := by
  obtain ⟨t, ht, hr⟩ := physical_run g hg
  let N := (EncodedGraph.encode g).length
  have hc := graphCost_polynomial g hg
  have hsq : 1 ≤ (N + 1)^2 := by nlinarith
  have hpow : N + 1 ≤ (N + 1)^3 := by
    calc
      N + 1 = (N + 1) * 1 := by omega
      _ ≤ (N + 1) * (N + 1)^2 := Nat.mul_le_mul_left _ hsq
      _ = (N + 1)^3 := by ring
  refine ⟨t, ?_, hr⟩
  dsimp [N] at *
  omega

#print axioms endpoint_word_eq
#print axioms copy_run
#print axioms parser_run
#print axioms physical_run
#print axioms physical_run_public

end Paper2.PublicGraphEndpointMachine
