import EthInapproximability.CurrentPaper.SourceClauseWriter

/-!
# Physical finalizer for the ordered source-CNF writer

Source: frozen v8 `06-eth.tex`, `thm:paper-sparse-gap-source` and
`B-effectivity-details.tex`. The preceding clause loop leaves the ordered
payload reversed on a stack. This finite Boolean-stack program restores its
order and writes both canonical numeric headers. Its inputs are a unary
variable-count bank, a canonical binary clause-count word, and the reversed
payload. It does not assume preloaded final clauses or a preloaded final word.

Producing these three banks, including the *computed* clause-count word,
and integrating this program with the slot loop remain separate obligations.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseMachine

open Turing TM2.Stmt BitMachineEncoding

inductive Label where
  | payload
  | count
  | countFlush
  | vars
  deriving DecidableEq, Fintype

abbrev Stack := Fin 5
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool)

def contents (vars count reversed saved output : List Bool) : Stack → List Bool :=
  ![vars, count, reversed, saved, output]

def cfg (l : Option Label) (v : Option Bool)
    (vars count reversed saved output : List Bool) : Config :=
  ⟨l, v, contents vars count reversed saved output⟩

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .payload =>
      pop 2 (fun _ b => b)
        (branch Option.isSome
          (push 4 (fun b => b.getD false) (goto (fun _ => .payload)))
          (goto (fun _ => .count)))
  | .count =>
      pop 1 (fun _ b => b)
        (branch Option.isSome
          (push 3 (fun _ => true)
            (push 3 (fun b => b.getD false) (goto (fun _ => .count))))
          (push 3 (fun _ => false) (goto (fun _ => .countFlush))))
  | .countFlush =>
      pop 3 (fun _ b => b)
        (branch Option.isSome
          (push 4 (fun b => b.getD false) (goto (fun _ => .countFlush)))
          (push 4 (fun _ => false) (goto (fun _ => .vars))))
  | .vars =>
      pop 0 (fun _ b => b)
        (branch Option.isSome
          (push 4 (fun _ => true) (goto (fun _ => .vars))) halt)

def run (t : Nat) (c : Config) := ((advance program)^[t]) c

theorem run_succ (t : Nat) (c : Config) :
    run (t + 1) c = run t (advance program c) :=
  Function.iterate_succ_apply _ _ _

theorem run_add (t u : Nat) (c : Config) :
    run (t + u) c = run u (run t c) := by
  simpa only [run, Nat.add_comm] using Function.iterate_add_apply (advance program) u t c

theorem payload_cons (v : Option Bool) (b : Bool)
    (vars count rest saved output : List Bool) :
    advance program (cfg (some .payload) v vars count (b :: rest) saved output) =
      cfg (some .payload) (some b) vars count rest saved (b :: output) := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, contents]
  funext i; fin_cases i <;> rfl

theorem payload_nil (v : Option Bool) (vars count saved output : List Bool) :
    advance program (cfg (some .payload) v vars count [] saved output) =
      cfg (some .count) none vars count [] saved output := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, contents]

theorem payload_run (v : Option Bool)
    (vars count reversed saved output : List Bool) :
    run (reversed.length + 1)
      (cfg (some .payload) v vars count reversed saved output) =
        cfg (some .count) none vars count [] saved (reversed.reverse ++ output) := by
  induction reversed generalizing v output with
  | nil => simpa [run] using payload_nil v vars count saved output
  | cons b rest ih =>
      rw [List.length_cons, run_succ, payload_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

theorem count_cons (v : Option Bool) (b : Bool)
    (vars rest reversed saved output : List Bool) :
    advance program (cfg (some .count) v vars (b :: rest) reversed saved output) =
      cfg (some .count) (some b) vars rest reversed (b :: true :: saved) output := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, contents]
  funext i; fin_cases i <;> rfl

theorem count_nil (v : Option Bool) (vars reversed saved output : List Bool) :
    advance program (cfg (some .count) v vars [] reversed saved output) =
      cfg (some .countFlush) none vars [] reversed (false :: saved) output := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, contents]
  funext i; fin_cases i <;> rfl

theorem count_run (v : Option Bool)
    (vars count reversed saved output : List Bool) :
    run (count.length + 1)
      (cfg (some .count) v vars count reversed saved output) =
        cfg (some .countFlush) none vars [] reversed
          ((EncodedCommunication.field count).reverse ++ saved) output := by
  induction count generalizing v saved with
  | nil => simpa [run, EncodedCommunication.field] using
      count_nil v vars reversed saved output
  | cons b rest ih =>
      rw [List.length_cons, run_succ, count_cons, ih]
      simp [EncodedCommunication.field, List.reverse_cons, List.append_assoc]

theorem flush_cons (v : Option Bool) (b : Bool)
    (vars count reversed rest output : List Bool) :
    advance program (cfg (some .countFlush) v vars count reversed (b :: rest) output) =
      cfg (some .countFlush) (some b) vars count reversed rest (b :: output) := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, contents]
  funext i; fin_cases i <;> rfl

theorem flush_nil (v : Option Bool) (vars count reversed output : List Bool) :
    advance program (cfg (some .countFlush) v vars count reversed [] output) =
      cfg (some .vars) none vars count reversed [] (false :: output) := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, contents]
  funext i; fin_cases i <;> rfl

theorem flush_run (v : Option Bool)
    (vars count reversed saved output : List Bool) :
    run (saved.length + 1)
      (cfg (some .countFlush) v vars count reversed saved output) =
        cfg (some .vars) none vars count reversed []
          (false :: (saved.reverse ++ output)) := by
  induction saved generalizing v output with
  | nil => simpa [run] using flush_nil v vars count reversed output
  | cons b rest ih =>
      rw [List.length_cons, run_succ, flush_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

theorem vars_cons (v : Option Bool) (b : Bool)
    (rest count reversed output : List Bool) :
    advance program (cfg (some .vars) v (b :: rest) count reversed [] output) =
      cfg (some .vars) (some b) rest count reversed [] (true :: output) := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, contents]
  funext i; fin_cases i <;> rfl

theorem vars_nil (v : Option Bool) (count reversed output : List Bool) :
    advance program (cfg (some .vars) v [] count reversed [] output) =
      cfg none none [] count reversed [] output := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, contents]

theorem vars_run (v : Option Bool) (vars count reversed output : List Bool) :
    run (vars.length + 1) (cfg (some .vars) v vars count reversed [] output) =
      cfg none none [] count reversed []
        (List.replicate vars.length true ++ output) := by
  induction vars generalizing v output with
  | nil => simpa [run] using vars_nil v count reversed output
  | cons b rest ih =>
      rw [List.length_cons, run_succ, vars_cons, ih]
      rw [show List.replicate rest.length true ++ true :: output =
        (List.replicate rest.length true ++ [true]) ++ output by simp [List.append_assoc]]
      simp [List.replicate_add, List.append_assoc]

/-- Complete physical finalization. The input banks are consumed; the output
is the canonical CNF header followed by the previously streamed payload. -/
theorem finalize (n count : Nat) (reversePayload output : List Bool) :
    run (reversePayload.length + 3 * count.bits.length + n + 5)
      (cfg (some .payload) none (List.replicate n true) count.bits
        reversePayload [] output) =
      cfg none none [] [] [] []
        (EncodedGraph.unary n ++ EncodedCommunication.natField count ++
          reversePayload.reverse ++ output) := by
  have hp := payload_run none (List.replicate n true) count.bits reversePayload [] output
  have hc : run (count.bits.length + 1)
      (cfg (some .count) none (List.replicate n true) count.bits [] []
        (reversePayload.reverse ++ output)) =
      cfg (some .countFlush) none (List.replicate n true) [] []
        (EncodedCommunication.field count.bits).reverse
        (reversePayload.reverse ++ output) := by
    simpa only [List.append_nil] using count_run none (List.replicate n true)
      count.bits [] [] (reversePayload.reverse ++ output)
  have hf : run ((EncodedCommunication.field count.bits).reverse.length + 1)
      (cfg (some .countFlush) none (List.replicate n true) [] []
        (EncodedCommunication.field count.bits).reverse
        (reversePayload.reverse ++ output)) =
      cfg (some .vars) none (List.replicate n true) [] [] []
        (false :: (EncodedCommunication.field count.bits ++
          reversePayload.reverse ++ output)) := by
    simpa only [List.reverse_reverse, List.append_assoc] using
      flush_run none (List.replicate n true)
      [] [] (EncodedCommunication.field count.bits).reverse
        (reversePayload.reverse ++ output)
  have hv := vars_run none (List.replicate n true) [] []
    (false :: (EncodedCommunication.field count.bits ++ reversePayload.reverse ++ output))
  have ht : reversePayload.length + 3 * count.bits.length + n + 5 =
      (reversePayload.length + 1) + (count.bits.length + 1) +
        ((EncodedCommunication.field count.bits).reverse.length + 1) +
          ((List.replicate n true).length + 1) := by
    simp [EncodedCommunication.field_length]
    omega
  rw [ht, show
      (reversePayload.length + 1) + (count.bits.length + 1) +
        ((EncodedCommunication.field count.bits).reverse.length + 1) +
          ((List.replicate n true).length + 1) =
      (reversePayload.length + 1) + ((count.bits.length + 1) +
        (((EncodedCommunication.field count.bits).reverse.length + 1) +
          ((List.replicate n true).length + 1))) by omega,
    run_add, hp, run_add, hc, run_add, hf, hv]
  simp [EncodedCommunication.natField, EncodedGraph.unary, List.append_assoc]

def outputClauseCount {n m a q : Nat} (P : SourceBooleanEncoding.CSP n m a q)
    (hq : 0 < q) : Nat :=
  SourceClauseHeaderCount.countedClauses (SourceBooleanEncoding.formula P hq).clauses

/-- The actual finalizer run specializes to the exact source converter word.
The starting banks are specified outputs of the still-separate slot/header
producers, not an assumption that those producers have been compiled. -/
theorem finalize_source {n m a q : Nat} (P : SourceBooleanEncoding.CSP n m a q)
    (hq : 0 < q) (output : List Bool) :
    run ((SourceClauseWriter.stream P hq).length +
        3 * (outputClauseCount P hq).bits.length +
          (SourceBooleanEncoding.threeCNF P hq).variables + 5)
      (cfg (some .payload) none
        (List.replicate (SourceBooleanEncoding.threeCNF P hq).variables true)
        (outputClauseCount P hq).bits
        (SourceClauseWriter.stream P hq) [] output) =
      cfg none none [] [] [] []
        (EncodedCNF.encode (SourceBooleanEncoding.threeCNF P hq) ++ output) := by
  have h := finalize (SourceBooleanEncoding.threeCNF P hq).variables
    (outputClauseCount P hq) (SourceClauseWriter.stream P hq) output
  have hh := SourceClauseWriter.withHeader_correct P hq
  change EncodedGraph.unary (SourceBooleanEncoding.threeCNF P hq).variables ++
      EncodedCommunication.natField (outputClauseCount P hq) ++
        (SourceClauseWriter.stream P hq).reverse =
      EncodedCNF.encode (SourceBooleanEncoding.threeCNF P hq) at hh
  rw [hh] at h
  exact h

/-- The finalizer's literal transition count is at most twice the final
encoded output length plus one, independently of the source promise. -/
theorem finalizer_time_le_output {n m a q : Nat}
    (P : SourceBooleanEncoding.CSP n m a q) (hq : 0 < q) :
    (SourceClauseWriter.stream P hq).length +
        3 * (outputClauseCount P hq).bits.length +
          (SourceBooleanEncoding.threeCNF P hq).variables + 5 ≤
      2 * (EncodedCNF.encode (SourceBooleanEncoding.threeCNF P hq)).length + 1 := by
  have hcount := SourceClauseHeaderCount.boolean_clause_count P hq
  have hp := SourceClauseWriter.stream_correct P hq
  have hlen := congrArg List.length hp
  simp only [List.length_reverse] at hlen
  unfold outputClauseCount
  rw [hlen, ← hcount]
  simp only [EncodedCNF.encode, List.length_append,
    EncodedGraph.unary, List.length_append, List.length_replicate,
    List.length_singleton, EncodedCommunication.natField,
    EncodedCommunication.field_length]
  omega

/-- Sum of the already implemented clause-emission calls and the concrete
finalizer's transitions. This still does not charge the missing producer and
dispatch machinery, so it is not a bound for a complete converter. -/
theorem emitted_and_finalized_charge {n m a q : Nat}
    (P : SourceBooleanEncoding.CSP n m a q) (hq : 0 < q) :
    SourceClauseWriter.physicalCharge
        (SourceBooleanEncoding.threeCNF P hq).clauses +
      ((SourceClauseWriter.stream P hq).length +
        3 * (outputClauseCount P hq).bits.length +
          (SourceBooleanEncoding.threeCNF P hq).variables + 5) ≤
      3 * (EncodedCNF.encode (SourceBooleanEncoding.threeCNF P hq)).length +
        (SourceBooleanEncoding.threeCNF P hq).clauses.length + 1 := by
  have h₁ := SourceClauseWriter.source_physicalCharge_le P hq
  have h₂ := finalizer_time_le_output P hq
  omega

theorem emitted_and_finalized_charge_quadratic {n m a q : Nat}
    (P : SourceBooleanEncoding.CSP n m a q) (hq : 0 < q)
    (hn : n ≤ q * m) :
    SourceClauseWriter.physicalCharge
        (SourceBooleanEncoding.threeCNF P hq).clauses +
      ((SourceClauseWriter.stream P hq).length +
        3 * (outputClauseCount P hq).bits.length +
          (SourceBooleanEncoding.threeCNF P hq).variables + 5) ≤
      (18 * (SourceBooleanEncoding.threeSizeFactor a q) ^ 2 +
        28 * SourceBooleanEncoding.threeSizeFactor a q + 7) * (m + 1) ^ 2 := by
  let S := SourceBooleanEncoding.threeSizeFactor a q
  let F := SourceBooleanEncoding.threeCNF P hq
  have hsize : F.variables + F.clauses.length ≤ S * m :=
    SourceBooleanEncoding.threeCNF_size P hq hn
  have hv : F.variables ≤ S * m := by omega
  have hc : F.clauses.length ≤ S * m := by omega
  have henc := EncodedCNF.encode_length_upper F
    (SourceBooleanEncoding.threeCNF_valid P hq)
  have hmul := Nat.mul_le_mul hc
    (show 6 * F.variables + 8 ≤ 6 * (S * m) + 8 by omega)
  have hcost := emitted_and_finalized_charge P hq
  change (EncodedCNF.encode F).length ≤
    F.variables + 2 + F.clauses.length * (6 * F.variables + 8) at henc
  change SourceClauseWriter.physicalCharge F.clauses +
      ((SourceClauseWriter.stream P hq).length +
        3 * (outputClauseCount P hq).bits.length + F.variables + 5) ≤
      3 * (EncodedCNF.encode F).length + F.clauses.length + 1 at hcost
  change SourceClauseWriter.physicalCharge F.clauses +
      ((SourceClauseWriter.stream P hq).length +
        3 * (outputClauseCount P hq).bits.length + F.variables + 5) ≤
      (18 * S ^ 2 + 28 * S + 7) * (m + 1) ^ 2
  nlinarith

end EthInapproximability.CurrentPaper.SourceClauseMachine
