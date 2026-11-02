import Paper2.AFrontTransducer
import EthInapproximability.CurrentPaper.CNFValidatorRuntime
import EthInapproximability.CurrentPaper.BitMachineComposition
import EthInapproximability.CurrentPaper.EncodedETHTail

/-!
# WP-U18a (iv): the sparse-density check for the growing-gap branch (lane `owner:a-front-1`)

Private lane module, 27 September 2026. Paper A, lock v12. Author decisions of 27 September 2026:
D-A2 (the language is Paper B's `EncodedCNF.Language`) and D-A6 (randomized sparse ETH in the
DRAFT promise form: "no randomized decider with error <= 1/3 on well-formed 3-CNF inputs with
clauses <= c_s N"). Lock text: v12 `sections/05-*`/`E:95-98` (`def:reth`) "3-SAT on N variables
and at most c_sN clauses".

For every machine constant `K` (the density constant `c_s`), ONE fixed machine
`sparseCheck K = composition CNFValidator.machine (Transducer.machine (sparseSpec K) .flag)`
prints, on EVERY bitstring `w`, exactly `[sparseAnswer K w]`, where `sparseAnswer K w` is true
iff `w` is the canonical encoding of a valid formula with `#clauses ≤ K · #variables`.
The transducer keeps a physical unary counter: `K` marks per unary variable bit, one mark
removed at the sign bit of the first literal of each clause; an empty counter at that point
sends it to the rejecting sink. Clock: cubic (validator) plus linear.

No ledger row is closed by this module.
-/

namespace AFront.Sparse

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCNF
open AFront.Transducer

inductive SP
  | flag | unary | cntTag | cntBit
  | sign0 | tag0 | bit0 | sign1 | tag1 | bit1 | sign2 | tag2 | bit2
  | dead
  deriving DecidableEq, Fintype

/-- The counter transducer for density constant `K`. It reads the validator's result word. -/
def sparseSpec (K : ℕ) : Spec SP where
  step s b present := match s, b with
    | .flag, true => .unary
    | .flag, false => .dead
    | .unary, true => .unary
    | .unary, false => .cntTag
    | .cntTag, true => .cntBit
    | .cntTag, false => .sign0
    | .cntBit, _ => .cntTag
    | .sign0, _ => if present then .tag0 else .dead
    | .tag0, true => .bit0
    | .tag0, false => .sign1
    | .bit0, _ => .tag0
    | .sign1, _ => .tag1
    | .tag1, true => .bit1
    | .tag1, false => .sign2
    | .bit1, _ => .tag1
    | .sign2, _ => .tag2
    | .tag2, true => .bit2
    | .tag2, false => .sign0
    | .bit2, _ => .tag2
    | .dead, _ => .dead
  emit _ _ := []
  op s b := match s, b with
    | .unary, true => .inc
    | .sign0, _ => .dec
    | _, _ => .keep
  fin s := match s with
    | .dead => [false]
    | _ => [true]
  incBy := K
  bound := 1
  emit_le _ _ := by simp
  fin_le s := by cases s <;> simp

variable (K : ℕ)

theorem out_eq (s : SP) (c : ℕ) (w : List Bool) :
    (sparseSpec K).out s c w = (sparseSpec K).fin ((sparseSpec K).last s c w).1 := by
  induction w generalizing s c with
  | nil => rfl
  | cons b w ih =>
      rw [Spec.out_cons, ih]
      rfl

theorem last_append (s : SP) (c : ℕ) (u v : List Bool) :
    (sparseSpec K).last s c (u ++ v) =
      (sparseSpec K).last ((sparseSpec K).last s c u).1 ((sparseSpec K).last s c u).2 v := by
  induction u generalizing s c with
  | nil => rfl
  | cons b u ih => exact ih _ _

theorem last_cons (s : SP) (c : ℕ) (b : Bool) (w : List Bool) :
    (sparseSpec K).last s c (b :: w) =
      (sparseSpec K).last ((sparseSpec K).next s c b).1 ((sparseSpec K).next s c b).2 w := rfl

theorem next_sign0_succ (c : ℕ) (b : Bool) : (sparseSpec K).next .sign0 (c + 1) b = (.tag0, c) := by
  simp [Spec.next, sparseSpec]

theorem last_dead (c : ℕ) (w : List Bool) : ((sparseSpec K).last .dead c w).1 = .dead := by
  induction w generalizing c with
  | nil => rfl
  | cons b w ih => exact ih _

theorem last_unary (c n : ℕ) :
    (sparseSpec K).last .unary c (List.replicate n true) = (.unary, c + K * n) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ]
      show (sparseSpec K).last .unary (c + K) (List.replicate n true) = _
      rw [ih]
      congr 1
      ring

/-- A self-delimiting field in the "tag" state returns to the matching exit state. -/
theorem last_field (tag bitS exit : SP) (htrue : ∀ b c, (sparseSpec K).next tag c true = (bitS, c) ∧
      (sparseSpec K).next bitS c b = (tag, c))
    (hfalse : ∀ c, (sparseSpec K).next tag c false = (exit, c))
    (c : ℕ) (bs : List Bool) :
    (sparseSpec K).last tag c (EncodedCommunication.field bs) = (exit, c) := by
  induction bs with
  | nil =>
      show (sparseSpec K).last ((sparseSpec K).next tag c false).1
        ((sparseSpec K).next tag c false).2 [] = _
      rw [hfalse]; rfl
  | cons b bs ih =>
      show (sparseSpec K).last ((sparseSpec K).next ((sparseSpec K).next tag c true).1
        ((sparseSpec K).next tag c true).2 b).1
        ((sparseSpec K).next ((sparseSpec K).next tag c true).1
        ((sparseSpec K).next tag c true).2 b).2 (EncodedCommunication.field bs) = _
      rw [(htrue b c).1, (htrue b c).2]
      exact ih

theorem last_count (c : ℕ) (m : ℕ) :
    (sparseSpec K).last .cntTag c (EncodedCommunication.natField m) = (.sign0, c) :=
  last_field K .cntTag .cntBit .sign0 (fun b c => ⟨rfl, rfl⟩) (fun c => rfl) c _

theorem last_clause (c : ℕ) (cl : Clause) :
    (sparseSpec K).last .sign0 c (encodeClause cl) =
      if c = 0 then ((sparseSpec K).last .dead 0 ((encodeClause cl).drop 1)) else (.sign0, c - 1) := by
  rcases cl with ⟨⟨v0, p0⟩, ⟨v1, p1⟩, ⟨v2, p2⟩⟩
  simp only [encodeClause, encodeLiteral, EncodedCommunication.natField, List.cons_append,
    List.drop_succ_cons, List.drop_zero]
  cases c with
  | zero => rfl
  | succ c =>
      simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
      rw [last_cons, next_sign0_succ]
      simp only [List.append_assoc]
      rw [last_append, last_field K .tag0 .bit0 .sign1 (fun b c => ⟨rfl, rfl⟩) (fun c => rfl)]
      simp only [List.cons_append]
      rw [last_cons]
      show (sparseSpec K).last .tag1 c _ = _
      rw [last_append, last_field K .tag1 .bit1 .sign2 (fun b c => ⟨rfl, rfl⟩) (fun c => rfl)]
      simp only [List.cons_append]
      rw [last_cons]
      show (sparseSpec K).last .tag2 c _ = _
      rw [last_field K .tag2 .bit2 .sign0 (fun b c => ⟨rfl, rfl⟩) (fun c => rfl)]

theorem last_clauses (cs : List Clause) (c : ℕ) :
    ((sparseSpec K).last .sign0 c (clauseFields cs)).1 =
      if cs.length ≤ c then .sign0 else .dead := by
  induction cs generalizing c with
  | nil => simp [clauseFields, Spec.last]
  | cons cl cs ih =>
      rw [clauseFields, last_append, last_clause]
      cases c with
      | zero =>
          simp only [if_true]
          rw [last_dead, last_dead]
          simp
      | succ c =>
          simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
          rw [ih]
          simp [List.length_cons]

/-- The decided predicate: `w` encodes a valid formula with `#clauses ≤ K · #variables`. -/
def sparseAnswer (w : List Bool) : Bool :=
  match EncodedCNF.decode w with
  | none => false
  | some f => decide (f.clauses.length ≤ K * f.variables)

theorem sparseAnswer_encode (f : Formula) (hf : f.Valid) :
    sparseAnswer K (encode f) = decide (f.clauses.length ≤ K * f.variables) := by
  simp [sparseAnswer, EncodedCNF.decode_encode f hf]

theorem sparseAnswer_malformed {w : List Bool} (h : EncodedCNF.decode w = none) :
    sparseAnswer K w = false := by
  simp [sparseAnswer, h]

theorem sparseAnswer_iff (w : List Bool) :
    sparseAnswer K w = true ↔ ∃ f, EncodedCNF.decode w = some f ∧ f.clauses.length ≤ K * f.variables := by
  unfold sparseAnswer
  cases h : EncodedCNF.decode w with
  | none => simp
  | some f => simp

theorem spec_out (w : List Bool) :
    (sparseSpec K).out .flag 0 (CNFValidator.result w) = [sparseAnswer K w] := by
  rw [out_eq]
  unfold CNFValidator.result
  cases h : EncodedCNF.decode w with
  | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, if_false]
      rw [sparseAnswer_malformed K h]
      rfl
  | some f =>
      simp only [Option.isSome_some, if_true]
      obtain ⟨hv, he⟩ := EncodedCNF.decode_spec h
      rw [← he, sparseAnswer_encode K f hv]
      rw [last_cons]
      show (sparseSpec K).fin ((sparseSpec K).last .unary 0 (encode f)).1 = _
      rw [encode, EncodedGraph.unary]
      simp only [List.append_assoc, List.singleton_append]
      rw [last_append, last_unary]
      simp only [List.cons_append]
      rw [last_cons]
      show (sparseSpec K).fin ((sparseSpec K).last .cntTag (0 + K * f.variables)
        (EncodedCommunication.natField f.clauses.length ++ clauseFields f.clauses)).1 = _
      rw [last_append]
      rw [last_count, last_clauses]
      by_cases hle : f.clauses.length ≤ 0 + K * f.variables
      · have : f.clauses.length ≤ K * f.variables := by omega
        simp [hle, this, sparseSpec]
      · have : ¬ f.clauses.length ≤ K * f.variables := by omega
        simp [hle, this, sparseSpec]

/-- THE fixed sparse-density checker for machine constant `K`. -/
noncomputable def sparseCheck : BitMachine.Machine :=
  BitMachineComposition.composition CNFValidator.machine (Transducer.machine (sparseSpec K) SP.flag)

theorem result_length (w : List Bool) : (CNFValidator.result w).length ≤ w.length + 1 := by
  unfold CNFValidator.result; split <;> simp

/-- **Sparse-density check (exact, charged).** On EVERY bitstring `w`, `sparseCheck K` prints
exactly `[sparseAnswer K w]`. -/
theorem sparseCheck_outputs (w : List Bool) :
    (sparseCheck K).OutputsWithin w [sparseAnswer K w]
      (250 * (w.length + 1) ^ 3 + 2 * (CNFValidator.result w).length + 2 +
        ((sparseSpec K).bound + 2) * ((CNFValidator.result w).length + 1)) := by
  have h2 := Transducer.machine_outputs_linear (sparseSpec K) SP.flag (CNFValidator.result w)
  rw [spec_out] at h2
  exact BitMachineComposition.composition_outputsWithin _ _ (CNFValidator.Runtime.outputs w) h2

/-- The same with one cubic clock, independent of `K`. -/
theorem sparseCheck_outputs_poly (w : List Bool) :
    (sparseCheck K).OutputsWithin w [sparseAnswer K w] (260 * (w.length + 1) ^ 3) := by
  apply BitMachine.outputsWithin_mono _ (sparseCheck_outputs K w)
  have hr := result_length w
  have hb : (sparseSpec K).bound = 1 := rfl
  have hl : w.length + 1 ≤ (w.length + 1) ^ 3 := by
    calc w.length + 1 = (w.length + 1) ^ 1 := (pow_one _).symm
      _ ≤ (w.length + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  rw [hb]
  omega

theorem sparseCheck_polytime : BitMachine.Polytime (fun w => [sparseAnswer K w]) :=
  ⟨sparseCheck K, 260, 3, fun w => sparseCheck_outputs_poly K w⟩

/-- On valid formula words: the check decides `#clauses ≤ K · #variables` exactly. -/
theorem sparseCheck_valid (f : Formula) (hf : f.Valid) :
    (sparseCheck K).OutputsWithin (encode f) [decide (f.clauses.length ≤ K * f.variables)]
      (260 * ((encode f).length + 1) ^ 3) := by
  have h := sparseCheck_outputs_poly K (encode f)
  rwa [sparseAnswer_encode K f hf] at h

#print axioms sparseCheck_outputs
#print axioms sparseCheck_outputs_poly
#print axioms sparseCheck_polytime
#print axioms sparseCheck_valid
#print axioms sparseAnswer_iff

end AFront.Sparse
