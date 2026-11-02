import EthInapproximability.CurrentPaper.SourceClauseGenericTrue
import EthInapproximability.CurrentPaper.SourceClauseCircuitClock

namespace EthInapproximability.CurrentPaper.SourceClauseGenericCircuitClock

open Turing BitMachineEncoding
open scoped Classical
open SourceClauseRowSchedule SourceClauseEncoding EncodedCNF
open SourceClauseCallback (Circuit rowQuery)
open SourceClauseGenericCallback

theorem bounded_irrel {K L V : Type}
    (P : L → Turing.TM2.Stmt (fun _ : K => Bool) L V)
    (c u : Turing.TM2.Cfg (fun _ : K => Bool) L V)
    (d e : DecidableEq K) (B : ℕ)
    (h : ∃ t ≤ B, ((@advance K L V d P)^[t]) c = u) :
    ∃ t ≤ B, ((@advance K L V e P)^[t]) c = u := by
  cases SourceClauseCallback.decidable_eq_irrel d e
  exact h

noncomputable def unitCost {a q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q)) (ell : ℕ) (sign : Bool)
    (saved output count : List Bool) : ℕ :=
  SourceClauseRowWriterUnitReady.stageCost q n r a k.val (width a q) ell +
  SourceClauseRowUnitMachine.cost n r a q k.val (width a q) ell + 1 +
  SourceClauseRowWriterUnitClean.clearCost
    (SourceClauseRowWriterUnitReady.unitFinalBank row n r a k.val
      (width a q) ell sign saved output count) + 1

noncomputable def gateCost {a q : ℕ}
    (j : Fin q) (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q)) (s t : ℕ) (sign : Bool)
    (saved output count : List Bool) : ℕ :=
  SourceClauseRowWriterGateRun.stageCost j row n r a k.val s t (width a q) +
  SourceClauseRowIndexedGate.cost q n r a k.val
    (row (.inl (j, 1))).length s t (width a q) sign + 1 +
  SourceClauseRowWriterGateClean.clearCost
    (SourceClauseRowWriterGateRun.result j row n r a k.val
      s t (width a q) sign saved output count) + 1

theorem opening_bounded {a q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count : List Bool) :
    Circuit.BoundedRun (openingCircuit k)
      (unitCost row n r k 0 false saved output count)
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterBlank.bank row n r
        ((encodeClause (unit (negative (base n r k)))).reverse ++ saved)
        output (true :: count)) := by
  classical
  obtain ⟨t, ht, hr⟩ := opening_run row n r k saved output count
  exact bounded_irrel _ _ _ _ _ _ ⟨t, ht, hr⟩

theorem false_gate_bounded {a q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count : List Bool)
    (hquery : row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    Circuit.BoundedRun (SourceClauseGenericCallback.gateCircuit k j)
      (gateCost j row n r k (tuple a q k j).val j.val false
        saved output count)
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterBlank.bank row n r
        ((SourceClauseGenericCallback.gatePayload row n r k j).reverse ++ saved)
        output (true :: true :: true :: count)) := by
  classical
  obtain ⟨t, ht, hr⟩ := gate_run j row n r k saved output count hquery
  exact bounded_irrel _ _ _ _ _ _ ⟨t, ht, hr⟩

theorem false_closing_bounded {a q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count : List Bool) :
    Circuit.BoundedRun (SourceClauseGenericCallback.closingCircuit k)
      (unitCost row n r k q true saved output count)
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterBlank.bank row n r
        ((encodeClause (unit (positive (base n r k + q)))).reverse ++ saved)
        output (true :: count)) := by
  classical
  obtain ⟨t, ht, hr⟩ := closing_run row n r k saved output count
  exact bounded_irrel _ _ _ _ _ _ ⟨t, ht, hr⟩

theorem true_gate_bounded {a q : ℕ} (hq : 0 < q) (p : Fin (q + 1))
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count : List Bool)
    (hquery : row (.inl ((SourceClauseGenericTrue.instruction hq k p).1, 1)) =
      List.replicate
        (row (.inl ((SourceClauseGenericTrue.instruction hq k p).1, 1))).length true) :
    Circuit.BoundedRun (SourceClauseGenericTrue.gateCircuit hq k p)
      (gateCost (SourceClauseGenericTrue.instruction hq k p).1
        row n r k (SourceClauseGenericTrue.instruction hq k p).2.1.val
        p.val (SourceClauseGenericTrue.instruction hq k p).2.2
        saved output count)
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterBlank.bank row n r
        ((SourceClauseGenericTrue.gatePayload hq row n r k p).reverse ++ saved)
        output (true :: true :: true :: count)) := by
  classical
  obtain ⟨t, ht, hr⟩ := SourceClauseRowWriterGateClean.run
    (SourceClauseGenericTrue.instruction hq k p).1 row n r a k.val
    (SourceClauseGenericTrue.instruction hq k p).2.1.val p.val (width a q)
    (SourceClauseGenericTrue.instruction hq k p).2.2
    saved output count hquery
  rw [SourceClauseRowWriterNormalize.gate_blank (h := hquery),
    SourceClauseGenericTrue.gate_saved] at hr
  exact bounded_irrel _ _ _ _ _ _ ⟨t, ht, hr⟩

theorem true_closing_bounded {a q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count : List Bool) :
    Circuit.BoundedRun (SourceClauseGenericTrue.closingCircuit k)
      (unitCost row n r k (q + 1) true saved output count)
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterBlank.bank row n r
        ((encodeClause (unit (positive (base n r k + (q + 1))))).reverse ++ saved)
        output (true :: count)) := by
  classical
  obtain ⟨t, ht, hr⟩ := SourceClauseRowWriterUnitClean.run
    row n r a k.val (width a q) (q + 1) true saved output count
  rw [SourceClauseRowWriterUnitClean.unit_blank,
    SourceClauseGenericTrue.closing_saved] at hr
  exact bounded_irrel _ _ _ _ _ _ ⟨t, ht, hr⟩

noncomputable def listCircuit {K α : Type} (C : α → Circuit K) :
    List α → Circuit K
  | [] => Circuit.halt
  | a :: as => Circuit.seq (C a) (listCircuit C as)

def foldSaved {α : Type} (payload : α → List Bool)
    (as : List α) (saved : List Bool) : List Bool :=
  as.foldl (fun acc a => payload a ++ acc) saved

noncomputable def listCost {α : Type}
    (stepCost : α → List Bool → List Bool → List Bool → ℕ)
    (payload : α → List Bool) (as : List α)
    (saved output count : List Bool) : ℕ :=
  match as with
  | [] => 1
  | a :: as =>
      stepCost a saved output count +
      listCost stepCost payload as (payload a ++ saved)
        output (true :: true :: true :: count) + 1

theorem list_bounded_run {α : Type} {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (C : α → Circuit (SourceClauseRowWriterOperands.Stack q))
    (stepCost : α → List Bool → List Bool → List Bool → ℕ)
    (payload : α → List Bool) (as : List α)
    (saved output count : List Bool)
    (hstep : ∀ a saved output count,
      Circuit.BoundedRun (C a) (stepCost a saved output count)
        (SourceClauseRowWriterBlank.bank row n r saved output count)
        (SourceClauseRowWriterBlank.bank row n r
          (payload a ++ saved) output
          (true :: true :: true :: count))) :
    Circuit.BoundedRun (listCircuit C as)
      (listCost stepCost payload as saved output count)
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterBlank.bank row n r
        (foldSaved payload as saved) output
        (List.replicate (3 * as.length) true ++ count)) := by
  induction as generalizing saved count with
  | nil =>
      simpa [listCircuit, listCost, foldSaved] using
        Circuit.halt_bounded_run
          (SourceClauseRowWriterBlank.bank row n r saved output count)
  | cons a as ih =>
      have hhead := hstep a saved output count
      have htail := ih (payload a ++ saved)
        (true :: true :: true :: count)
      have hseq := Circuit.seq_bounded_run (C a) (listCircuit C as)
        (SourceClauseRowWriterBlank.bank row n r saved output count)
        (SourceClauseRowWriterBlank.bank row n r
          (payload a ++ saved) output (true :: true :: true :: count))
        (SourceClauseRowWriterBlank.bank row n r
          (foldSaved payload as (payload a ++ saved)) output
          (List.replicate (3 * as.length) true ++
            (true :: true :: true :: count)))
        (stepCost a saved output count)
        (listCost stepCost payload as (payload a ++ saved)
          output (true :: true :: true :: count))
        hhead htail
      have hnum :
          List.replicate (3 * (a :: as).length) true ++ count =
            List.replicate (3 * as.length) true ++
              (true :: true :: true :: count) := by
        rw [List.length_cons, Nat.mul_add, Nat.mul_one,
          List.replicate_add, List.append_assoc]
        rfl
      simpa only [listCircuit, listCost, foldSaved, List.foldl_cons,
        hnum] using hseq

theorem false_listCircuit_eq {a q : ℕ} (k : Fin (a ^ q))
    (js : List (Fin q)) :
    listCircuit (SourceClauseGenericCallback.gateCircuit k) js =
      SourceClauseGenericCallback.gateListCircuit k js := by
  induction js with
  | nil => rfl
  | cons j js ih => simp [listCircuit, SourceClauseGenericCallback.gateListCircuit, ih]

theorem true_listCircuit_eq {a q : ℕ} (hq : 0 < q)
    (k : Fin (a ^ q)) (ps : List (Fin (q + 1))) :
    listCircuit (SourceClauseGenericTrue.gateCircuit hq k) ps =
      SourceClauseGenericTrue.gateListCircuit hq k ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [listCircuit, SourceClauseGenericTrue.gateListCircuit, ih]

def falseGateBytes {a q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q)) (j : Fin q) : List Bool :=
  (SourceClauseGenericCallback.gatePayload row n r k j).reverse

noncomputable def falseGateCost {a q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q)) (j : Fin q)
    (saved output count : List Bool) : ℕ :=
  gateCost j row n r k (tuple a q k j).val j.val false
    saved output count

def trueGateBytes {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q)) (p : Fin (q + 1)) : List Bool :=
  (SourceClauseGenericTrue.gatePayload hq row n r k p).reverse

noncomputable def trueGateCost {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q)) (p : Fin (q + 1))
    (saved output count : List Bool) : ℕ :=
  gateCost (SourceClauseGenericTrue.instruction hq k p).1 row n r k
    (SourceClauseGenericTrue.instruction hq k p).2.1.val p.val
    (SourceClauseGenericTrue.instruction hq k p).2.2
    saved output count

theorem false_gates_bounded {a q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (js : List (Fin q)) (saved output count : List Bool)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    Circuit.BoundedRun (SourceClauseGenericCallback.gateListCircuit k js)
      (listCost (falseGateCost row n r k) (falseGateBytes row n r k)
        js saved output count)
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterBlank.bank row n r
        (foldSaved (falseGateBytes row n r k) js saved) output
        (List.replicate (3 * js.length) true ++ count)) := by
  rw [← false_listCircuit_eq]
  apply list_bounded_run
  intro j saved output count
  simpa [falseGateCost, falseGateBytes] using
    false_gate_bounded j row n r k saved output count (hquery j)

theorem true_gates_bounded {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (ps : List (Fin (q + 1))) (saved output count : List Bool)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    Circuit.BoundedRun (SourceClauseGenericTrue.gateListCircuit hq k ps)
      (listCost (trueGateCost hq row n r k)
        (trueGateBytes hq row n r k) ps saved output count)
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterBlank.bank row n r
        (foldSaved (trueGateBytes hq row n r k) ps saved) output
        (List.replicate (3 * ps.length) true ++ count)) := by
  rw [← true_listCircuit_eq]
  apply list_bounded_run
  intro p saved output count
  simpa [trueGateCost, trueGateBytes] using
    true_gate_bounded hq p row n r k saved output count
      (hquery (SourceClauseGenericTrue.instruction hq k p).1)

theorem false_fold_eq {a q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (js : List (Fin q)) (saved : List Bool) :
    foldSaved (falseGateBytes row n r k) js saved =
      SourceClauseGenericCallback.gateFold row n r k js saved := rfl

theorem true_fold_eq {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (ps : List (Fin (q + 1))) (saved : List Bool) :
    foldSaved (trueGateBytes hq row n r k) ps saved =
      SourceClauseGenericTrue.gateFold hq row n r k ps saved := rfl

noncomputable def falseBlockCost {a q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count : List Bool) : ℕ :=
  let s₀ := (encodeClause (unit (negative (base n r k)))).reverse ++ saved
  let c₀ := true :: count
  let js := List.ofFn (fun j : Fin q => j)
  let s₁ := foldSaved (falseGateBytes row n r k) js s₀
  let c₁ := List.replicate (3 * q) true ++ c₀
  unitCost row n r k 0 false saved output count +
    (listCost (falseGateCost row n r k) (falseGateBytes row n r k)
      js s₀ output c₀ +
      unitCost row n r k q true s₁ output c₁ + 1) + 1

theorem false_block_source_bounded {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count : List Bool)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    Circuit.BoundedRun (SourceClauseGenericCallback.blockCircuit k)
      (falseBlockCost row n r k saved output count)
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterBlank.bank row n r
        ((clauseFields (chain (base n r k)
          (tupleClause hq k (rowQuery row) false))).reverse ++ saved)
        output (List.replicate (3 * q + 2) true ++ count)) := by
  let s₀ := (encodeClause (unit (negative (base n r k)))).reverse ++ saved
  let c₀ := true :: count
  let js := List.ofFn (fun j : Fin q => j)
  let s₁ := foldSaved (falseGateBytes row n r k) js s₀
  let c₁ := List.replicate (3 * q) true ++ c₀
  have h₀ := opening_bounded row n r k saved output count
  have h₁ := false_gates_bounded row n r k js s₀ output c₀ hquery
  have h₂ := false_closing_bounded row n r k s₁ output c₁
  have h₁₂ := Circuit.seq_bounded_run
    (SourceClauseGenericCallback.gateListCircuit k js)
    (SourceClauseGenericCallback.closingCircuit k)
    (SourceClauseRowWriterBlank.bank row n r s₀ output c₀)
    (SourceClauseRowWriterBlank.bank row n r s₁ output c₁)
    (SourceClauseRowWriterBlank.bank row n r
      ((encodeClause (unit (positive (base n r k + q)))).reverse ++ s₁)
      output (true :: c₁))
    (listCost (falseGateCost row n r k) (falseGateBytes row n r k)
      js s₀ output c₀)
    (unitCost row n r k q true s₁ output c₁)
    (by simpa [js, c₁, s₁] using h₁) h₂
  have h := Circuit.seq_bounded_run
    (openingCircuit k)
    (Circuit.seq (SourceClauseGenericCallback.gateListCircuit k js)
      (SourceClauseGenericCallback.closingCircuit k))
    (SourceClauseRowWriterBlank.bank row n r saved output count)
    (SourceClauseRowWriterBlank.bank row n r s₀ output c₀)
    (SourceClauseRowWriterBlank.bank row n r
      ((encodeClause (unit (positive (base n r k + q)))).reverse ++ s₁)
      output (true :: c₁))
    (unitCost row n r k 0 false saved output count)
    (listCost (falseGateCost row n r k) (falseGateBytes row n r k)
      js s₀ output c₀ +
      unitCost row n r k q true s₁ output c₁ + 1)
    h₀ h₁₂
  have hp := SourceClauseGenericCallback.source_payload hq row n r k saved
  rw [← false_fold_eq] at hp
  have hc : true :: c₁ =
      List.replicate (3 * q + 2) true ++ count := by
    dsimp [c₁, c₀]
    rw [show 3 * q + 2 = 1 + (3 * q + 1) by omega,
      List.replicate_add]
    simp [List.replicate_add, List.append_assoc]
  simpa only [SourceClauseGenericCallback.blockCircuit,
    falseBlockCost, js, s₀, c₀, s₁, c₁, hp, hc] using h

noncomputable def trueBlockCost {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count : List Bool) : ℕ :=
  let s₀ := (encodeClause (unit (negative (base n r k)))).reverse ++ saved
  let c₀ := true :: count
  let ps := List.ofFn (fun p : Fin (q + 1) => p)
  let s₁ := foldSaved (trueGateBytes hq row n r k) ps s₀
  let c₁ := List.replicate (3 * (q + 1)) true ++ c₀
  unitCost row n r k 0 false saved output count +
    (listCost (trueGateCost hq row n r k) (trueGateBytes hq row n r k)
      ps s₀ output c₀ +
      unitCost row n r k (q + 1) true s₁ output c₁ + 1) + 1

theorem true_block_source_bounded {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count : List Bool)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    Circuit.BoundedRun (SourceClauseGenericTrue.blockCircuit hq k)
      (trueBlockCost hq row n r k saved output count)
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterBlank.bank row n r
        ((clauseFields (chain (base n r k)
          (tupleClause hq k (rowQuery row) true))).reverse ++ saved)
        output (List.replicate (3 * q + 5) true ++ count)) := by
  let s₀ := (encodeClause (unit (negative (base n r k)))).reverse ++ saved
  let c₀ := true :: count
  let ps := List.ofFn (fun p : Fin (q + 1) => p)
  let s₁ := foldSaved (trueGateBytes hq row n r k) ps s₀
  let c₁ := List.replicate (3 * (q + 1)) true ++ c₀
  have h₀ := opening_bounded row n r k saved output count
  have h₁ := true_gates_bounded hq row n r k ps s₀ output c₀ hquery
  have h₂ := true_closing_bounded row n r k s₁ output c₁
  have h₁₂ := Circuit.seq_bounded_run
    (SourceClauseGenericTrue.gateListCircuit hq k ps)
    (SourceClauseGenericTrue.closingCircuit k)
    (SourceClauseRowWriterBlank.bank row n r s₀ output c₀)
    (SourceClauseRowWriterBlank.bank row n r s₁ output c₁)
    (SourceClauseRowWriterBlank.bank row n r
      ((encodeClause (unit (positive (base n r k + (q + 1))))).reverse ++ s₁)
      output (true :: c₁))
    (listCost (trueGateCost hq row n r k) (trueGateBytes hq row n r k)
      ps s₀ output c₀)
    (unitCost row n r k (q + 1) true s₁ output c₁)
    (by simpa [ps, c₁, s₁] using h₁) h₂
  have h := Circuit.seq_bounded_run
    (openingCircuit k)
    (Circuit.seq (SourceClauseGenericTrue.gateListCircuit hq k ps)
      (SourceClauseGenericTrue.closingCircuit k))
    (SourceClauseRowWriterBlank.bank row n r saved output count)
    (SourceClauseRowWriterBlank.bank row n r s₀ output c₀)
    (SourceClauseRowWriterBlank.bank row n r
      ((encodeClause (unit (positive (base n r k + (q + 1))))).reverse ++ s₁)
      output (true :: c₁))
    (unitCost row n r k 0 false saved output count)
    (listCost (trueGateCost hq row n r k) (trueGateBytes hq row n r k)
      ps s₀ output c₀ +
      unitCost row n r k (q + 1) true s₁ output c₁ + 1)
    h₀ h₁₂
  have hp := SourceClauseGenericTrue.source_payload hq row n r k saved
  rw [← true_fold_eq] at hp
  have hc : true :: c₁ =
      List.replicate (3 * q + 5) true ++ count := by
    dsimp [c₁, c₀]
    rw [show 3 * q + 5 = 1 + (3 * (q + 1) + 1) by omega,
      List.replicate_add]
    simp [List.replicate_add, List.append_assoc]
  simpa only [SourceClauseGenericTrue.blockCircuit,
    trueBlockCost, ps, s₀, c₀, s₁, c₁, hp, hc] using h

end EthInapproximability.CurrentPaper.SourceClauseGenericCircuitClock
