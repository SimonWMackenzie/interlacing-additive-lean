import Paper2.AFrontTransducer
import Paper2.EncodedSelectedOutput

/-!
# The D-A3 projection machine (lane `owner:a-front-1`)

Private lane module, 27 September 2026. Paper A, lock v12.

Author decision D-A3 (`AUTHOR_DECISIONS_2026-09-27.md`, 27 September 2026): "Input: the matrix
part of what the reduction prints, `(rows, cols, table)` (option (c), a projection machine from
`outputBits`)." D-Y3: "the same format as D-A3".

Lock text implemented: v12 `sections/01-introduction.tex:72-76` ("An additive-error-$a$
estimator returns a number $\widehat D(M)$ with $|\widehat D(M)-\D(M)|\le a$ ... The numerical
output must permit polynomial-time comparison with binary rationals of polynomial length, as
required by the decision procedure using the estimator."): the decision procedure feeds the
estimator the matrix `M` printed by the reduction and compares against the printed budget `B`.

The reduction prints `EncodedSelectedOutput.outputBits … t =
EncodedCommunication.encodeInstance ⟨rows, cols, budget, table⟩ =
natField rows ++ natField cols ++ natField budget ++ table`. Two fixed one-pass machines
(`AFrontTransducer`, linear clock, exact output on EVERY word):

* `matrixMachine` computes `matrixPart`; on every `encodeInstance i` it prints
  `matrixWord i.rows i.cols i.table = natField rows ++ natField cols ++ table`
  (`matrixPart_encodeInstance`), in particular on the reduction's printed word
  (`matrixPart_outputBits`);
* `thresholdMachine` computes `thresholdPart`; on every `encodeInstance i` it prints
  `natField i.threshold` (`thresholdPart_encodeInstance`, `thresholdPart_outputBits`).

`matrixWord` is defined with exactly the body of lane `owner:a-model-1`'s
`Paper2.AModel.matrixWord` (`a-model-owner-1/AModelEstimator.lean:58`, private, not imported);
the two agree by `rfl` once both are admitted. Its relation to `encodeInstance` is
`encodeInstance_eq_insert`.

No ledger row is closed by this module.
-/

namespace AFront.Projection

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open AFront.Transducer

/-- D-A3 matrix-only word (lock `01-introduction.tex:72-73`; decision D-A3 "the matrix part of
what the reduction prints, `(rows, cols, table)`"): the admitted `encodeInstance` word without
its threshold field. Same body as `Paper2.AModel.matrixWord` (lane a-model-1). -/
def matrixWord (rows cols : ℕ) (table : List Bool) : List Bool :=
  natField rows ++ natField cols ++ table

/-- The admitted instance word is the matrix word with the threshold field inserted after the
two dimension fields. -/
theorem encodeInstance_eq_insert (i : Instance) :
    encodeInstance i = natField i.rows ++ natField i.cols ++ natField i.threshold ++ i.table :=
  rfl

inductive PS
  | rTag | rBit | cTag | cBit | tTag | tBit | table
  deriving DecidableEq, Fintype

/-- The shared field parser (rows field, cols field, threshold field, raw table). -/
def parse : PS → Bool → PS
  | .rTag, true => .rBit
  | .rTag, false => .cTag
  | .rBit, _ => .rTag
  | .cTag, true => .cBit
  | .cTag, false => .tTag
  | .cBit, _ => .cTag
  | .tTag, true => .tBit
  | .tTag, false => .table
  | .tBit, _ => .tTag
  | .table, _ => .table

/-- Emit everything except the threshold field. -/
def matrixSpec : Spec PS where
  step s b _ := parse s b
  emit s b := match s with
    | .tTag | .tBit => []
    | _ => [b]
  op _ _ := .keep
  fin _ := []
  incBy := 0
  bound := 1
  emit_le s b := by cases s <;> simp
  fin_le _ := by simp

/-- Emit only the threshold field. -/
def thresholdSpec : Spec PS where
  step s b _ := parse s b
  emit s b := match s with
    | .tTag | .tBit => [b]
    | _ => []
  op _ _ := .keep
  fin _ := []
  incBy := 0
  bound := 1
  emit_le s b := by cases s <;> simp
  fin_le _ := by simp

/-- The function computed by the matrix projection machine (on every word). -/
def matrixPart (w : List Bool) : List Bool := matrixSpec.out .rTag 0 w

/-- The function computed by the threshold projection machine (on every word). -/
def thresholdPart (w : List Bool) : List Bool := thresholdSpec.out .rTag 0 w

/-- A field read in state `tag` (with bit state `bitS`, exit `exit`) by a keep-only transducer. -/
theorem out_field (P : Spec PS) (hop : ∀ s b, P.op s b = .keep)
    (tag bitS exit : PS) (hpt : ∀ x, P.step tag true x = bitS) (hpb : ∀ b x, P.step bitS b x = tag)
    (hpf : ∀ x, P.step tag false x = exit) (emits : Bool)
    (het : ∀ b, P.emit tag b = if emits then [b] else [])
    (heb : ∀ b, P.emit bitS b = if emits then [b] else [])
    (bs rest : List Bool) :
    P.out tag 0 (field bs ++ rest) = (if emits then field bs else []) ++ P.out exit 0 rest := by
  have hc : ∀ s b w, P.out s 0 (b :: w) = P.emit s b ++ P.out (P.step s b true) 0 w := by
    intro s b w
    rw [Spec.out_cons]
    simp [Spec.next, hop]
  induction bs with
  | nil =>
      simp only [field, List.cons_append, List.nil_append]
      rw [hc, het, hpf]
  | cons b bs ih =>
      simp only [field, List.cons_append]
      rw [hc, het, hpt, hc, heb, hpb, ih]
      cases emits <;> simp

theorem matrix_table (l : List Bool) : matrixSpec.out .table 0 l = l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
      rw [Spec.out_cons]
      show [b] ++ matrixSpec.out .table 0 l = b :: l
      rw [ih]; rfl

theorem threshold_table (l : List Bool) : thresholdSpec.out .table 0 l = [] := by
  induction l with
  | nil => rfl
  | cons b l ih =>
      rw [Spec.out_cons]
      show [] ++ thresholdSpec.out .table 0 l = []
      rw [ih]; rfl

/-- **Projection identity (matrix).** On every instance word the matrix projection prints the
matrix-only word. -/
theorem matrixPart_encodeInstance (i : Instance) :
    matrixPart (encodeInstance i) = matrixWord i.rows i.cols i.table := by
  have hop : ∀ s b, matrixSpec.op s b = .keep := fun _ _ => rfl
  unfold matrixPart
  rw [encodeInstance_eq_insert, List.append_assoc, List.append_assoc, natField,
    out_field matrixSpec hop .rTag .rBit .cTag (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
      true (fun _ => rfl) (fun _ => rfl), natField,
    out_field matrixSpec hop .cTag .cBit .tTag (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
      true (fun _ => rfl) (fun _ => rfl), natField,
    out_field matrixSpec hop .tTag .tBit .table (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
      false (fun _ => rfl) (fun _ => rfl), matrix_table]
  simp [matrixWord, natField, List.append_assoc]

/-- **Projection identity (threshold).** -/
theorem thresholdPart_encodeInstance (i : Instance) :
    thresholdPart (encodeInstance i) = natField i.threshold := by
  have hop : ∀ s b, thresholdSpec.op s b = .keep := fun _ _ => rfl
  unfold thresholdPart
  rw [encodeInstance_eq_insert, List.append_assoc, List.append_assoc, natField,
    out_field thresholdSpec hop .rTag .rBit .cTag (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
      false (fun _ => rfl) (fun _ => rfl), natField,
    out_field thresholdSpec hop .cTag .cBit .tTag (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
      false (fun _ => rfl) (fun _ => rfl), natField,
    out_field thresholdSpec hop .tTag .tBit .table (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
      true (fun _ => rfl) (fun _ => rfl), threshold_table]
  simp [natField]

/-! ## The machines -/

/-- THE fixed D-A3 matrix projection machine. -/
noncomputable def matrixMachine : BitMachine.Machine := Transducer.machine matrixSpec PS.rTag

/-- THE fixed threshold projection machine. -/
noncomputable def thresholdMachine : BitMachine.Machine := Transducer.machine thresholdSpec PS.rTag

/-- **Matrix projection (exact, charged, every word).** -/
theorem matrixMachine_outputs (w : List Bool) :
    matrixMachine.OutputsWithin w (matrixPart w) (3 * (w.length + 1)) :=
  Transducer.machine_outputs_linear matrixSpec PS.rTag w

/-- **Threshold projection (exact, charged, every word).** -/
theorem thresholdMachine_outputs (w : List Bool) :
    thresholdMachine.OutputsWithin w (thresholdPart w) (3 * (w.length + 1)) :=
  Transducer.machine_outputs_linear thresholdSpec PS.rTag w

theorem matrixMachine_encodeInstance (i : Instance) :
    matrixMachine.OutputsWithin (encodeInstance i) (matrixWord i.rows i.cols i.table)
      (3 * ((encodeInstance i).length + 1)) := by
  have h := matrixMachine_outputs (encodeInstance i)
  rwa [matrixPart_encodeInstance] at h

theorem thresholdMachine_encodeInstance (i : Instance) :
    thresholdMachine.OutputsWithin (encodeInstance i) (natField i.threshold)
      (3 * ((encodeInstance i).length + 1)) := by
  have h := thresholdMachine_outputs (encodeInstance i)
  rwa [thresholdPart_encodeInstance] at h

/-! ## On the reduction's printed word -/

open Paper2.EncodedSelectedOutput Paper2.TotalFiniteConstructorScratch

/-- **D-A3 projection of the printed word (matrix).** On the word the uniform reduction prints,
`matrixMachine` prints exactly the matrix-only word of the selected table: rows, cols and the
row-major table bits of `(select …).table t`. -/
theorem matrixMachine_outputBits {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select hn edge Δ γ k).Tape) :
    matrixMachine.OutputsWithin (outputBits hn edge Δ γ k t)
      (matrixWord (select hn edge Δ γ k).rows (select hn edge Δ γ k).cols
        ((select hn edge Δ γ k).table t).bits)
      (3 * ((outputBits hn edge Δ γ k t).length + 1)) :=
  matrixMachine_encodeInstance (selectedInstance hn edge Δ γ k t)

/-- **D-A3 projection of the printed word (threshold).** `thresholdMachine` prints exactly the
canonical field of the public budget `B = (select …).budget`. -/
theorem thresholdMachine_outputBits {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select hn edge Δ γ k).Tape) :
    thresholdMachine.OutputsWithin (outputBits hn edge Δ γ k t)
      (natField (select hn edge Δ γ k).budget)
      (3 * ((outputBits hn edge Δ γ k t).length + 1)) :=
  thresholdMachine_encodeInstance (selectedInstance hn edge Δ γ k t)

/-- The matrix word of the printed word decodes back to the selected table (row-major bits of
exactly `rows · cols` entries). -/
theorem matrixWord_outputBits_readback {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select hn edge Δ γ k).Tape) :
    readNat (matrixWord (select hn edge Δ γ k).rows (select hn edge Δ γ k).cols
        ((select hn edge Δ γ k).table t).bits) =
      some ((select hn edge Δ γ k).rows,
        natField (select hn edge Δ γ k).cols ++ ((select hn edge Δ γ k).table t).bits) ∧
    readNat (natField (select hn edge Δ γ k).cols ++ ((select hn edge Δ γ k).table t).bits) =
      some ((select hn edge Δ γ k).cols, ((select hn edge Δ γ k).table t).bits) ∧
    ((select hn edge Δ γ k).table t).bits.length =
      (select hn edge Δ γ k).rows * (select hn edge Δ γ k).cols := by
  refine ⟨?_, ?_, ((select hn edge Δ γ k).table t).length⟩
  · simp [matrixWord, List.append_assoc, readNat_append]
  · simp [readNat_append]

/-- The threshold word decodes back to the budget. -/
theorem threshold_readback (B : ℕ) : readNat (natField B) = some (B, []) := by
  simpa using readNat_append B []

#print axioms matrixMachine_outputs
#print axioms thresholdMachine_outputs
#print axioms matrixPart_encodeInstance
#print axioms thresholdPart_encodeInstance
#print axioms matrixMachine_outputBits
#print axioms thresholdMachine_outputBits
#print axioms matrixWord_outputBits_readback
#print axioms threshold_readback

end AFront.Projection
