import Paper2.AFrontProjection
import EthInapproximability.CurrentPaper.EncodedComplexity

/-!
# The D-A3 split machine: matrix word and threshold from ONE machine (lane `owner:a-front-1`)

Private lane module, 27 September 2026. Paper A, lock v12, decision D-A3 (the estimator reads
the matrix part `(rows, cols, table)` of what the reduction prints; the decision procedure
compares with the printed threshold, lock `sections/01-introduction.tex:72-76`).

`splitMachine` is ONE fixed machine which on the printed word `encodeInstance i` prints
`pair (matrixWord i.rows i.cols i.table) (natField i.threshold)` (the matrix word as the
self-delimiting first field, the threshold field as the raw second field), so that the admitted
`PairMap` combinator can run an estimator on the first field while keeping the threshold.

Physical program (four Boolean stacks: input, output, matrix buffer, threshold buffer; finite
control `PS × Option Bool`): `scan` parses the input with the same field parser as
`AFrontProjection` and pushes each bit onto the matrix or the threshold buffer; `moveT` moves the
threshold buffer onto the output; `pushF` pushes the field terminator; `emit` pops the matrix
buffer and pushes each bit followed by a tag bit `true`. Exact transition count
`|w| + |thresholdPart w| + |matrixPart w| + 4`. No ledger row is closed.
-/

namespace AFront.Split

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.BitMachineEncoding
open AFront.Transducer (bank update0 update1 update2 update3 bank0 bank1 bank2 bank3)
open AFront.Projection

inductive SL
  | scan | moveT | pushF | emit
  deriving DecidableEq, Fintype

abbrev Ctl := PS × Option Bool
abbrev Stmt := TM2.Stmt (fun _ : Fin 4 => Bool) SL Ctl
abbrev Config := TM2.Cfg (fun _ : Fin 4 => Bool) SL Ctl

def inT : PS → Bool
  | .tTag | .tBit => true
  | _ => false

def bit (v : Ctl) : Bool := v.2.getD false

def program : SL → Stmt
  | .scan => .pop 0 (fun v b => (v.1, b))
      (.branch (fun v => v.2.isSome)
        (.branch (fun v => inT v.1)
          (.push 3 bit (.load (fun v => (parse v.1 (bit v), v.2)) (.goto fun _ => .scan)))
          (.push 2 bit (.load (fun v => (parse v.1 (bit v), v.2)) (.goto fun _ => .scan))))
        (.goto fun _ => .moveT))
  | .moveT => .pop 3 (fun v b => (v.1, b))
      (.branch (fun v => v.2.isSome) (.push 1 bit (.goto fun _ => .moveT)) (.goto fun _ => .pushF))
  | .pushF => .push 1 (fun _ => false) (.goto fun _ => .emit)
  | .emit => .pop 2 (fun v b => (v.1, b))
      (.branch (fun v => v.2.isSome)
        (.push 1 bit (.push 1 (fun _ => true) (.goto fun _ => .emit))) .halt)

/-- THE fixed D-A3 split machine. -/
noncomputable def splitMachine : BitMachine.Machine :=
  ofFinite (0 : Fin 4) 1 SL.scan ((PS.rTag, none) : Ctl) program

/-- The two streams, stated through the projection specs (both have empty final emission). -/
theorem matrix_out (s : PS) (b : Bool) (w : List Bool) :
    matrixSpec.out s 0 (b :: w) = matrixSpec.emit s b ++ matrixSpec.out (parse s b) 0 w := by
  rw [AFront.Transducer.Spec.out_cons]; rfl

theorem threshold_out (s : PS) (b : Bool) (w : List Bool) :
    thresholdSpec.out s 0 (b :: w) = thresholdSpec.emit s b ++ thresholdSpec.out (parse s b) 0 w := by
  rw [AFront.Transducer.Spec.out_cons]; rfl

theorem scan_step (s : PS) (o : Option Bool) (b : Bool) (w out M T : List Bool) :
    advance program (⟨some .scan, (s, o), bank (b :: w) out M T⟩ : Config) =
      ⟨some .scan, (parse s b, some b),
        bank w out ((matrixSpec.emit s b).reverse ++ M) ((thresholdSpec.emit s b).reverse ++ T)⟩ := by
  cases s <;>
    simp [advance, TM2.step, program, TM2.stepAux, inT, bit, matrixSpec, thresholdSpec,
      update0, update2, update3]

theorem scan_run (w : List Bool) (s : PS) (o : Option Bool) (out M T : List Bool) :
    ∃ o' : Option Bool, ((advance program)^[w.length]) (⟨some .scan, (s, o), bank w out M T⟩ : Config) =
      ⟨some .scan, ((matrixSpec.last s 0 w).1, o'),
        bank [] out ((matrixSpec.out s 0 w).reverse ++ M) ((thresholdSpec.out s 0 w).reverse ++ T)⟩ := by
  induction w generalizing s o M T with
  | nil => exact ⟨o, rfl⟩
  | cons b w ih =>
      obtain ⟨o', h⟩ := ih (parse s b) (some b) ((matrixSpec.emit s b).reverse ++ M)
        ((thresholdSpec.emit s b).reverse ++ T)
      refine ⟨o', ?_⟩
      rw [List.length_cons, Function.iterate_succ_apply, scan_step, h, matrix_out, threshold_out]
      simp only [List.reverse_append, List.append_assoc]
      rfl

theorem scan_end (s : PS) (o : Option Bool) (out M T : List Bool) :
    advance program (⟨some .scan, (s, o), bank [] out M T⟩ : Config) =
      ⟨some .moveT, (s, none), bank [] out M T⟩ := by
  simp [advance, TM2.step, program, TM2.stepAux, update0]

theorem moveT_run (T out M : List Bool) (v : Ctl) :
    ∃ v' : Ctl, ((advance program)^[T.length + 1]) (⟨some .moveT, v, bank [] out M T⟩ : Config) =
      ⟨some .pushF, v', bank [] (T.reverse ++ out) M []⟩ := by
  induction T generalizing v out with
  | nil => exact ⟨(v.1, none), by simp [advance, TM2.step, program, TM2.stepAux, update3]⟩
  | cons b bs ih =>
      have hstep : advance program (⟨some .moveT, v, bank [] out M (b :: bs)⟩ : Config) =
          ⟨some .moveT, (v.1, some b), bank [] (b :: out) M bs⟩ := by
        simp [advance, TM2.step, program, TM2.stepAux, update1, update3, bit]
      obtain ⟨v', hv⟩ := ih (b :: out) (v.1, some b)
      refine ⟨v', ?_⟩
      rw [List.length_cons, Function.iterate_succ_apply, hstep, hv]
      simp [List.append_assoc]

theorem pushF_step (v : Ctl) (out M : List Bool) :
    advance program (⟨some .pushF, v, bank [] out M []⟩ : Config) =
      ⟨some .emit, v, bank [] (false :: out) M []⟩ := by
  simp [advance, TM2.step, program, TM2.stepAux, update1]

/-- Pushing a reversed buffer as field tags. -/
def pushField : List Bool → List Bool → List Bool
  | [], acc => acc
  | b :: bs, acc => pushField bs (true :: b :: acc)

theorem pushField_append (a b acc : List Bool) :
    pushField (a ++ b) acc = pushField b (pushField a acc) := by
  induction a generalizing acc with
  | nil => rfl
  | cons x a ih => exact ih _

theorem pushField_reverse (xs rest : List Bool) :
    pushField xs.reverse (false :: rest) = field xs ++ rest := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [List.reverse_cons, pushField_append, ih]
      rfl

theorem emit_run (M out : List Bool) (v : Ctl) :
    ∃ v' : Ctl, ((advance program)^[M.length + 1]) (⟨some .emit, v, bank [] out M []⟩ : Config) =
      ⟨none, v', bank [] (pushField M out) [] []⟩ := by
  induction M generalizing v out with
  | nil => exact ⟨(v.1, none), by simp [advance, TM2.step, program, TM2.stepAux, update2, pushField]⟩
  | cons b bs ih =>
      have hstep : advance program (⟨some .emit, v, bank [] out (b :: bs) []⟩ : Config) =
          ⟨some .emit, (v.1, some b), bank [] (true :: b :: out) bs []⟩ := by
        simp [advance, TM2.step, program, TM2.stepAux, update1, update2, bit]
      obtain ⟨v', hv⟩ := ih (true :: b :: out) (v.1, some b)
      refine ⟨v', ?_⟩
      rw [List.length_cons, Function.iterate_succ_apply, hstep, hv]
      rfl

theorem rawInit_eq (w : List Bool) :
    (rawInit (0 : Fin 4) SL.scan ((PS.rTag, none) : Ctl) w) =
      (⟨some .scan, (PS.rTag, none), bank w [] [] []⟩ : Config) := by
  simp only [rawInit]
  congr 1
  funext k; fin_cases k <;> rfl

/-- **Split (exact, charged, every word).** On EVERY word `w`, `splitMachine` prints exactly
`pair (matrixPart w) (thresholdPart w)`. -/
theorem splitMachine_outputs (w : List Bool) :
    splitMachine.OutputsWithin w (EncodedComplexity.pair (matrixPart w) (thresholdPart w))
      (w.length + (thresholdPart w).length + (matrixPart w).length + 4) := by
  obtain ⟨o', hscan⟩ := scan_run w PS.rTag none [] [] []
  set M := (matrixSpec.out PS.rTag 0 w).reverse ++ []
  set T := (thresholdSpec.out PS.rTag 0 w).reverse ++ []
  obtain ⟨v1, hT⟩ := moveT_run T [] M ((matrixSpec.last PS.rTag 0 w).1, none)
  obtain ⟨v2, hM⟩ := emit_run M (false :: (T.reverse ++ [])) v1
  have hrun : ((advance program)^[(M.length + 1) + 1 + (T.length + 1) + 1 + w.length])
      (rawInit (0 : Fin 4) SL.scan ((PS.rTag, none) : Ctl) w) =
      ⟨none, v2, bank [] (pushField M (false :: (T.reverse ++ []))) [] []⟩ := by
    rw [rawInit_eq, Function.iterate_add_apply, Function.iterate_add_apply,
      Function.iterate_add_apply, Function.iterate_add_apply, hscan, Function.iterate_one,
      scan_end, hT, pushF_step, hM]
  have hout : pushField M (false :: (T.reverse ++ [])) =
      EncodedComplexity.pair (matrixPart w) (thresholdPart w) := by
    simp only [M, T, List.append_nil, List.reverse_reverse]
    rw [pushField_reverse]
    rfl
  have hMl : M.length = (matrixPart w).length := by simp [M, matrixPart]
  have hTl : T.length = (thresholdPart w).length := by simp [T, thresholdPart]
  apply outputsWithin_of_raw_run (0 : Fin 4) 1 SL.scan ((PS.rTag, none) : Ctl) program w
    (EncodedComplexity.pair (matrixPart w) (thresholdPart w))
    ((M.length + 1) + 1 + (T.length + 1) + 1 + w.length) _ (by omega)
  · rw [hrun]
  · rw [hrun]; exact hout

/-- **D-A3 split of an instance word.** -/
theorem splitMachine_encodeInstance (i : Instance) :
    splitMachine.OutputsWithin (encodeInstance i)
      (EncodedComplexity.pair (matrixWord i.rows i.cols i.table) (natField i.threshold))
      (3 * ((encodeInstance i).length + 1)) := by
  have h := splitMachine_outputs (encodeInstance i)
  have hm := matrixPart_encodeInstance i
  have ht := thresholdPart_encodeInstance i
  rw [hm, ht] at h
  apply BitMachine.outputsWithin_mono _ h
  have hl : (encodeInstance i).length =
      (matrixWord i.rows i.cols i.table).length + (natField i.threshold).length := by
    simp only [encodeInstance, matrixWord, List.length_append]
    omega
  have h1 : 1 ≤ (natField i.threshold).length := by
    simp [natField, field_length]
  omega

open Paper2.EncodedSelectedOutput Paper2.TotalFiniteConstructorScratch in
/-- **D-A3 split of the reduction's printed word.** On `outputBits`, `splitMachine` prints
`pair (matrixWord rows cols tableBits) (natField budget)` of the selected output. -/
theorem splitMachine_outputBits {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select hn edge Δ γ k).Tape) :
    splitMachine.OutputsWithin (outputBits hn edge Δ γ k t)
      (EncodedComplexity.pair
        (matrixWord (select hn edge Δ γ k).rows (select hn edge Δ γ k).cols
          ((select hn edge Δ γ k).table t).bits)
        (natField (select hn edge Δ γ k).budget))
      (3 * ((outputBits hn edge Δ γ k t).length + 1)) :=
  splitMachine_encodeInstance (selectedInstance hn edge Δ γ k t)

#print axioms splitMachine_outputs
#print axioms splitMachine_encodeInstance
#print axioms splitMachine_outputBits

end AFront.Split
