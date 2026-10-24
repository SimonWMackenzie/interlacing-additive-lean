import Paper2.A4Loops
import Paper2.A4Kof
import Paper2.A4PairMap
import Paper2.HeaderWordRun
import EthInapproximability.CurrentPaper.BinarySuccessorMachine
import EthInapproximability.CurrentPaper.UnaryBinaryEncoding

/-!
# Paper A (lock v12), lane `owner:a-eth-4`, segment 1 (obstacle O1): ONE header machine for every gap

The admitted A27 header `HeaderWordRun.machine k` is one machine PER FIXED gap `k`. This module
builds ONE fixed finite machine `GrowHeader.machine` which, on `pair (1^k) (encodeInstance i)`,
prints `HeaderWordRun.headeredWord k i = natField (2 * i.threshold + k) ++ matrixWord` for EVERY
`k ≥ 1`, and the fixed composite `KHeader.machine` which, on `pair (encode f) (encodeInstance i)`,
prints `headeredWord (kOf f.variables) i` (admitted `KofFront.KMachine`, admitted `PairMap`).

The arithmetic is done in the machine: the threshold bits `B.bits` are doubled by one pushed
`false`, and the unary gap is added by `k` literal carry loops (one per popped counter bit), each
computing the admitted list function `BinarySuccessorMachine.successor`; the value identity is the
admitted `FixedGapHeader.addBits_nat`. The table is never moved: the clock does not mention it.

Every step is one `TM2.step` of a literal statement; nothing is inserted; the machine starts from
`Machine.init`. No ledger row is closed. Nothing here is admitted.
-/

namespace Paper2.AEth4

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.BinarySuccessorMachine (successor carryCount carryCount_le_length)
open Paper2.Unit4Shell.Loops

section Generic

variable {K Λ W : Type*} [DecidableEq K]

/-- One carry step of the LSB-first successor on stack `A`, with the carried zeros on `T`. -/
def carryStmt (A T : K) (here next : Λ) : TM2.Stmt (fun _ : K => Bool) Λ (Option Bool × W) :=
  .pop A setBit (.branch (fun v => v.1.getD false)
    (.push T (fun _ => false) (.goto fun _ => here))
    (.push A (fun _ => true) (.goto fun _ => next)))

/-- Pop one counter bit; branch on whether there was one. -/
def countStmt (C : K) (yes no : Λ) : TM2.Stmt (fun _ : K => Bool) Λ (Option Bool × W) :=
  .pop C setBit (.branch (fun v => v.1.isSome) (.goto fun _ => yes) (.goto fun _ => no))

theorem successor_eq (q : List Bool) :
    successor q = List.replicate (carryCount q) false ++ true :: q.drop (carryCount q + 1) := by
  induction q with
  | nil => rfl
  | cons b q ih =>
      cases b with
      | false => rfl
      | true =>
          simp only [successor, carryCount, List.replicate_succ, List.cons_append, ih,
            List.drop_succ_cons]

theorem iterate_successor_length_le (k : ℕ) (q : List Bool) :
    (successor^[k] q).length ≤ q.length + k := by
  induction k generalizing q with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      have h1 := ih (successor q)
      have h2 := UnaryBinaryEncoding.successor_length q
      omega

/-- `successor^[k] (false :: B.bits) = (2 * B + k).bits` for every `k ≥ 1`. -/
theorem iterate_successor_double (B k : ℕ) (hk : 1 ≤ k) :
    successor^[k] (false :: B.bits) = (2 * B + k).bits := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Function.iterate_succ_apply]
  have h1 : successor (false :: B.bits) = (2 * B + 1).bits := by
    rw [successor, ← Nat.bits_append_bit B true (fun _ => rfl)]
    congr 1
  rw [h1]
  have h2 := Paper2.FixedGapHeader.addBits_nat j (2 * B + 1)
  simp only [Paper2.FixedGapHeader.addBits] at h2
  rw [h2]
  congr 1
  omega

variable (P : Λ → TM2.Stmt (fun _ : K => Bool) Λ (Option Bool × W))

theorem carry_loop (A T : K) (here next : Λ) (hAT : A ≠ T)
    (hP : P here = carryStmt A T here next) :
    ∀ (q : List Bool) (j : ℕ) (S : K → List Bool) (o : Option Bool) (w : W),
      S A = q → S T = List.replicate j false →
      ∃ (o' : Option Bool) (S' : K → List Bool),
        (advance P)^[carryCount q + 1] ⟨some here, (o, w), S⟩ = ⟨some next, (o', w), S'⟩ ∧
        S' A = true :: q.drop (carryCount q + 1) ∧
        S' T = List.replicate (j + carryCount q) false ∧
        ∀ x, x ≠ A → x ≠ T → S' x = S x := by
  intro q
  induction q with
  | nil =>
      intro j S o w hA hT
      refine ⟨none, Function.update S A [true], ?_, by simp, ?_, ?_⟩
      · simp [carryCount, advance, TM2.step, TM2.stepAux, hP, carryStmt, setBit, hA]
      · simp [carryCount, Function.update_of_ne hAT.symm, hT]
      · intro x hx _
        simp [Function.update_of_ne hx]
  | cons b q ih =>
      intro j S o w hA hT
      cases b with
      | false =>
          refine ⟨some false, Function.update S A (true :: q), ?_, by simp [carryCount], ?_, ?_⟩
          · simp [carryCount, advance, TM2.step, TM2.stepAux, hP, carryStmt, setBit, hA]
          · simp [carryCount, Function.update_of_ne hAT.symm, hT]
          · intro x hx _
            simp [Function.update_of_ne hx]
      | true =>
          have h1 : advance P ⟨some here, (o, w), S⟩ = ⟨some here, (some true, w),
              Function.update (Function.update S A q) T (false :: S T)⟩ := by
            simp [advance, TM2.step, TM2.stepAux, hP, carryStmt, setBit, hA,
              Function.update_of_ne hAT.symm]
          obtain ⟨o', S', hrun, hA', hT', hx'⟩ := ih (j + 1)
            (Function.update (Function.update S A q) T (false :: S T)) (some true) w
            (by rw [Function.update_of_ne hAT, Function.update_self])
            (by rw [Function.update_self, hT, List.replicate_succ])
          refine ⟨o', S', ?_, ?_, ?_, ?_⟩
          · rw [show carryCount (true :: q) + 1 = (carryCount q + 1) + 1 by
              simp [carryCount], Function.iterate_succ_apply, h1, hrun]
          · rw [hA']
            simp [carryCount]
          · rw [hT']
            congr 1
            simp [carryCount]
            omega
          · intro x hx hx2
            rw [hx' x hx hx2, Function.update_of_ne hx2, Function.update_of_ne hx]

theorem count_loop (C A T : K) (cnt car res out : Λ) (hCA : C ≠ A) (hCT : C ≠ T)
    (hAT : A ≠ T)
    (hC : P cnt = countStmt C car out) (hK : P car = carryStmt A T car res)
    (hR : P res = moveStmt T A res cnt) :
    ∀ (k : ℕ) (q : List Bool) (S : K → List Bool) (o : Option Bool) (w : W),
      S C = List.replicate k true → S A = q → S T = [] →
      ∃ n, n ≤ k * (2 * (q.length + k) + 4) + 1 ∧ ∃ S' : K → List Bool,
        (advance P)^[n] ⟨some cnt, (o, w), S⟩ = ⟨some out, (none, w), S'⟩ ∧
        S' C = [] ∧ S' A = successor^[k] q ∧ S' T = [] ∧
        ∀ x, x ≠ C → x ≠ A → x ≠ T → S' x = S x := by
  intro k
  induction k with
  | zero =>
      intro q S o w hC0 hA hT
      refine ⟨1, by omega, Function.update S C [], ?_, by simp, ?_, ?_, ?_⟩
      · simp at hC0
        simp [advance, TM2.step, TM2.stepAux, hC, countStmt, setBit, hC0]
      · rw [Function.update_of_ne hCA.symm, hA]
        rfl
      · rw [Function.update_of_ne hCT.symm, hT]
      · intro x hx _ _
        rw [Function.update_of_ne hx]
  | succ k ih =>
      intro q S o w hC0 hA hT
      rw [List.replicate_succ] at hC0
      have h1 : advance P ⟨some cnt, (o, w), S⟩ =
          ⟨some car, (some true, w), Function.update S C (List.replicate k true)⟩ := by
        simp [advance, TM2.step, TM2.stepAux, hC, countStmt, setBit, hC0]
      set S1 := Function.update S C (List.replicate k true) with hS1
      obtain ⟨o2, S2, h2, hA2, hT2, hx2⟩ := carry_loop P A T car res hAT hK q 0 S1 (some true) w
        (by rw [hS1, Function.update_of_ne hCA.symm]; exact hA)
        (by rw [hS1, Function.update_of_ne hCT.symm, hT]; rfl)
      have h3 := move_loop P T A res cnt hAT.symm hR
        (List.replicate (0 + carryCount q) false) S2 o2 w hT2
      set S3 := Function.update (Function.update S2 A
        ((List.replicate (0 + carryCount q) false).reverse ++ S2 A)) T [] with hS3
      have hA3 : S3 A = successor q := by
        rw [hS3, Function.update_of_ne hAT, Function.update_self, hA2, List.reverse_replicate,
          successor_eq]
        simp
      have hC3 : S3 C = List.replicate k true := by
        rw [hS3, Function.update_of_ne hCT, Function.update_of_ne hCA, hx2 C hCA hCT, hS1,
          Function.update_self]
      have hT3 : S3 T = [] := by rw [hS3, Function.update_self]
      obtain ⟨n, hn, S', h4, hC', hA', hT', hx'⟩ := ih (successor q) S3 none w hC3 hA3 hT3
      refine ⟨1 + (carryCount q + 1) + ((List.replicate (0 + carryCount q) false).length + 1) + n,
        ?_, S', ?_, hC', ?_, hT', ?_⟩
      · have hs := UnaryBinaryEncoding.successor_length q
        have hc := carryCount_le_length q
        have hm : k * (2 * ((successor q).length + k) + 4) ≤ k * (2 * (q.length + 1 + k) + 4) :=
          Nat.mul_le_mul_left _ (by omega)
        simp only [List.length_replicate]
        nlinarith
      · exact iter_chain (iter_chain (iter_chain (show (advance P)^[1] _ = _ from h1) h2) h3) h4
      · rw [hA', Function.iterate_succ_apply]
      · intro x hxC hxA hxT
        rw [hx' x hxC hxA hxT, hS3, Function.update_of_ne hxT, Function.update_of_ne hxA,
          hx2 x hxA hxT, hS1, Function.update_of_ne hxC]

end Generic

namespace GrowHeader

inductive HL
  | p1 | p2 | p3 | p4 | p5 | p6 | cnt | car | res | e1 | e2 | e3 | e4 | e5 | e6 | e7 | done
  deriving DecidableEq, Fintype

abbrev Stack := Fin 7
abbrev Control := Option Bool × Unit

/-- Stacks: `0` input/output, `1` unary counter, `2` rows (reversed), `3` cols (reversed),
`4` threshold scratch, `5` the binary number (LSB on top), `6` carried zeros. -/
def program : HL → TM2.Stmt (fun _ : Stack => Bool) HL Control
  | .p1 => parseStmt 0 1 .p1 .p2
  | .p2 => parseStmt 0 2 .p2 .p3
  | .p3 => parseStmt 0 3 .p3 .p4
  | .p4 => parseStmt 0 4 .p4 .p5
  | .p5 => moveStmt 4 5 .p5 .p6
  | .p6 => pushFalseStmt 5 .cnt
  | .cnt => countStmt 1 .car .e1
  | .car => carryStmt 5 6 .car .res
  | .res => moveStmt 6 5 .res .cnt
  | .e1 => pushFalseStmt 0 .e2
  | .e2 => emitStmt 3 0 .e2 .e3
  | .e3 => pushFalseStmt 0 .e4
  | .e4 => emitStmt 2 0 .e4 .e5
  | .e5 => moveStmt 5 4 .e5 .e6
  | .e6 => pushFalseStmt 0 .e7
  | .e7 => emitStmt 4 0 .e7 .done
  | .done => .halt

/-- THE fixed uniform header machine (input and output stack `0`). -/
noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Stack) (0 : Stack) HL.p1 ((none, ()) : Control) program

/-- The explicit clock, in the gap `k` and the three header fields only (never the table). -/
def clock (k r c B : ℕ) : ℕ :=
  (k + 1) + (r.bits.length + 1) + (c.bits.length + 1) + (B.bits.length + 1) +
    (B.bits.length + 1) + 1 +
    (k * (2 * ((B.bits.length + 1) + k) + 4) + 1) +
    1 + (c.bits.length + 1) + 1 + (r.bits.length + 1) +
    ((B.bits.length + 1 + k) + 1) + 1 + ((B.bits.length + 1 + k) + 1) + 1

/-- **Uniform header, raw form.** For EVERY `k`, on
`field (1^k) ++ natField r ++ natField c ++ natField B ++ table` the fixed machine prints
`field (successor^[k] (false :: B.bits)) ++ natField r ++ natField c ++ table`. -/
theorem machine_outputs_raw (k r c B : ℕ) (table : List Bool) :
    machine.OutputsWithin
      (field (List.replicate k true) ++ (field r.bits ++ (field c.bits ++ (field B.bits ++ table))))
      (field (successor^[k] (false :: B.bits)) ++ (field r.bits ++ (field c.bits ++ table)))
      (clock k r c B) := by
  set inW := field (List.replicate k true) ++
    (field r.bits ++ (field c.bits ++ (field B.bits ++ table))) with hinW
  let S0 : Stack → List Bool := fun j => if j = 0 then inW else []
  -- p1: the unary counter
  have e1 := parse_loop program (0 : Stack) 1 HL.p1 HL.p2 (by decide) rfl
    (List.replicate k true) (field r.bits ++ (field c.bits ++ (field B.bits ++ table))) S0
    none () (by simp [S0, hinW])
  set S1 := Function.update (Function.update S0 1 ((List.replicate k true).reverse ++ S0 1)) 0
    (field r.bits ++ (field c.bits ++ (field B.bits ++ table))) with hS1
  -- p2: rows
  have e2 := parse_loop program (0 : Stack) 2 HL.p2 HL.p3 (by decide) rfl
    r.bits (field c.bits ++ (field B.bits ++ table)) S1 (some false) () (by simp [hS1])
  set S2 := Function.update (Function.update S1 2 (r.bits.reverse ++ S1 2)) 0
    (field c.bits ++ (field B.bits ++ table)) with hS2
  -- p3: cols
  have e3 := parse_loop program (0 : Stack) 3 HL.p3 HL.p4 (by decide) rfl
    c.bits (field B.bits ++ table) S2 (some false) () (by simp [hS2])
  set S3 := Function.update (Function.update S2 3 (c.bits.reverse ++ S2 3)) 0
    (field B.bits ++ table) with hS3
  -- p4: threshold
  have e4 := parse_loop program (0 : Stack) 4 HL.p4 HL.p5 (by decide) rfl
    B.bits table S3 (some false) () (by simp [hS3])
  set S4 := Function.update (Function.update S3 4 (B.bits.reverse ++ S3 4)) 0 table with hS4
  have h44 : S4 4 = B.bits.reverse := by simp [hS4, hS3, hS2, hS1, S0]
  -- p5: threshold bits onto the number stack
  have e5 := move_loop program (4 : Stack) 5 HL.p5 HL.p6 (by decide) rfl
    B.bits.reverse S4 (some false) () h44
  rw [List.length_reverse] at e5
  set S5 := Function.update (Function.update S4 5 (B.bits.reverse.reverse ++ S4 5)) 4 []
    with hS5
  -- p6: double
  have e6 := pushFalse_step program (5 : Stack) HL.p6 HL.cnt rfl (none, ()) S5
  set S6 := Function.update S5 5 (false :: S5 5) with hS6
  have h61 : S6 1 = List.replicate k true := by simp [hS6, hS5, hS4, hS3, hS2, hS1, S0]
  have h65 : S6 5 = false :: B.bits := by simp [hS6, hS5, hS4, hS3, hS2, hS1, S0]
  have h66 : S6 6 = [] := by simp [hS6, hS5, hS4, hS3, hS2, hS1, S0]
  -- the counted carry loop
  obtain ⟨n, hn, S7, e7, h71, h75, h76, hx7⟩ := count_loop program (1 : Stack) 5 6
    HL.cnt HL.car HL.res HL.e1 (by decide) (by decide) (by decide) rfl rfl rfl
    k (false :: B.bits) S6 none () h61 h65 h66
  have h70 : S7 0 = table := by
    rw [hx7 0 (by decide) (by decide) (by decide)]
    simp [hS6, hS5, hS4]
  have h72 : S7 2 = r.bits.reverse := by
    rw [hx7 2 (by decide) (by decide) (by decide)]
    simp [hS6, hS5, hS4, hS3, hS2, hS1, S0]
  have h73 : S7 3 = c.bits.reverse := by
    rw [hx7 3 (by decide) (by decide) (by decide)]
    simp [hS6, hS5, hS4, hS3, hS2, hS1, S0]
  have h74 : S7 4 = [] := by
    rw [hx7 4 (by decide) (by decide) (by decide)]
    simp [hS6, hS5]
  set X := successor^[k] (false :: B.bits) with hX
  -- e1, e2: cols field
  have f1 := pushFalse_step program (0 : Stack) HL.e1 HL.e2 rfl (none, ()) S7
  set S8 := Function.update S7 0 (false :: S7 0) with hS8
  have f2 := emit_loop program (3 : Stack) 0 HL.e2 HL.e3 (by decide) rfl c.bits.reverse S8
    none () (by simp [hS8, h73])
  rw [List.length_reverse] at f2
  set S9 := Function.update (Function.update S8 0 (c.bits.reverse.foldl emitFold (S8 0))) 3 []
    with hS9
  have h90 : S9 0 = field c.bits ++ table := by
    simp only [hS9, Function.update_of_ne (by decide : (0 : Stack) ≠ 3), Function.update_self,
      hS8, h70]
    exact emit_reverse_field c.bits table
  -- e3, e4: rows field
  have f3 := pushFalse_step program (0 : Stack) HL.e3 HL.e4 rfl (none, ()) S9
  set S10 := Function.update S9 0 (false :: S9 0) with hS10
  have f4 := emit_loop program (2 : Stack) 0 HL.e4 HL.e5 (by decide) rfl r.bits.reverse S10
    none () (by simp [hS10, hS9, hS8, h72])
  rw [List.length_reverse] at f4
  set S11 := Function.update (Function.update S10 0 (r.bits.reverse.foldl emitFold (S10 0))) 2 []
    with hS11
  have h110 : S11 0 = field r.bits ++ (field c.bits ++ table) := by
    simp only [hS11, Function.update_of_ne (by decide : (0 : Stack) ≠ 2), Function.update_self,
      hS10, h90]
    exact emit_reverse_field r.bits _
  -- e5: reverse the number
  have f5 := move_loop program (5 : Stack) 4 HL.e5 HL.e6 (by decide) rfl X S11 none ()
    (by simp [hS11, hS10, hS9, hS8, h75])
  set S12 := Function.update (Function.update S11 4 (X.reverse ++ S11 4)) 5 [] with hS12
  have h124 : S12 4 = X.reverse := by simp [hS12, hS11, hS10, hS9, hS8, h74]
  -- e6, e7: the number field
  have f6 := pushFalse_step program (0 : Stack) HL.e6 HL.e7 rfl (none, ()) S12
  set S13 := Function.update S12 0 (false :: S12 0) with hS13
  have f7 := emit_loop program (4 : Stack) 0 HL.e7 HL.done (by decide) rfl X.reverse S13
    none () (by simp [hS13, h124])
  rw [List.length_reverse] at f7
  set S14 := Function.update (Function.update S13 0 (X.reverse.foldl emitFold (S13 0))) 4 []
    with hS14
  have h140 : S14 0 = field X ++ (field r.bits ++ (field c.bits ++ table)) := by
    have h130 : S13 0 = false :: (field r.bits ++ (field c.bits ++ table)) := by
      simp only [hS13, Function.update_self, hS12,
        Function.update_of_ne (by decide : (0 : Stack) ≠ 5),
        Function.update_of_ne (by decide : (0 : Stack) ≠ 4), h110]
    simp only [hS14, Function.update_of_ne (by decide : (0 : Stack) ≠ 4), Function.update_self,
      h130]
    exact emit_reverse_field X _
  have f8 := halt_step program HL.done rfl (none, ()) S14
  have hrun := iter_chain (iter_chain (iter_chain (iter_chain (iter_chain (iter_chain
    (iter_chain (iter_chain (iter_chain (iter_chain (iter_chain (iter_chain (iter_chain
    (iter_chain e1 e2) e3) e4) e5) (show (advance program)^[1] _ = _ from e6)) e7)
    (show (advance program)^[1] _ = _ from f1)) f2) (show (advance program)^[1] _ = _ from f3))
    f4) f5) (show (advance program)^[1] _ = _ from f6)) f7)
    (show (advance program)^[1] _ = _ from f8)
  have hraw : rawInit (0 : Stack) HL.p1 ((none, ()) : Control) inW =
      ⟨some HL.p1, (none, ()), S0⟩ := rfl
  have hXlen : X.length ≤ B.bits.length + 1 + k := by
    have := iterate_successor_length_le k (false :: B.bits)
    simpa [hX] using this
  have key : ∀ m, (advance program)^[m] (rawInit (0 : Stack) HL.p1 ((none, ()) : Control) inW) =
      ⟨none, (none, ()), S14⟩ → m ≤ clock k r c B →
      machine.OutputsWithin inW (field X ++ (field r.bits ++ (field c.bits ++ table)))
        (clock k r c B) := by
    intro m hm hle
    exact outputsWithin_of_raw_run (0 : Stack) (0 : Stack) HL.p1 ((none, ()) : Control)
      program inW _ m _ hle (by rw [hm]) (by rw [hm]; exact h140)
  rw [← hraw] at hrun
  refine key _ hrun ?_
  simp only [List.length_replicate, List.length_cons] at hn ⊢
  unfold clock
  omega

/-- **Uniform header, instance form.** ONE fixed machine: for every gap `k ≥ 1` and every
instance `i`, on `pair (1^k) (encodeInstance i)` it prints exactly the admitted A27 word
`HeaderWordRun.headeredWord k i = natField (2 * i.threshold + k) ++ matrixWord`. -/
theorem machine_outputs (k : ℕ) (hk : 1 ≤ k) (i : Instance) :
    machine.OutputsWithin (EncodedComplexity.pair (List.replicate k true) (encodeInstance i))
      (Paper2.HeaderWordRun.headeredWord k i) (clock k i.rows i.cols i.threshold) := by
  have h := machine_outputs_raw k i.rows i.cols i.threshold i.table
  rw [iterate_successor_double i.threshold k hk] at h
  simpa [EncodedComplexity.pair, encodeInstance, Paper2.HeaderWordRun.headeredWord,
    Paper2.HeaderWordRun.matrix, AFront.Projection.matrixWord, natField,
    List.append_assoc] using h

theorem clock_le (k : ℕ) (i : Instance) :
    clock k i.rows i.cols i.threshold ≤
      4 * ((EncodedComplexity.pair (List.replicate k true) (encodeInstance i)).length + 1) ^ 2 := by
  have hL := encodeInstance_length i
  simp only [EncodedComplexity.pair_length, List.length_replicate]
  unfold clock
  set r := i.rows.bits.length
  set c := i.cols.bits.length
  set b := i.threshold.bits.length
  set L := (encodeInstance i).length
  nlinarith

end GrowHeader

namespace KHeader

/-- THE fixed composite: `pair (encode f) (encodeInstance i) ↦ headeredWord (kOf N) i`. -/
noncomputable def machine : BitMachine.Machine :=
  BitMachineComposition.composition
    (Paper2.Unit4Shell.PairMap.machine Paper2.Unit4Shell.KofFront.KMachine) GrowHeader.machine

noncomputable def clock (f : EncodedCNF.Formula) (i : Instance) : ℕ :=
  (2 * (EncodedCNF.encode f).length + Paper2.Unit4Shell.KofFront.BK * (f.variables + 1) ^ 2 +
      2 * (Paper2.Unit4Shell.Asymptotics.kOf f.variables) + 6) +
    2 * (EncodedComplexity.pair (List.replicate (Paper2.Unit4Shell.Asymptotics.kOf f.variables) true)
      (encodeInstance i)).length + 2 +
    GrowHeader.clock (Paper2.Unit4Shell.Asymptotics.kOf f.variables) i.rows i.cols i.threshold

/-- **The header at the growing gap `k = kOf N`.** For every CNF `f` with `1 ≤ kOf N` and every
instance `i`, the ONE fixed machine prints `natField (2 * i.threshold + kOf N) ++ matrixWord`. -/
theorem machine_outputs (f : EncodedCNF.Formula) (hk : 1 ≤ Paper2.Unit4Shell.Asymptotics.kOf f.variables)
    (i : Instance) :
    machine.OutputsWithin (EncodedComplexity.pair (EncodedCNF.encode f) (encodeInstance i))
      (Paper2.HeaderWordRun.headeredWord (Paper2.Unit4Shell.Asymptotics.kOf f.variables) i) (clock f i) := by
  have h1 := Paper2.Unit4Shell.PairMap.machine_outputs
    (M := Paper2.Unit4Shell.KofFront.KMachine) (EncodedCNF.encode f)
    (List.replicate (Paper2.Unit4Shell.Asymptotics.kOf f.variables) true) (encodeInstance i) _
    (Paper2.Unit4Shell.KofFront.KMachine_outputs f)
  have h2 := GrowHeader.machine_outputs (Paper2.Unit4Shell.Asymptotics.kOf f.variables) hk i
  have h := BitMachineComposition.composition_outputsWithin _ _ h1 h2
  simpa [clock, List.length_replicate] using h

end KHeader

#print axioms successor_eq
#print axioms iterate_successor_double
#print axioms carry_loop
#print axioms count_loop
#print axioms GrowHeader.machine_outputs_raw
#print axioms GrowHeader.machine_outputs
#print axioms GrowHeader.clock_le
#print axioms KHeader.machine_outputs

end Paper2.AEth4
