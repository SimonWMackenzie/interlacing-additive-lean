import Paper2.RecursiveLabelCodec
import Paper2.LookupSeed
import EthInapproximability.CurrentPaper.MatrixReadAt
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import EthInapproximability.CurrentPaper.BitMachineClearBank
import Mathlib.Tactic

namespace Paper2.SeedEntryMachine

open Turing TM2.Stmt
open Paper2.RecursiveLabelCodecScratch
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

abbrev Stack := Fin 9
inductive Admin where | scan | restore | clear | finish
  deriving DecidableEq, Fintype
abbrev Label := Admin ⊕ MatrixReadAt.Label
abbrev Control := MatrixReadAt.Control × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def readInitial : MatrixReadAt.Control :=
  (none, none, (false, false), (false, false))

def embedRead : Fin 7 ↪ Stack :=
  ⟨fun i => i.castLE (by omega), by
    intro a b h
    exact Fin.ext (by simpa using congrArg Fin.val h)⟩

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl .scan =>
      pop 7 (fun v b => (v.1,b))
        (branch (fun v => v.2.getD false)
          (push 0 (fun _ => true) (push 8 (fun _ => true)
            (goto (fun _ => .inl .scan))))
          (push 8 (fun _ => false) (goto (fun _ => .inl .restore))))
  | .inl .restore =>
      pop 8 (fun v b => (v.1,b))
        (branch (fun v => v.2.isSome)
          (push 7 (fun v => v.2.getD false) (goto (fun _ => .inl .restore)))
          (load (fun _ => (readInitial,none))
            (goto (fun _ => .inr (.inl .scan)))))
  | .inl .clear =>
      BitMachineClearBank.clearStep 0 (.inl .clear) (.inl .finish)
  | .inl .finish => halt
  | .inr l =>
      BitMachineStackEmbedding.stmt embedRead Sum.inr
        (fun v => (v,none)) Prod.fst (some (.inl .clear))
        (MatrixReadAt.program l)

def cfg (l : Option Label) (v : Control)
    (row col idx scratch out : List Bool) : Config :=
  ⟨l,v,![idx,[],[],row,[],out,[],col,scratch]⟩

def initial (row col : List Bool) : Config :=
  cfg (some (.inl .scan)) (readInitial,none) row col [] [] []

def final (row col : List Bool) (answer : Bool) (v : Control) : Config :=
  cfg none v row col [] [] [answer]

def run (t : Nat) (c : Config) := ((advance program)^[t]) c

private theorem run_add {a b : Config} {t : Nat} (h : run t a = b) (u : Nat) :
    run (t+u) a = run u b := by
  rw [Nat.add_comm t u]
  simpa only [run, Function.iterate_add_apply] using congrArg ((advance program)^[u]) h

private theorem scan_true (v : Control) (row tail idx scratch out : List Bool) :
    run 1 (cfg (some (.inl .scan)) v row (true :: tail) idx scratch out) =
      cfg (some (.inl .scan)) (v.1,some true) row tail
        (true :: idx) (true :: scratch) out := by
  simp [run, cfg, program, advance, TM2.step, TM2.stepAux]
  funext i
  fin_cases i <;> simp [Function.update]

private theorem scan_false (v : Control) (row tail idx scratch out : List Bool) :
    run 1 (cfg (some (.inl .scan)) v row (false :: tail) idx scratch out) =
      cfg (some (.inl .restore)) (v.1,some false) row tail idx
        (false :: scratch) out := by
  simp [run, cfg, program, advance, TM2.step, TM2.stepAux]
  funext i
  fin_cases i <;> simp [Function.update]

private theorem restore_bit (v : Control) (row col idx scratch out : List Bool)
    (b : Bool) :
    run 1 (cfg (some (.inl .restore)) v row col idx (b :: scratch) out) =
      cfg (some (.inl .restore)) (v.1,some b) row (b :: col) idx scratch out := by
  cases b <;>
    simp [run, cfg, program, advance, TM2.step, TM2.stepAux] <;>
    (funext i; fin_cases i <;> simp [Function.update])

private theorem restore_done (v : Control) (row col idx out : List Bool) :
    run 1 (cfg (some (.inl .restore)) v row col idx [] out) =
      cfg (some (.inr (.inl .scan))) (readInitial,none) row col idx [] out := by
  simp [run, cfg, program, advance, TM2.step, TM2.stepAux]

private theorem rep_true_shift (j : Nat) (tail : List Bool) :
    List.replicate j true ++ true :: tail =
      true :: (List.replicate j true ++ tail) := by
  induction j with
  | zero => rfl
  | succ j ih => simpa [List.replicate_succ] using congrArg (true :: ·) ih

private theorem scan_prefix (j : Nat) (v : Control)
    (row tail idx scratch out : List Bool) :
    run j (cfg (some (.inl .scan)) v row
      (List.replicate j true ++ tail) idx scratch out) =
      cfg (some (.inl .scan)) (if j = 0 then v else (v.1,some true))
        row tail (List.replicate j true ++ idx)
        (List.replicate j true ++ scratch) out := by
  induction j generalizing v idx scratch with
  | zero => simp [run]
  | succ j ih =>
      have hs := run_add
        (scan_true v row (List.replicate j true ++ tail) idx scratch out) j
      have hh := ih (v.1,some true) (true :: idx) (true :: scratch)
      simpa [List.replicate_succ, rep_true_shift, Nat.add_comm]
        using hs.trans hh

private theorem restore_prefix (j : Nat) (v : Control)
    (row col idx scratch out : List Bool) :
    run j (cfg (some (.inl .restore)) v row col idx
      (List.replicate j true ++ scratch) out) =
      cfg (some (.inl .restore)) (if j = 0 then v else (v.1,some true))
        row (List.replicate j true ++ col) idx scratch out := by
  induction j generalizing v col with
  | zero => simp [run]
  | succ j ih =>
      have hs := run_add
        (restore_bit v row col idx (List.replicate j true ++ scratch) out true) j
      have hh := ih (v.1,some true) (true :: col)
      simpa [List.replicate_succ, rep_true_shift, Nat.add_comm]
        using hs.trans hh

private theorem parsed_column (j : Nat) (row out : List Bool) :
    run (2*j+3) (cfg (some (.inl .scan)) (readInitial,none) row
      (List.replicate j true ++ [false]) [] [] out) =
    cfg (some (.inr (.inl .scan))) (readInitial,none) row
      (List.replicate j true ++ [false]) (List.replicate j true) [] out := by
  let v₁ : Control := if j = 0 then (readInitial,none) else (readInitial,some true)
  let v₂ : Control := (readInitial,some false)
  let v₃ : Control := if j = 0 then v₂ else (readInitial,some true)
  have h₁ : run j (cfg (some (.inl .scan)) (readInitial,none) row
      (List.replicate j true ++ [false]) [] [] out) =
      cfg (some (.inl .scan)) v₁ row [false]
        (List.replicate j true) (List.replicate j true) out := by
    simpa only [v₁, List.append_nil] using
      scan_prefix j (readInitial,none) row [false] [] [] out
  have h₂ := scan_false v₁ row []
    (List.replicate j true) (List.replicate j true) out
  have h₃ := restore_bit v₂ row [] (List.replicate j true)
    (List.replicate j true) out false
  have h₄ : run j (cfg (some (.inl .restore)) v₂ row [false]
      (List.replicate j true) (List.replicate j true) out) =
      cfg (some (.inl .restore)) v₃ row
        (List.replicate j true ++ [false]) (List.replicate j true) [] out := by
    simpa only [v₃, List.append_nil] using
      restore_prefix j v₂ row [false] (List.replicate j true) [] out
  have h₅ := restore_done v₃ row
    (List.replicate j true ++ [false]) (List.replicate j true) out
  have hv : v₁.1 = readInitial := by unfold v₁; split <;> rfl
  have h₂' : run 1 (cfg (some (.inl .scan)) v₁ row [false]
      (List.replicate j true) (List.replicate j true) out) =
      cfg (some (.inl .restore)) v₂ row [] (List.replicate j true)
        (false :: List.replicate j true) out := by simpa only [hv, v₂] using h₂
  have h₃' : run 1 (cfg (some (.inl .restore)) v₂ row []
      (List.replicate j true) (false :: List.replicate j true) out) =
      cfg (some (.inl .restore)) v₂ row [false]
        (List.replicate j true) (List.replicate j true) out := by
    simpa only [v₂] using h₃
  have h₁₂ := (run_add h₁ 1).trans h₂'
  have h₁₂₃ := (run_add h₁₂ 1).trans h₃'
  have h₁₂₃₄ := (run_add h₁₂₃ j).trans h₄
  have h₁₂₃₄₅ := (run_add h₁₂₃₄ 1).trans h₅
  have htime : (((j+1)+1)+j)+1 = 2*j+3 := by omega
  rw [htime] at h₁₂₃₄₅
  exact h₁₂₃₄₅

theorem bool_pi_encode (p : Nat) (x : Fin p → Bool) :
    (piCodec boolCodec p).encode x = List.ofFn x := by
  induction p with
  | zero => simp [piCodec, emptyPiCodec, List.ofFn]
  | succ p ih =>
      simp [piCodec, transportCodec, prodCodec, boolCodec,
        List.ofFn_succ]
      simpa [Fin.tail] using ih (Fin.tail x)

private theorem reader_start_eq (row col idx : List Bool) :
    cfg (some (.inr (.inl .scan))) (readInitial,none) row col idx [] [] =
    BitMachineStackEmbedding.cfg embedRead
      (cfg (some (.inr (.inl .scan))) (readInitial,none) row col idx [] []).stk
      Sum.inr (fun v => (v,none)) (some (.inl .clear))
      (MatrixReadAt.initial idx row []) := by
  simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, MatrixReadAt.initial, MatrixReadAt.cfg,
    cfg]
  congr 1
  symm
  apply (BitMachineStackEmbedding.bank_eq_self embedRead _ _)
  intro i
  fin_cases i <;> rfl

private theorem reader_end_eq (row col idx : List Bool) (b : Bool)
    (v : MatrixReadAt.Control) :
    BitMachineStackEmbedding.cfg embedRead
      (cfg (some (.inr (.inl .scan))) (readInitial,none) row col idx [] []).stk
      Sum.inr (fun w => (w,none)) (some (.inl .clear))
      (MatrixReadAt.cfg none v idx [] row [] [b]) =
    cfg (some (.inl .clear)) (v,none) row col idx [] [b] := by
  simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, MatrixReadAt.cfg, cfg]
  congr 1
  let S : Stack → List Bool := ![idx,[],[],row,[],[],[],col,[]]
  let T : Fin 7 → List Bool := ![idx,[],[],row,[],[b],[]]
  have hlow (k : Fin 7) :
      BitMachineStackEmbedding.bank embedRead S T (embedRead k) =
        (![idx,[],[],row,[],[b],[],col,[]] : Stack → List Bool) (embedRead k) := by
    rw [BitMachineStackEmbedding.bank_at]
    fin_cases k <;> rfl
  have h7 : ¬ ∃ k : Fin 7, embedRead k = (7 : Stack) := by
    rintro ⟨k,h⟩
    have hk : k.val = 7 := by simpa [embedRead] using congrArg Fin.val h
    omega
  have h8 : ¬ ∃ k : Fin 7, embedRead k = (8 : Stack) := by
    rintro ⟨k,h⟩
    have hk : k.val = 8 := by simpa [embedRead] using congrArg Fin.val h
    omega
  change BitMachineStackEmbedding.bank embedRead S T =
    (![idx,[],[],row,[],[b],[],col,[]] : Stack → List Bool)
  funext i
  fin_cases i <;>
    first
    | exact hlow 0
    | exact hlow 1
    | exact hlow 2
    | exact hlow 3
    | exact hlow 4
    | exact hlow 5
    | exact hlow 6
    | simpa [S] using BitMachineStackEmbedding.bank_outside embedRead S T 7 h7
    | simpa [S] using BitMachineStackEmbedding.bank_outside embedRead S T 8 h8

private theorem reader_run (j : Nat) (row col : List Bool) :
    ∃ t ≤ 3*j+3*row.length+8,
      run t (cfg (some (.inr (.inl .scan))) (readInitial,none) row col
        (List.replicate j true) [] []) =
      cfg (some (.inl .clear)) (readInitial,none) row col
        (List.replicate j true) [] [row[j]?.getD false] := by
  let idx := List.replicate j true
  let base := (cfg (some (.inr (.inl .scan))) (readInitial,none)
    row col idx [] []).stk
  obtain ⟨t,ht,hraw⟩ := MatrixReadAt.readAt_run j row []
  have hhalt : (((advance MatrixReadAt.program)^[t])
      (MatrixReadAt.initial idx row [])).l = none := by
    simpa only [MatrixReadAt.run] using congrArg TM2.Cfg.l hraw
  obtain ⟨u,hu,hrun⟩ := BitMachineStackEmbedding.outputs
    embedRead base Sum.inr (fun v => (v,none)) Prod.fst
    (by intro v; rfl) (some (.inl .clear))
    MatrixReadAt.program program (by intro l; rfl)
    (MatrixReadAt.initial idx row []) t hhalt
  refine ⟨u, hu.trans ht, ?_⟩
  rw [reader_start_eq]
  have hraw' : ((advance MatrixReadAt.program)^[t])
      (MatrixReadAt.initial idx row []) =
      MatrixReadAt.cfg none readInitial idx [] row [] [row[j]?.getD false] := by
    simpa only [MatrixReadAt.run, idx, readInitial] using hraw
  rw [hraw'] at hrun
  simpa only [run, reader_end_eq, idx, base] using hrun

private theorem clear_run (j : Nat) (row col : List Bool) (b : Bool) :
    run (j+2) (cfg (some (.inl .clear)) (readInitial,none) row col
      (List.replicate j true) [] [b]) =
    final row col b (readInitial,none) := by
  let S := (cfg (some (.inl .clear)) (readInitial,none) row col
      (List.replicate j true) [] [b]).stk
  have hc := BitMachineClearBank.clear_one_run program (0 : Stack)
    (.inl .clear) (.inl .finish) (by rfl) readInitial S
  have hlen : (S 0).length = j := by simp [S, cfg]
  have hbank : Function.update S 0 [] =
      (cfg (some (.inl .finish)) (readInitial,none) row col [] [] [b]).stk := by
    funext i
    fin_cases i <;> simp [S, cfg, Function.update]
  have hc' : run (j+1) (cfg (some (.inl .clear)) (readInitial,none)
      row col (List.replicate j true) [] [b]) =
      cfg (some (.inl .finish)) (readInitial,none) row col [] [] [b] := by
    rw [hlen, hbank] at hc
    simpa only [run, S, cfg] using hc
  have hf : run 1 (cfg (some (.inl .finish)) (readInitial,none)
      row col [] [] [b]) = final row col b (readInitial,none) := by
    simp [run, cfg, final, program, advance, TM2.step, TM2.stepAux]
  have h := (run_add hc' 1).trans hf
  simpa only [show (j+1)+1 = j+2 by omega] using h

theorem encoded_row_at (p : Nat) (x : Fin p → Bool) (j : Fin p) :
    ((piCodec boolCodec p).encode x)[j.val]?.getD false = x j := by
  rw [bool_pi_encode]
  simp

/-- One fixed finite-state TM2 controller evaluates a literal valid seed
row/column pair. Both input words survive, the work bank is empty, and the
only answer is the selected coordinate. The program is independent of p. -/
theorem run_encoded_pair (p : Nat) (x : Fin p → Bool) (j : Fin p) :
    ∃ t ≤ 9*p+13,
      run t (initial ((piCodec boolCodec p).encode x)
        ((finCodec p).encode j)) =
      final ((piCodec boolCodec p).encode x)
        ((finCodec p).encode j) (LookupSeed.matrix p x j)
        (readInitial,none) := by
  let row := (piCodec boolCodec p).encode x
  let col := (finCodec p).encode j
  have hcol : col = List.replicate j.val true ++ [false] := rfl
  have hp := parsed_column j.val row []
  obtain ⟨tr,htr,hr⟩ := reader_run j.val row col
  have hc := clear_run j.val row col (row[j.val]?.getD false)
  have hp' : run (2*j.val+3) (initial row col) =
      cfg (some (.inr (.inl .scan))) (readInitial,none) row col
        (List.replicate j.val true) [] [] := by
    simpa only [initial, hcol] using hp
  have hpr := (run_add hp' tr).trans hr
  have hfull := (run_add hpr (j.val+2)).trans hc
  have hbit : row[j.val]?.getD false = LookupSeed.matrix p x j := by
    simpa only [row, LookupSeed.matrix] using encoded_row_at p x j
  refine ⟨(2*j.val+3+tr)+(j.val+2), ?_, ?_⟩
  · have hj := j.isLt
    have hrowlen : row.length = p := by simp [row, bool_pi_encode]
    have htr' : tr ≤ 3*j.val+3*p+8 := by simpa only [hrowlen] using htr
    omega
  · simpa only [row, col, hbit] using hfull

#print axioms run_encoded_pair
#print axioms program

end Paper2.SeedEntryMachine
