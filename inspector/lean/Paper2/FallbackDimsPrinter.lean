import Paper2.FallbackOutputPrint
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import Mathlib.Tactic

/-! F1 (private, lane owner:a-uniform-clock-2): the writer's `ready` bank is
PRODUCED, not supplied. From the public unary word `k` (producer cell 0) and
otherwise empty stacks, one fixed program

1. `dec`:    pops one unit of `k` (if any) onto a marker cell (1 step);
2. `power`:  the admitted unary-power controller writes `2^(k-1)` (truncated
             subtraction) into the writer's `rows` stack (reused by exact name:
             `MatrixStage4ScalarPreparationOps.unary_power_run`);
3. `copy`:   the admitted copy controller copies `rows` to `cols`
             (`MatrixStage4ScalarPreparationOps.copy_run`);
4. `adjust`: one finite-control step that restores `k` from the marker and adds
             one column exactly when `k = 1` (so `cols 1 = 2`);
5. `writer`: the admitted row-major writer `MatrixTableWriter.program P start initial`
             for an arbitrary fixed entry program `P`, started in its
             `ready (fun _ => []) (rows k) (cols k) 0 0 0 0 [] []` layout.

Every step of every phase is counted; the phase hand-offs are the halts of the
inlined sub-programs (no extra step) and the two explicit one-step phases.
Instantiated with the admitted `CodeTableFallback.falseCell` (zero table, every
`k`), `FallbackIdentityCell.eqCell` (`2^(k-1)` identity, `k ≥ 2`) and
`FallbackOutputPrint.oneCell` (`[0 1]`, `k = 1`). -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Paper2.FallbackDimsPrinter

open Turing TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

noncomputable section

/-- Producer cells `Fin 4` (0 = unary `k`, 1 = marker, 2 and 3 = scratch),
then the complete writer stack set. -/
abbrev Stack (K : Nat) := Fin 4 ⊕ MatrixTableWriter.Stack K

def kCell {K : Nat} : Stack K := .inl 0
def marker {K : Nat} : Stack K := .inl 1
def rowsW {K : Nat} : Stack K := .inr (.inr .rows)
def colsW {K : Nat} : Stack K := .inr (.inr .cols)

def powSlot {K : Nat} : MatrixUnaryPower.Stack → Stack K
  | .inl 0 => .inr (.inr .rows)
  | .inl 1 => .inl 2
  | .inl _ => .inl 3
  | .inr _ => .inl 0

theorem powSlot_injective {K : Nat} : Function.Injective (powSlot (K := K)) := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b
  · fin_cases a <;> fin_cases b <;> simp_all [powSlot]
  · cases b; fin_cases a <;> simp_all [powSlot]
  · cases a; fin_cases b <;> simp_all [powSlot]
  · cases a; cases b; rfl

def powSlots {K : Nat} : MatrixUnaryPower.Stack ↪ Stack K := ⟨powSlot, powSlot_injective⟩

def copySlot {K : Nat} : Fin 3 → Stack K
  | 0 => .inr (.inr .rows)
  | 1 => .inr (.inr .cols)
  | _ => .inl 2

theorem copySlot_injective {K : Nat} : Function.Injective (copySlot (K := K)) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [copySlot]

def copySlots {K : Nat} : Fin 3 ↪ Stack K := ⟨copySlot, copySlot_injective⟩

/-- Ambient finite control: two producer registers, the unary-power control,
and the writer control. -/
abbrev Ctl (V : Type) := (Option Bool × Option Bool) × MatrixUnaryPower.Control ×
  MatrixTableWriter.Control V

def dPow : MatrixUnaryPower.Control := ((false, false), none)

variable {K : Nat} {L V : Type}

def D0 (initial : V) : Ctl V := ((none, none), dPow, (initial, none))
def embedPow (initial : V) (p : MatrixUnaryPower.Control) : Ctl V :=
  ((none, none), p, (initial, none))
def readPow (v : Ctl V) : MatrixUnaryPower.Control := v.2.1
def embedCopy (initial : V) (o : Option Bool) : Ctl V := ((o, none), dPow, (initial, none))
def readCopy (v : Ctl V) : Option Bool := v.1.1
def embedWriter (w : MatrixTableWriter.Control V) : Ctl V := ((none, none), dPow, w)
def readWriter (v : Ctl V) : MatrixTableWriter.Control V := v.2.2

inductive Lab (L : Type) where
  | dec
  | power (l : MatrixUnaryPower.Label)
  | copy (l : BitMachineCopy.Label)
  | adjust
  | writer (l : MatrixTableWriter.Label L)

def writerStart : Lab L := .writer (.inr (.copy .rows))

/-- The fixed composite program (fixed for each fixed entry program `P`). -/
def program (P : L → TM2.Stmt (fun _ : MatrixTableWriter.CellStack K => Bool) L V)
    (start : L) (initial : V) :
    Lab L → TM2.Stmt (fun _ : Stack K => Bool) (Lab L) (Ctl V)
  | .dec => pop kCell (fun v b => ((b, none), v.2))
      (branch (fun v => v.1.1.isSome)
        (push marker (fun _ => true)
          (load (fun _ => D0 initial) (goto (fun _ => .power (.inr false)))))
        (load (fun _ => D0 initial) (goto (fun _ => .power (.inr false)))))
  | .power l => BitMachineInline.stmt Lab.power (embedPow initial) readPow
      (some (.copy .scan)) (MatrixStage4ScalarPreparationOps.unaryPowerProgram powSlots l)
  | .copy l => BitMachineInline.stmt Lab.copy (embedCopy initial) readCopy
      (some .adjust) (MatrixStage4ScalarPreparationOps.copyProgram copySlots l)
  | .adjust => pop kCell (fun v b => ((b, v.1.2), v.2))
      (pop marker (fun v b => ((v.1.1, b), v.2))
        (branch (fun v => v.1.1.isSome)
          (push kCell (fun _ => true) (push kCell (fun _ => true)
            (load (fun _ => D0 initial) (goto (fun _ => writerStart)))))
          (branch (fun v => v.1.2.isSome)
            (push colsW (fun _ => true) (push kCell (fun _ => true)
              (load (fun _ => D0 initial) (goto (fun _ => writerStart)))))
            (load (fun _ => D0 initial) (goto (fun _ => writerStart))))))
  | .writer l => BitMachineStackEmbedding.stmt Function.Embedding.inr Lab.writer
      embedWriter readWriter none (MatrixTableWriter.program P start initial l)

/-- Producer cells: `k`-cell, marker, two scratch cells. -/
def pbank (a m : Nat) : Fin 4 → List Bool :=
  ![List.replicate a true, List.replicate m true, [], []]

/-- Writer stacks with dimension words `r`, `c`, every other stack empty. -/
def wbank (r c : Nat) : MatrixTableWriter.Stack K → List Bool :=
  (MatrixTableWriter.ready (fun _ => []) r c 0 0 0 0 [] []).contents

def B (a m r c : Nat) : Stack K → List Bool := Sum.elim (pbank a m) (wbank r c)

/-- Start configuration: public unary `k`, everything else empty. -/
def startCfg (initial : V) (k : Nat) :
    TM2.Cfg (fun _ : Stack K => Bool) (Lab L) (Ctl V) :=
  ⟨some .dec, D0 initial, B k 0 0 0⟩

theorem cfg_ext {c : TM2.Cfg (fun _ : Stack K => Bool) (Lab L) (Ctl V)}
    {l : Option (Lab L)} {v : Ctl V} {S : Stack K → List Bool}
    (hl : c.l = l) (hv : c.var = v) (hs : ∀ j, c.stk j = S j) :
    c = ⟨l, v, S⟩ := by
  cases c with
  | mk l' v' S' =>
    simp only at hl hv
    subst hl hv
    have : S' = S := funext hs
    subst this
    rfl

section Stages

variable (P : L → TM2.Stmt (fun _ : MatrixTableWriter.CellStack K => Bool) L V)
  (start : L) (initial : V)

abbrev step := advance (program P start initial)

theorem dec_zero (v : Ctl V) :
    step P start initial ⟨some .dec, v, B 0 0 0 0⟩ =
      ⟨some (.power (.inr false)), D0 initial, B 0 0 0 0⟩ := by
  apply cfg_ext
  · rfl
  · rfl
  · intro j
    rcases j with j | (j | j) | j
    · fin_cases j <;> rfl
    · rfl
    · fin_cases j <;> rfl
    · cases j <;> rfl

theorem dec_succ (a : Nat) (v : Ctl V) :
    step P start initial ⟨some .dec, v, B (a + 1) 0 0 0⟩ =
      ⟨some (.power (.inr false)), D0 initial, B a 1 0 0⟩ := by
  apply cfg_ext
  · rfl
  · rfl
  · intro j
    rcases j with j | (j | j) | j
    · fin_cases j <;> rfl
    · rfl
    · fin_cases j <;> rfl
    · cases j <;> rfl

theorem power_stage (a m : Nat) :
    ∃ t ≤ 4 * 2 ^ a + 5 * a + 7,
      ((step P start initial)^[t]) ⟨some (.power (.inr false)), D0 initial, B a m 0 0⟩ =
        ⟨some (.copy .scan), D0 initial, B a m (2 ^ a) 0⟩ := by
  obtain ⟨t, ht, hr⟩ := MatrixStage4ScalarPreparationOps.unary_power_run
    (powSlots (K := K)) (B a m 0 0) a rfl rfl rfl rfl
  obtain ⟨n, hn, he⟩ := BitMachineInline.outputs Lab.power (embedPow initial) readPow
    (fun _ => rfl) (some (.copy .scan))
    (MatrixStage4ScalarPreparationOps.unaryPowerProgram powSlots)
    (program P start initial) (fun _ => rfl)
    (⟨some (.inr false), ((false, false), none), B a m 0 0⟩ :
      TM2.Cfg (fun _ : Stack K => Bool) MatrixUnaryPower.Label MatrixUnaryPower.Control)
    t (by rw [hr])
  refine ⟨n, hn.trans ht, ?_⟩
  rw [hr] at he
  refine he.trans (cfg_ext rfl rfl ?_)
  intro j
  rcases j with j | (j | j) | j
  · fin_cases j <;> rfl
  · rfl
  · fin_cases j <;> rfl
  · cases j <;> rfl

theorem copy_stage (a m r : Nat) :
    ∃ t ≤ 2 * r + 2,
      ((step P start initial)^[t]) ⟨some (.copy .scan), D0 initial, B a m r 0⟩ =
        ⟨some .adjust, D0 initial, B a m r r⟩ := by
  have hr := MatrixStage4ScalarPreparationOps.copy_run (copySlots (K := K))
    (B a m r 0) rfl
  have h0 : B (K := K) a m r 0 (copySlots 0) = List.replicate r true := rfl
  have h1 : B (K := K) a m r 0 (copySlots 1) = [] := rfl
  rw [h0, h1, List.append_nil, List.length_replicate] at hr
  obtain ⟨n, hn, he⟩ := BitMachineInline.outputs Lab.copy (embedCopy initial) readCopy
    (fun _ => rfl) (some .adjust)
    (MatrixStage4ScalarPreparationOps.copyProgram copySlots)
    (program P start initial) (fun _ => rfl)
    (⟨some .scan, none, B a m r 0⟩ :
      TM2.Cfg (fun _ : Stack K => Bool) BitMachineCopy.Label (Option Bool))
    (2 * r + 2) (by rw [hr])
  refine ⟨n, hn, ?_⟩
  rw [hr] at he
  refine he.trans (cfg_ext rfl rfl ?_)
  intro j
  rcases j with j | (j | j) | j
  · fin_cases j <;> rfl
  · rfl
  · fin_cases j <;> rfl
  · cases j <;> rfl

theorem adjust_big (a r c : Nat) :
    step P start initial ⟨some .adjust, D0 initial, B (a + 1) 1 r c⟩ =
      ⟨some writerStart, D0 initial, B (a + 2) 0 r c⟩ := by
  apply cfg_ext
  · rfl
  · rfl
  · intro j
    rcases j with j | (j | j) | j
    · fin_cases j <;> rfl
    · rfl
    · fin_cases j <;> rfl
    · cases j <;> rfl

theorem adjust_one (r c : Nat) :
    step P start initial ⟨some .adjust, D0 initial, B 0 1 r c⟩ =
      ⟨some writerStart, D0 initial, B 1 0 r (c + 1)⟩ := by
  apply cfg_ext
  · rfl
  · rfl
  · intro j
    rcases j with j | (j | j) | j
    · fin_cases j <;> rfl
    · rfl
    · fin_cases j <;> rfl
    · cases j <;> rfl

theorem adjust_zero (r c : Nat) :
    step P start initial ⟨some .adjust, D0 initial, B 0 0 r c⟩ =
      ⟨some writerStart, D0 initial, B 0 0 r c⟩ := by
  apply cfg_ext
  · rfl
  · rfl
  · intro j
    rcases j with j | (j | j) | j
    · fin_cases j <;> rfl
    · rfl
    · fin_cases j <;> rfl
    · cases j <;> rfl

theorem bank_inr (p : Fin 4 → List Bool) (T U : MatrixTableWriter.Stack K → List Bool) :
    BitMachineStackEmbedding.bank (Function.Embedding.inr : MatrixTableWriter.Stack K ↪ Stack K)
      (Sum.elim p T) U = Sum.elim p U := by
  funext j
  cases j with
  | inl k =>
      simpa only [Sum.elim_inl] using
        (BitMachineStackEmbedding.bank_outside
          (Function.Embedding.inr : MatrixTableWriter.Stack K ↪ Stack K)
          (Sum.elim p T) U (Sum.inl k : Stack K)
          (by intro h; obtain ⟨x, hx⟩ := h
              change Sum.inr x = Sum.inl k at hx
              cases hx))
  | inr k =>
      simpa only [Sum.elim_inr] using
        (BitMachineStackEmbedding.bank_at
          (Function.Embedding.inr : MatrixTableWriter.Stack K ↪ Stack K) (Sum.elim p T) U k)

/-- The admitted writer, inlined on the writer stacks, from the produced bank. -/
theorem writer_stage (p : Fin 4 → List Bool) (r c T : Nat) (entry : Nat → Nat → Bool)
    (f : Fin r → Fin c → Bool) (hf : ∀ x y, entry x.val y.val = f x y)
    (hcell : MatrixTableWriter.EntryRuns P start initial (fun _ => []) r c T entry) :
    ∃ t ≤ MatrixTableWriter.writerBound r c T, ∃ v,
      ((step P start initial)^[t]) ⟨some writerStart, D0 initial, Sum.elim p (wbank r c)⟩ =
        ⟨none, embedWriter v, Sum.elim p
          (MatrixTableWriter.ready (fun _ => []) r c 0 0 0 0 []
            (MatrixMaterialization.rowMajor f)).contents⟩ := by
  obtain ⟨bound, hbound, v, hwrite⟩ := MatrixTableWriter.write_rowMajor P start initial
    (fun _ => []) r c T entry f hf hcell []
  let d : MatrixTableWriter.Data K := MatrixTableWriter.ready (fun _ => []) r c 0 0 0 0 [] []
  let a : MatrixTableWriter.Config K L V :=
    MatrixTableWriter.cfg (some (.inr (.copy .rows))) (initial, none) d
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs
    (Function.Embedding.inr : MatrixTableWriter.Stack K ↪ Stack K)
    (Sum.elim p d.contents) Lab.writer embedWriter readWriter (fun _ => rfl) none
    (MatrixTableWriter.program P start initial) (program P start initial) (fun _ => rfl)
    a bound (by
      have h2 := congrArg TM2.Cfg.l hwrite
      simpa [MatrixTableWriter.run, a, d] using h2)
  refine ⟨t, ht.trans hbound, v, ?_⟩
  change ((advance (program P start initial))^[t])
      (BitMachineStackEmbedding.cfg Function.Embedding.inr (Sum.elim p d.contents)
        Lab.writer embedWriter none a) =
    BitMachineStackEmbedding.cfg Function.Embedding.inr (Sum.elim p d.contents)
      Lab.writer embedWriter none (MatrixTableWriter.run P start initial bound a) at he
  change MatrixTableWriter.run P start initial bound a =
    MatrixTableWriter.cfg none v (MatrixTableWriter.ready (fun _ => []) r c 0 0 0 0 []
      (MatrixMaterialization.rowMajor f ++ [])) at hwrite
  rw [hwrite, List.append_nil] at he
  simpa only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, bank_inr, MatrixTableWriter.cfg, a, d, writerStart, wbank] using he

end Stages

theorem seq {α : Type*} {f : α → α} {c0 c1 c2 : α} {b1 b2 : Nat}
    (h1 : ∃ t ≤ b1, f^[t] c0 = c1) (h2 : ∃ t ≤ b2, f^[t] c1 = c2) :
    ∃ t ≤ b1 + b2, f^[t] c0 = c2 := by
  obtain ⟨t1, ht1, e1⟩ := h1
  obtain ⟨t2, ht2, e2⟩ := h2
  exact ⟨t2 + t1, by omega, by rw [Function.iterate_add_apply, e1, e2]⟩

/-- Exact charged clock of the dimension producer (phases 1-4). -/
def dimsClock (k : Nat) : Nat :=
  1 + ((4 * 2 ^ (k - 1) + 5 * (k - 1) + 7) + (2 * 2 ^ (k - 1) + 2)) + 1

/-- F1 producer: from public unary `k` alone, the physical run reaches the
writer's start label with EXACTLY the writer layout
`ready (fun _ => []) (rows k) (cols k) 0 0 0 0 [] []` and the `k` cell restored. -/
theorem dims_run (P : L → TM2.Stmt (fun _ : MatrixTableWriter.CellStack K => Bool) L V)
    (start : L) (initial : V) (k : Nat) :
    ∃ t ≤ dimsClock k,
      ((advance (program P start initial))^[t]) (startCfg initial k) =
        ⟨some writerStart, D0 initial,
          B k 0 (FiniteFallbackOutput.rows k) (FiniteFallbackOutput.cols k)⟩ := by
  have one : ∀ {c0 c1 : TM2.Cfg (fun _ : Stack K => Bool) (Lab L) (Ctl V)},
      advance (program P start initial) c0 = c1 →
      ∃ t ≤ 1, ((advance (program P start initial))^[t]) c0 = c1 :=
    fun h => ⟨1, le_rfl, by rw [Function.iterate_one, h]⟩
  rcases k with _ | _ | i
  · exact seq (seq (one (dec_zero P start initial _))
      (seq (power_stage P start initial 0 0) (copy_stage P start initial 0 0 1)))
      (one (adjust_zero P start initial 1 1))
  · exact seq (seq (one (dec_succ P start initial 0 _))
      (seq (power_stage P start initial 0 1) (copy_stage P start initial 0 1 1)))
      (one (adjust_one P start initial 1 1))
  · have h := seq (seq (one (dec_succ P start initial (i + 1) (D0 initial)))
      (seq (power_stage P start initial (i + 1) 1)
        (copy_stage P start initial (i + 1) 1 (2 ^ (i + 1)))))
      (one (adjust_big P start initial i (2 ^ (i + 1)) (2 ^ (i + 1))))
    simpa [dimsClock, FiniteFallbackOutput.rows, FiniteFallbackOutput.cols] using h

/-- F1 composite: producer then printer, one fixed program, every step charged. -/
theorem print_from_k (P : L → TM2.Stmt (fun _ : MatrixTableWriter.CellStack K => Bool) L V)
    (start : L) (initial : V) (k T : Nat) (entry : Nat → Nat → Bool)
    (f : Fin (FiniteFallbackOutput.rows k) → Fin (FiniteFallbackOutput.cols k) → Bool)
    (hf : ∀ x y, entry x.val y.val = f x y)
    (hcell : MatrixTableWriter.EntryRuns P start initial (fun _ => [])
      (FiniteFallbackOutput.rows k) (FiniteFallbackOutput.cols k) T entry) :
    ∃ t ≤ dimsClock k + MatrixTableWriter.writerBound (FiniteFallbackOutput.rows k)
        (FiniteFallbackOutput.cols k) T, ∃ v,
      ((advance (program P start initial))^[t]) (startCfg initial k) =
        ⟨none, embedWriter v, Sum.elim (pbank k 0)
          (MatrixTableWriter.ready (fun _ => []) (FiniteFallbackOutput.rows k)
            (FiniteFallbackOutput.cols k) 0 0 0 0 []
            (MatrixMaterialization.rowMajor f)).contents⟩ := by
  obtain ⟨t1, ht1, e1⟩ := dims_run P start initial k
  obtain ⟨t2, ht2, v, e2⟩ := writer_stage P start initial (pbank k 0)
    (FiniteFallbackOutput.rows k) (FiniteFallbackOutput.cols k) T entry f hf hcell
  refine ⟨t2 + t1, by omega, v, ?_⟩
  rw [Function.iterate_add_apply, e1]
  exact e2

/-! Instantiations with the three fixed entry programs. -/

abbrev zeroProgram := program (K := 0) CodeTableFallback.falseCell () ()
abbrev identityProgram := program (K := 2) FallbackIdentityCell.eqCell
  FallbackIdentityCell.Label.move ((none, none, false) : FallbackIdentityCell.Control)
abbrev oneRowProgram := program (K := 0) FallbackOutputPrint.oneCell ()
  ((none, none) : FallbackOutputPrint.Control)

theorem bank0_eq : CodeTableFallback.emptyBank = (fun _ => [] : Fin 0 → List Bool) := by
  funext i; exact i.elim0

theorem bank2_eq : FallbackIdentityCell.emptyBank = (fun _ => [] : Fin 2 → List Bool) := by
  funext i; fin_cases i <;> rfl

/-- Zero table (three-colourable graph; also the unused `k = 0` hard case). -/
theorem zero_from_k (k : Nat) :
    ∃ t ≤ dimsClock k + MatrixTableWriter.writerBound (FiniteFallbackOutput.rows k)
        (FiniteFallbackOutput.cols k) 1, ∃ v,
      ((advance zeroProgram)^[t]) (startCfg () k) =
        ⟨none, embedWriter v, Sum.elim (pbank k 0)
          (MatrixTableWriter.ready (fun _ => []) (FiniteFallbackOutput.rows k)
            (FiniteFallbackOutput.cols k) 0 0 0 0 []
            (MatrixMaterialization.rowMajor
              (fun (_ : Fin (FiniteFallbackOutput.rows k))
                (_ : Fin (FiniteFallbackOutput.cols k)) => false))).contents⟩ := by
  have hcell := CodeTableFallback.falseCell_entryRuns
    (FiniteFallbackOutput.rows k) (FiniteFallbackOutput.cols k)
  rw [bank0_eq] at hcell
  exact print_from_k CodeTableFallback.falseCell () () k 1 (fun _ _ => false) _
    (fun _ _ => rfl) hcell

/-- `2^(k-1)` identity, `k = j + 2` (v12 D:108-110). -/
theorem identity_from_k (j : Nat) :
    ∃ t ≤ dimsClock (j + 2) + MatrixTableWriter.writerBound (FiniteFallbackOutput.rows (j + 2))
        (FiniteFallbackOutput.cols (j + 2)) (3 * 2 ^ (j + 1) + 3), ∃ v,
      ((advance identityProgram)^[t]) (startCfg ((none, none, false) : FallbackIdentityCell.Control)
          (j + 2)) =
        ⟨none, embedWriter v, Sum.elim (pbank (j + 2) 0)
          (MatrixTableWriter.ready (fun _ => []) (FiniteFallbackOutput.rows (j + 2))
            (FiniteFallbackOutput.cols (j + 2)) 0 0 0 0 []
            (MatrixMaterialization.rowMajor
              (FiniteFallbackOutput.hardMatrix (j + 2)))).contents⟩ := by
  have hcell := FallbackIdentityCell.eqCell_entryRuns (2 ^ (j + 1)) (2 ^ (j + 1))
  rw [bank2_eq] at hcell
  exact print_from_k FallbackIdentityCell.eqCell FallbackIdentityCell.Label.move
    ((none, none, false) : FallbackIdentityCell.Control) (j + 2) (3 * 2 ^ (j + 1) + 3)
    (fun x y => decide (x = y)) (FiniteFallbackOutput.hardMatrix (j + 2))
    (by intro x y; exact decide_eq_decide.mpr Fin.val_inj) hcell

/-- `[0 1]`, `k = 1` (v12 D:108-110). -/
theorem oneRow_from_k :
    ∃ t ≤ dimsClock 1 + MatrixTableWriter.writerBound (FiniteFallbackOutput.rows 1)
        (FiniteFallbackOutput.cols 1) 1, ∃ v,
      ((advance oneRowProgram)^[t]) (startCfg ((none, none) : FallbackOutputPrint.Control) 1) =
        ⟨none, embedWriter v, Sum.elim (pbank 1 0)
          (MatrixTableWriter.ready (fun _ => []) (FiniteFallbackOutput.rows 1)
            (FiniteFallbackOutput.cols 1) 0 0 0 0 []
            (MatrixMaterialization.rowMajor
              (FiniteFallbackOutput.hardMatrix 1))).contents⟩ := by
  have hcell := FallbackOutputPrint.oneCell_entryRuns 1 2
  rw [bank0_eq] at hcell
  exact print_from_k FallbackOutputPrint.oneCell () ((none, none) : FallbackOutputPrint.Control)
    1 1 (fun _ y => decide (y = 1)) (FiniteFallbackOutput.hardMatrix 1)
    (by intro x y; exact decide_eq_decide.mpr ⟨fun h => Fin.ext h, fun h => h ▸ rfl⟩) hcell

theorem rows_le (k : Nat) : FiniteFallbackOutput.rows k ≤ 2 ^ k := by
  rcases k with _ | _ | k
  · decide
  · decide
  · show 2 ^ (k + 1) ≤ 2 ^ (k + 2)
    exact pow_le_pow_right₀ (by decide) (by omega)

theorem cols_le (k : Nat) : FiniteFallbackOutput.cols k ≤ 2 ^ k := by
  rcases k with _ | _ | k
  · decide
  · decide
  · show 2 ^ (k + 1) ≤ 2 ^ (k + 2)
    exact pow_le_pow_right₀ (by decide) (by omega)

/-- One public `2^{O(k)}` clock for every printer composite (entry clock
`T ≤ 3*2^k+3` covers `T = 1` and `T = 3*2^(k-1)+3`). -/
theorem print_clock_le (k T : Nat) (hT : T ≤ 3 * 2 ^ k + 3) :
    dimsClock k + MatrixTableWriter.writerBound (FiniteFallbackOutput.rows k)
      (FiniteFallbackOutput.cols k) T ≤ 2 ^ (3 * k + 15) := by
  have hw := MatrixTableWriter.writerBound_polynomial (FiniteFallbackOutput.rows k)
    (FiniteFallbackOutput.cols k) T
  have hr := rows_le k
  have hc := cols_le k
  have hN : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hk : k < 2 ^ k := Nat.lt_two_pow_self
  have hp : 2 ^ (k - 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
  have hsum : FiniteFallbackOutput.rows k + FiniteFallbackOutput.cols k + T + 1 ≤ 9 * 2 ^ k := by
    omega
  have hcube : (FiniteFallbackOutput.rows k + FiniteFallbackOutput.cols k + T + 1) ^ 3 ≤
      (9 * 2 ^ k) ^ 3 := Nat.pow_le_pow_left hsum 3
  have e : 2 ^ (3 * k + 15) = 32768 * (2 ^ k) ^ 3 := by
    rw [← pow_mul, show 3 * k + 15 = k * 3 + 15 by ring, pow_add]; norm_num; ring
  rw [e]
  set N := 2 ^ k with hNdef
  have hd : dimsClock k ≤ 6 * N + 5 * k + 11 := by
    unfold dimsClock; omega
  have hN3 : N ≤ N ^ 3 := by
    calc N = N ^ 1 := (pow_one N).symm
      _ ≤ N ^ 3 := Nat.pow_le_pow_right hN (by decide)
  nlinarith [hcube, hw, hd, hN3]

#print axioms powSlot_injective
#print axioms copySlot_injective
#print axioms dec_zero
#print axioms dec_succ
#print axioms power_stage
#print axioms copy_stage
#print axioms adjust_big
#print axioms adjust_one
#print axioms adjust_zero
#print axioms writer_stage
#print axioms dims_run
#print axioms print_from_k
#print axioms zero_from_k
#print axioms identity_from_k
#print axioms oneRow_from_k
#print axioms print_clock_le

end

end Paper2.FallbackDimsPrinter
