import EthInapproximability.CurrentPaper.MatrixWeightedDiagonal
import EthInapproximability.CurrentPaper.BitMachineSubroutine
import EthInapproximability.CurrentPaper.BitMachineComposition

/-!
# Fixed finite-stack unary variable power for protected-copy multiplicity

Frozen v8 Appendix A uses `Sdup = |Rows(M₂)|^s`.  The exponent `s` is not a
constant, so repeated host arithmetic is not a machine proof.  This program
uses a literal unary fuel stack.  Each round invokes the existing preserving
six-stack multiply-add machine with zero addend, clears the old accumulator,
and transfers the new unary product to it.  No natural-number register is
part of finite control.
-/

namespace EthInapproximability.CurrentPaper.MatrixWeightedPower

set_option maxRecDepth 4000

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineSubroutine BitMachineComposition

inductive Admin where
  | test | clear | move
  deriving DecidableEq, Fintype

abbrev Stack := Fin 6 ⊕ Fin 1
abbrev Label := MatrixAddressMachine.Label ⊕ Admin
abbrev Control := Bool × Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some .clear) (MatrixAddressMachine.program l)
  | .inr .test => pop (.inr 0) (fun v b => (v.1, b.isSome))
      (branch (fun v => v.2)
        (load (fun _ => (false, false)) (goto (fun _ => .inl .outer)))
        (load (fun _ => (false, false)) halt))
  | .inr .clear => pop (.inl 0) (fun v b => (v.1, b.isSome))
      (branch (fun v => v.2) (goto (fun _ => .inr .clear))
        (load (fun _ => (false, false)) (goto (fun _ => .inr .move))))
  | .inr .move => pop (.inl 5) (fun v b => (v.1, b.isSome))
      (branch (fun v => v.2)
        (push (.inl 0) (fun _ => true) (goto (fun _ => .inr .move)))
        (load (fun _ => (false, false)) (goto (fun _ => .inr .test))))

def bank (acc base out : List Bool) : Fin 6 → List Bool :=
  ![acc,base,[],[],[],out]

def cfg (l : Option Label) (v : Control) (acc base out fuel : List Bool) : Config :=
  ⟨l,v,Sum.elim (bank acc base out) (fun _ => fuel)⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

theorem run_succ {c d : Config} (h : advance program c = d) (t : ℕ) :
    run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, h]

theorem test_cons (b : Bool) (fuel acc base : List Bool) :
    advance program (cfg (some (.inr .test)) (false,false) acc base [] (b :: fuel)) =
      cfg (some (.inl .outer)) (false,false) acc base [] fuel := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg,
    Sum.elim_inr, List.head?_cons, List.tail_cons, Option.isSome_some, cond_true,
    Option.getD_some]
  congr 1
  funext k
  rcases k with k | k <;> fin_cases k <;> rfl

theorem test_nil (acc base : List Bool) :
    advance program (cfg (some (.inr .test)) (false,false) acc base [] []) =
      cfg none (false,false) acc base [] [] := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg,
    Sum.elim_inr, List.head?_nil, List.tail_nil, Option.isSome_none,
    cond_false, Option.getD_some]
  congr 1
  funext k
  rcases k with k | k <;> fin_cases k <;> rfl

/-- The actual six-stack multiplication is executed inside this fixed
seven-stack controller, with the fuel bank untouched. -/
theorem multiply_run (acc base : ℕ) (fuel : List Bool) :
    ∃ t ≤ MatrixAddressMachine.exactTime acc base 0,
      run t (cfg (some (.inl .outer)) (false,false)
        (List.replicate acc true) (List.replicate base true) [] fuel) =
      cfg (some (.inr .clear)) (false,false)
        (List.replicate acc true) (List.replicate base true)
        (List.replicate (acc * base) true) fuel := by
  have hlocal := MatrixAddressMachine.address_run acc base 0 false []
  have hhalt :
      ((advance MatrixAddressMachine.program)^[MatrixAddressMachine.exactTime acc base 0]
        (MatrixAddressMachine.cfg (some .outer) false
          (List.replicate acc true) (List.replicate base true)
          (List.replicate 0 true) [] [] [])).l = none := by
    rw [← MatrixAddressMachine.run, hlocal]
    rfl
  obtain ⟨t, ht, he⟩ := BitMachineSubroutine.lift_outputs
    MatrixAddressMachine.program program (some .clear)
      (fun _ => rfl) false (fun _ : Fin 1 => fuel)
      (MatrixAddressMachine.cfg (some .outer) false
        (List.replicate acc true) (List.replicate base true)
        (List.replicate 0 true) [] [] [])
      (MatrixAddressMachine.exactTime acc base 0) hhalt
  refine ⟨t, ht, ?_⟩
  rw [← MatrixAddressMachine.run, hlocal] at he
  simpa [run, cfg, bank, liftCfg, MatrixAddressMachine.cfg] using he

theorem clear_cons (b flag : Bool) (acc base out fuel : List Bool) :
    advance program (cfg (some (.inr .clear)) (false,flag)
      (b :: acc) base out fuel) =
      cfg (some (.inr .clear)) (false,true) acc base out fuel := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg,
    Sum.elim_inl]
  simp only [bank,
    show (![b :: acc, base, [], [], [], out] (0 : Fin 6)) = b :: acc from rfl,
    List.head?_cons, List.tail_cons, Option.isSome_some, cond_true, Option.getD_some]
  congr 1
  funext k
  rcases k with k | k <;> fin_cases k <;> rfl

theorem clear_nil (flag : Bool) (base out fuel : List Bool) :
    advance program (cfg (some (.inr .clear)) (false,flag) [] base out fuel) =
      cfg (some (.inr .move)) (false,false) [] base out fuel := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg,
    Sum.elim_inl]
  simp only [bank,
    show (![[], base, [], [], [], out] (0 : Fin 6)) = ([] : List Bool) from rfl,
    List.head?_nil, List.tail_nil, Option.isSome_none, cond_false, Option.getD_some]
  congr 1
  funext k
  rcases k with k | k <;> fin_cases k <;> rfl

theorem clear_run (n : ℕ) (flag : Bool) (base out fuel : List Bool) :
    run (n + 1) (cfg (some (.inr .clear)) (false,flag)
      (List.replicate n true) base out fuel) =
      cfg (some (.inr .move)) (false,false) [] base out fuel := by
  induction n generalizing flag with
  | zero => exact run_succ (clear_nil flag base out fuel) 0
  | succ n ih =>
      rw [List.replicate_succ, run_succ (clear_cons true flag
        (List.replicate n true) base out fuel) (n + 1)]
      exact ih true

theorem move_cons (b flag : Bool) (acc base out fuel : List Bool) :
    advance program (cfg (some (.inr .move)) (false,flag)
      acc base (b :: out) fuel) =
      cfg (some (.inr .move)) (false,true) (true :: acc) base out fuel := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg,
    Sum.elim_inl]
  simp only [bank,
    show (![acc, base, [], [], [], b :: out] (5 : Fin 6)) = b :: out from rfl,
    List.head?_cons, List.tail_cons, Option.isSome_some, cond_true, Option.getD_some]
  congr 1
  funext k
  rcases k with k | k <;> fin_cases k <;> rfl

theorem move_nil (flag : Bool) (acc base fuel : List Bool) :
    advance program (cfg (some (.inr .move)) (false,flag) acc base [] fuel) =
      cfg (some (.inr .test)) (false,false) acc base [] fuel := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg,
    Sum.elim_inl]
  simp only [bank,
    show (![acc, base, [], [], [], []] (5 : Fin 6)) = ([] : List Bool) from rfl,
    List.head?_nil, List.tail_nil, Option.isSome_none, cond_false, Option.getD_some]
  congr 1
  funext k
  rcases k with k | k <;> fin_cases k <;> rfl

theorem move_run (n k : ℕ) (flag : Bool) (base fuel : List Bool) :
    run (n + 1) (cfg (some (.inr .move)) (false,flag)
      (List.replicate k true) base (List.replicate n true) fuel) =
      cfg (some (.inr .test)) (false,false)
        (List.replicate (n + k) true) base [] fuel := by
  induction n generalizing k flag with
  | zero => simpa using run_succ (move_nil flag (List.replicate k true) base fuel) 0
  | succ n ih =>
      rw [List.replicate_succ, run_succ (move_cons true flag
        (List.replicate k true) base (List.replicate n true) fuel) (n + 1)]
      simpa [List.replicate_succ, Nat.add_assoc, Nat.add_comm 1 k] using ih (k + 1) true

def roundBound (acc base : ℕ) : ℕ :=
  1 + MatrixAddressMachine.exactTime acc base 0 + (acc + 1) + (acc * base + 1)

theorem round_run (acc base : ℕ) (fuel : List Bool) :
    ∃ t ≤ roundBound acc base,
      run t (cfg (some (.inr .test)) (false,false)
        (List.replicate acc true) (List.replicate base true) [] (true :: fuel)) =
      cfg (some (.inr .test)) (false,false)
        (List.replicate (acc * base) true) (List.replicate base true) [] fuel := by
  obtain ⟨tm, htm, hm⟩ := multiply_run acc base fuel
  refine ⟨1 + tm + (acc + 1) + (acc * base + 1), ?_, ?_⟩
  · dsimp [roundBound]
    omega
  · have ht := test_cons true fuel (List.replicate acc true)
      (List.replicate base true)
    calc
      run (1 + tm + (acc + 1) + (acc * base + 1))
        (cfg (some (.inr .test)) (false,false)
          (List.replicate acc true) (List.replicate base true) [] (true :: fuel)) =
        run (tm + (acc + 1) + (acc * base + 1))
          (cfg (some (.inl .outer)) (false,false)
            (List.replicate acc true) (List.replicate base true) [] fuel) := by
              rw [show 1 + tm + (acc + 1) + (acc * base + 1) =
                (tm + (acc + 1) + (acc * base + 1)) + 1 by omega]
              exact run_succ ht _
      _ = run ((acc + 1) + (acc * base + 1))
          (cfg (some (.inr .clear)) (false,false)
            (List.replicate acc true) (List.replicate base true)
            (List.replicate (acc * base) true) fuel) := by
              rw [show tm + (acc + 1) + (acc * base + 1) =
                tm + ((acc + 1) + (acc * base + 1)) by omega]
              exact run_add hm _
      _ = run (acc * base + 1)
          (cfg (some (.inr .move)) (false,false)
            [] (List.replicate base true)
            (List.replicate (acc * base) true) fuel) := by
              exact run_add (clear_run acc false
                (List.replicate base true) (List.replicate (acc * base) true) fuel) _
      _ = _ := by
        simpa using move_run (acc * base) 0 false (List.replicate base true) fuel

def iterateBound (acc base : ℕ) : ℕ → ℕ
  | 0 => 0
  | s + 1 => roundBound acc base + iterateBound (acc * base) base s

theorem iterate_run (acc base s : ℕ) :
    ∃ t ≤ iterateBound acc base s,
      run t (cfg (some (.inr .test)) (false,false)
        (List.replicate acc true) (List.replicate base true) []
        (List.replicate s true)) =
      cfg (some (.inr .test)) (false,false)
        (List.replicate (acc * base ^ s) true) (List.replicate base true) [] [] := by
  induction s generalizing acc with
  | zero =>
      refine ⟨0, by simp [iterateBound], ?_⟩
      simp [run, cfg]
  | succ s ih =>
      obtain ⟨tr, htr, hr⟩ := round_run acc base (List.replicate s true)
      obtain ⟨ti, hti, hi⟩ := ih (acc * base)
      refine ⟨tr + ti, ?_, ?_⟩
      · simp only [iterateBound]
        omega
      · rw [List.replicate_succ, run_add hr]
        simpa [pow_succ, mul_assoc, mul_comm base (base ^ s)] using hi

def powerBound (base s : ℕ) : ℕ := iterateBound 1 base s + 1

theorem roundBound_eq (acc base : ℕ) :
    roundBound acc base = 3 * acc * base + 5 * acc + 7 := by
  simp only [roundBound, MatrixAddressMachine.exactTime]
  ring

theorem iterateBound_le_cap (acc base s cap : ℕ)
    (hcap : ∀ i ≤ s, acc * base ^ i ≤ cap) :
    iterateBound acc base s ≤ s * (3 * cap * base + 5 * cap + 7) := by
  induction s generalizing acc with
  | zero => simp [iterateBound]
  | succ s ih =>
      have hacc : acc ≤ cap := by
        simpa using hcap 0 (by omega)
      have hnext : ∀ i ≤ s, (acc * base) * base ^ i ≤ cap := by
        intro i hi
        simpa [pow_succ, mul_assoc, mul_comm base (base ^ i)] using
          hcap (i + 1) (by omega)
      have hrec := ih (acc * base) hnext
      simp only [iterateBound, roundBound_eq]
      have hr : 3 * acc * base + 5 * acc + 7 ≤
          3 * cap * base + 5 * cap + 7 := by
        nlinarith
      nlinarith

theorem powerBound_polynomial (base s : ℕ) :
    powerBound base s ≤
      (s + 1) * (3 * (base ^ s + 1) * base +
        5 * (base ^ s + 1) + 7) := by
  have hcap : ∀ i ≤ s, 1 * base ^ i ≤ base ^ s + 1 := by
    intro i hi
    by_cases hb : base = 0
    · subst base
      cases i with
      | zero => simp
      | succ i => simp
    · have hp := Nat.pow_le_pow_right (by omega : 0 < base) hi
      omega
  have h := iterateBound_le_cap 1 base s (base ^ s + 1) hcap
  dsimp [powerBound]
  let K := 3 * (base ^ s + 1) * base + 5 * (base ^ s + 1) + 7
  have hk : 1 ≤ K := by dsimp [K]; omega
  have h' : iterateBound 1 base s ≤ s * K := h
  calc
    iterateBound 1 base s + 1 ≤ s * K + 1 := Nat.add_le_add_right h' 1
    _ ≤ s * K + K := Nat.add_le_add_left hk _
    _ = (s + 1) * (3 * (base ^ s + 1) * base +
          5 * (base ^ s + 1) + 7) := by dsimp [K]; ring

/-- Literal seven-stack program computes a variable unary power; the base
bank and all scratch banks survive in the displayed normal form. -/
theorem power_run (base s : ℕ) :
    ∃ t ≤ powerBound base s,
      run t (cfg (some (.inr .test)) (false,false)
        (List.replicate 1 true) (List.replicate base true) []
        (List.replicate s true)) =
      cfg none (false,false) (List.replicate (base ^ s) true)
        (List.replicate base true) [] [] := by
  obtain ⟨ti, hti, hi⟩ := iterate_run 1 base s
  refine ⟨ti + 1, ?_, ?_⟩
  · dsimp [powerBound]
    omega
  · rw [run_add hi]
    simpa using run_succ
      (test_nil (List.replicate (1 * base ^ s) true)
        (List.replicate base true)) 0

end EthInapproximability.CurrentPaper.MatrixWeightedPower
