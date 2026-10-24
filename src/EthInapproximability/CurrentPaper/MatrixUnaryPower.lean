import EthInapproximability.CurrentPaper.MatrixBinaryAddress
import EthInapproximability.CurrentPaper.BitMachineSubroutine

/-!
# A physical unary power-of-two constructor

Source: frozen v8 Appendix B, `thm:paper-materialization`, scalar parameter
initialization. Scan and restore the input exponent while writing its binary
power-of-two word, then invoke the actual binary-to-unary decoder. Runtime
is output-sensitive; it is not polynomial in the exponent alone.
-/

namespace EthInapproximability.CurrentPaper.MatrixUnaryPower

open Turing TM2.Stmt BitMachineEncoding BitMachineComposition BitMachineSubroutine

abbrev Stack := Fin 3 ⊕ Unit
abbrev Label := MatrixBinaryAddress.Label ⊕ Bool
abbrev Control := (Bool × Bool) × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def setPop (v : Control) (b : Option Bool) : Control := (v.1, b)
def go (b : Bool) : TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  goto (fun _ => .inr b)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt none (MatrixBinaryAddress.program l)
  | .inr false => pop (.inr ()) setPop
      (branch (fun v => v.2.isSome)
        (push (.inl 1) (fun v => v.2.getD false)
          (push (.inl 0) (fun _ => false) (go false))) (go true))
  | .inr true => pop (.inl 1) setPop
      (branch (fun v => v.2.isSome)
        (push (.inr ()) (fun v => v.2.getD false) (go true))
        (push (.inl 0) (fun _ => true)
          (load (fun _ => ((false, false), none))
            (goto (fun _ => .inl .readBit)))))

def contents (word work scratch exponent : List Bool) : Stack → List Bool :=
  Sum.elim (MatrixBinaryAddress.stackContents word work scratch) (fun _ => exponent)

def cfg (l : Option Label) (v : Control) (word work scratch exponent : List Bool) : Config :=
  ⟨l, v, contents word work scratch exponent⟩

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

theorem run_succ (t : ℕ) (c : Config) :
    run (t + 1) c = run t (advance program c) := Function.iterate_succ_apply _ _ _

theorem run_add (t u : ℕ) (c : Config) : run (t+u) c = run u (run t c) := by
  simpa only [run, Nat.add_comm] using Function.iterate_add_apply (advance program) u t c

theorem scan_cons (v : Control) (b : Bool) (w q p s : List Bool) :
    advance program (cfg (some (.inr false)) v q p s (b :: w)) =
      cfg (some (.inr false)) (setPop v (some b)) (false :: q) (b :: p) s w := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg, contents,
    Sum.elim_inr, go, setPop, List.head?_cons, List.tail_cons,
    Option.isSome_some, cond_true, Option.getD_some]
  congr 1
  funext k
  rcases k with k | k
  · fin_cases k <;> rfl
  · cases k; rfl

theorem scan_nil (v : Control) (q p s : List Bool) :
    advance program (cfg (some (.inr false)) v q p s []) =
      cfg (some (.inr true)) (setPop v none) q p s [] := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg, contents,
    Sum.elim_inr, go, setPop, List.head?_nil, List.tail_nil,
    Option.isSome_none, cond_false, Option.getD_some]
  congr 1
  funext k
  rcases k with k | k
  · rfl
  · cases k; rfl

theorem restore_cons (v : Control) (b : Bool) (p q s w : List Bool) :
    advance program (cfg (some (.inr true)) v q (b :: p) s w) =
      cfg (some (.inr true)) (setPop v (some b)) q p s (b :: w) := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg, contents,
    Sum.elim_inl, MatrixBinaryAddress.stackContents, go, setPop,
    List.head?_cons, List.tail_cons, Option.isSome_some, cond_true,
    Option.getD_some, show (1 : Fin 3) ≠ 0 from by decide, ↓reduceIte]
  congr 1
  funext k
  rcases k with k | k
  · fin_cases k <;> rfl
  · cases k; rfl

theorem restore_nil (v : Control) (q s w : List Bool) :
    advance program (cfg (some (.inr true)) v q [] s w) =
      cfg (some (.inl .readBit)) ((false, false), none) (true :: q) [] s w := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg, contents,
    Sum.elim_inl, MatrixBinaryAddress.stackContents, go, setPop,
    List.head?_nil, List.tail_nil, Option.isSome_none, cond_false,
    show (1 : Fin 3) ≠ 0 from by decide, ↓reduceIte, Option.getD_some]
  congr 1
  funext k
  rcases k with k | k
  · fin_cases k <;> rfl
  · cases k; rfl

theorem scan_run (w q p s : List Bool) (v : Control) :
    run (w.length+1) (cfg (some (.inr false)) v q p s w) =
      cfg (some (.inr true)) (setPop v none)
        (List.replicate w.length false ++ q) (w.reverse ++ p) s [] := by
  induction w generalizing q p v with
  | nil =>
      rw [show [].length+1 = 0+1 from rfl, run_succ, scan_nil]
      rfl
  | cons b w ih =>
      rw [List.length_cons, run_succ, scan_cons, ih]
      simp only [List.replicate_succ, List.reverse_cons, List.append_assoc,
        List.singleton_append, setPop]
      have hrep : List.replicate w.length false ++ false :: q =
          false :: (List.replicate w.length false ++ q) := by
        induction w.length with
        | zero => rfl
        | succ n ih => simp only [List.replicate_succ, List.cons_append, ih]
      rw [hrep]
      rfl

theorem restore_run (p q s w : List Bool) (v : Control) :
    run (p.length+1) (cfg (some (.inr true)) v q p s w) =
      cfg (some (.inl .readBit)) ((false, false), none)
        (true :: q) [] s (p.reverse ++ w) := by
  induction p generalizing w v with
  | nil =>
      rw [show [].length+1 = 0+1 from rfl, run_succ, restore_nil]
      rfl
  | cons b p ih =>
      rw [List.length_cons, run_succ, restore_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

theorem binary_ready (w : List Bool) :
    run (2*w.length+2) (cfg (some (.inr false)) ((false,false),none) [] [] [] w) =
      cfg (some (.inl .readBit)) ((false,false),none)
        (true :: List.replicate w.length false) [] [] w := by
  rw [show 2*w.length+2 = (w.length+1)+(w.length+1) by omega, run_add, scan_run]
  simp only [List.append_nil]
  have h := restore_run w.reverse (List.replicate w.length false) [] []
    (setPop ((false,false),none) none)
  simpa only [List.length_reverse, List.reverse_reverse, List.append_nil] using h

theorem value_zeros (n a : ℕ) :
    MatrixBinaryAddress.valueFrom n (List.replicate a false) = n * 2^a := by
  induction a generalizing n with
  | zero => simp [MatrixBinaryAddress.valueFrom]
  | succ a ih =>
      simp only [List.replicate_succ, MatrixBinaryAddress.valueFrom,
        MatrixBinaryAddress.bitVal, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      rw [ih, pow_succ]
      ring

theorem value_power (a : ℕ) :
    MatrixBinaryAddress.valueFrom 0 (true :: List.replicate a false) = 2^a := by
  simpa [MatrixBinaryAddress.valueFrom, MatrixBinaryAddress.bitVal] using value_zeros 1 a

/-- Four actual Boolean stacks; arbitrary source words are preserved.
Only their length is used as the exponent. Every work stack is empty at halt. -/
theorem power_run (w : List Bool) :
    ∃ t ≤ 4*2^w.length + 5*w.length + 7,
      run t (cfg (some (.inr false)) ((false,false),none) [] [] [] w) =
        cfg none ((false,false),none) (List.replicate (2^w.length) true) [] [] w := by
  let bits := true :: List.replicate w.length false
  have hd := MatrixBinaryAddress.run_correct bits 0 (false,false)
  simp only [MatrixBinaryAddress.run, List.replicate_zero] at hd
  have hh : (((advance MatrixBinaryAddress.program)^[MatrixBinaryAddress.workFrom 0 bits])
      (MatrixBinaryAddress.cfg (some .readBit) (false,false) bits [] [])).l = none := by
    rw [hd]
    rfl
  obtain ⟨t, ht, he⟩ := lift_outputs MatrixBinaryAddress.program program none (fun _ => rfl)
    (none : Option Bool) (fun _ : Unit => w)
    (MatrixBinaryAddress.cfg (some .readBit) (false,false) bits [] [])
    (MatrixBinaryAddress.workFrom 0 bits) hh
  rw [hd] at he
  change run t (cfg (some (.inl .readBit)) ((false,false),none) bits [] [] w) =
    cfg none ((false,false),none)
      (List.replicate (MatrixBinaryAddress.valueFrom 0 bits) true) [] [] w at he
  have hv : MatrixBinaryAddress.valueFrom 0 bits = 2^w.length := value_power _
  rw [hv] at he
  have hb := MatrixBinaryAddress.workFrom_bound 0 bits
  have hlen : bits.length = w.length+1 := by simp [bits]
  simp only [Nat.mul_zero, Nat.add_zero, hv, hlen] at hb
  refine ⟨2*w.length+2+t, by omega, ?_⟩
  rw [run_add, binary_ready]
  exact he

theorem unary_power_run (a : ℕ) :
    ∃ t ≤ 4*2^a + 5*a + 7,
      run t (cfg (some (.inr false)) ((false,false),none) [] [] [] (List.replicate a true)) =
        cfg none ((false,false),none) (List.replicate (2^a) true) [] []
          (List.replicate a true) := by
  simpa only [List.length_replicate] using power_run (List.replicate a true)

theorem time_le_output_size (a : ℕ) : 4*2^a + 5*a + 7 ≤ 16*2^a := by
  have h : a < 2^a := Nat.lt_two_pow_self
  have hp : 1 ≤ 2^a := Nat.one_le_pow _ _ (by omega)
  omega

noncomputable def machine : BitMachine.Machine :=
  ofFinite (.inr () : Stack) (.inl 0) (.inr false) ((false,false),none) program

theorem outputs (w : List Bool) :
    machine.OutputsWithin w (List.replicate (2^w.length) true) (16*2^w.length) := by
  obtain ⟨t, ht, he⟩ := power_run w
  have hi : rawInit (.inr () : Stack) (.inr false) ((false,false),none) w =
      cfg (some (.inr false)) ((false,false),none) [] [] [] w := by
    unfold rawInit cfg contents
    congr 1
    funext k
    rcases k with k | k
    · fin_cases k <;> rfl
    · cases k; rfl
  apply outputsWithin_of_raw_run (.inr () : Stack) (.inl 0) (.inr false)
    ((false,false),none) program w (List.replicate (2^w.length) true)
    t _ (ht.trans (time_le_output_size _))
  · change (run t _).l = none
    rw [hi, he]
    rfl
  · change (run t _).stk (.inl 0) = _
    rw [hi, he]
    rfl

end EthInapproximability.CurrentPaper.MatrixUnaryPower
