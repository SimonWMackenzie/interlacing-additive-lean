import Paper2.CodeRecursiveSeedPrep

/-! The row seed is constructed by a fixed six-bit append/bit block for
each physically popped raw p-cell, followed by the four-bit empty tail. -/

set_option maxHeartbeats 1000000

namespace Paper2.CodeRecursiveSeedRow

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.CodeRecursiveLoop Paper2.CodeRecursiveSeedPrep

def block : List Bool := [false,true,true,false,true,false]
def tail : List Bool := [false,false,false,false]

def blocks : Nat → List Bool
  | 0 => []
  | p+1 => block ++ blocks p

theorem blocks_rotate (p : Nat) : blocks p ++ block = block ++ blocks p := by
  induction p with
  | zero => rfl
  | succ p ih =>
      simp only [blocks, List.append_assoc]
      rw [ih]

theorem encode_copies_bit (p : Nat) :
    encodeCode (copies p .bit) = blocks p ++ tail := by
  induction p with
  | zero => rfl
  | succ p ih =>
      simp only [copies, encodeCode, blocks, ih]
      rfl

inductive Label where
  | init | loop
  deriving DecidableEq, Fintype

def program : Label →
    TM2.Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .init =>
      push 2 (fun _ => false) (push 2 (fun _ => false)
        (push 2 (fun _ => false) (push 2 (fun _ => false)
          (goto (fun _ => .loop)))))
  | .loop =>
      pop 41 (fun _ b => b)
        (branch Option.isSome
          (push 2 (fun _ => false) (push 2 (fun _ => true)
            (push 2 (fun _ => false) (push 2 (fun _ => true)
              (push 2 (fun _ => true) (push 2 (fun _ => false)
                (goto (fun _ => .loop))))))))
          (load (fun _ => none) halt))

def afterRow (n s q₁ q₂ w Q p : Nat) (fuel : List Bool) :
    Stack → List Bool :=
  Function.update
    (Function.update (afterCountCopy n s q₁ q₂ w Q p fuel)
      41 [])
    2 (encodeCode (copies p .bit))

theorem init_run (S : Stack → List Bool) (h : S 2 = []) :
    advance program
      (⟨some .init, none, S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool)) =
      ⟨some .loop, none, Function.update S 2 tail⟩ := by
  simp [advance, TM2.step, program, TM2.stepAux, tail, h]

theorem loop_step_cons (S : Stack → List Bool) (v : Option Bool)
    (b : Bool) (rest : List Bool) (h : S 41 = b::rest) :
    advance program
      (⟨some .loop, v, S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool)) =
      ⟨some .loop, some b,
        Function.update (Function.update S 41 rest)
          2 (block ++ S 2)⟩ := by
  simp [advance, TM2.step, program, TM2.stepAux, h, block]

theorem loop_step_nil (S : Stack → List Bool) (v : Option Bool)
    (h : S 41 = []) :
    advance program
      (⟨some .loop, v, S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool)) =
      ⟨none, none, S⟩ := by
  simp [advance, TM2.step, program, TM2.stepAux, h]

theorem loop_run (p : Nat) (S : Stack → List Bool) (v : Option Bool)
    (hcount : S 41 = List.replicate p true) :
    ((advance program)^[p+1])
      (⟨some .loop, v, S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool)) =
      ⟨none, none,
        Function.update (Function.update S 41 []) 2
          (blocks p ++ S 2)⟩ := by
  induction p generalizing S v with
  | zero =>
      have h := loop_step_nil S v (by simpa using hcount)
      have hnil : S 41 = [] := by simpa using hcount
      have he : Function.update (Function.update S 41 []) 2 (S 2) = S := by
        funext i
        by_cases hi2 : i = (2 : Stack)
        · subst i; simp
        · by_cases hi41 : i = (41 : Stack)
          · subst i; simp [hnil]
          · simp [hi2, hi41]
      simpa [blocks, he] using h
  | succ p ih =>
      let T := Function.update
        (Function.update S 41 (List.replicate p true))
        2 (block ++ S 2)
      have hstep := loop_step_cons S v true
        (List.replicate p true) (by simpa using hcount)
      have hT : T 41 = List.replicate p true := by
        simp [T]
      have hrun := ih T (some true) hT
      rw [show (p+1)+1 = (p+1)+1 by rfl,
        Function.iterate_succ_apply, hstep, hrun]
      congr 1
      funext i
      have hword : blocks p ++ (block ++ S 2) =
          blocks (p+1) ++ S 2 := by
        rw [← List.append_assoc, blocks_rotate]
        rfl
      by_cases hi2 : i = (2 : Stack)
      · subst i
        simp [T, hword]
      · by_cases hi41 : i = (41 : Stack)
        · subst i
          simp [T]
        · simp [T, hi2, hi41]

theorem run_exact (n s q₁ q₂ w Q p : Nat) (fuel : List Bool) :
    ((advance program)^[p+2])
      (⟨some .init, none,
        afterCountCopy n s q₁ q₂ w Q p fuel⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool)) =
      ⟨none, none, afterRow n s q₁ q₂ w Q p fuel⟩ := by
  let S := afterCountCopy n s q₁ q₂ w Q p fuel
  have hblank : S 2 = [] := by simp [S, afterCountCopy,
    afterTicket, publicBase]
  have hcount : (Function.update S 2 tail) 41 =
      List.replicate p true := by
    simp [S, afterCountCopy]
  have hi := init_run S hblank
  have hr := loop_run p (Function.update S 2 tail) none hcount
  rw [show p+2 = (p+1)+1 by omega,
    Function.iterate_succ_apply, hi, hr]
  congr 1
  funext i
  have hword := encode_copies_bit p
  by_cases hi2 : i = (2 : Stack)
  · subst i
    simp [afterRow, S, hword, tail]
  · by_cases hi41 : i = (41 : Stack)
    · subst i
      simp [afterRow, S]
    · simp [afterRow, S, hi2, hi41]

#print axioms run_exact

end Paper2.CodeRecursiveSeedRow
