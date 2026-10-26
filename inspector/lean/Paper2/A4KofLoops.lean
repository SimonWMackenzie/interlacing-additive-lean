import Paper2.A4BankOut

/-!
# Unit 4 (Paper A), N-4 (1b): fixed field-shuffling machines for the `kOf N` front

Owner lane `owner:a-unit4-shell-4` (private, 26 September 2026).

Three FIXED finite machines (no parameter), built from the fixed statements of `R3Loops` plus
one new fixed loop `dupStmt a b c` (pop every bit of `a`, push it on `b` AND on `c`):

* `DupField.machine`: `field x ++ t ↦ field x ++ field x ++ t`;
* `WrapDup.machine`: `1^N ↦ field (1^N) ++ field (1^N) ++ [false, false, false, false]`
  (the four trailing `false`s are the four empty fields of the six-bank division packet);
* `Swap.machine`: `field a ++ field b ++ t ↦ field b ++ field a ++ t`.

Every step is one `TM2.step` of a literal statement; nothing is inserted; the machines start
from `Machine.init`. **No ledger row is closed.**
-/

namespace Paper2.Unit4Shell.KofLoops

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.Unit4Shell.Loops

section Dup

variable {K Λ W : Type*} [DecidableEq K]

/-- Pop every bit of `a`, pushing it onto `b` and onto `c`. -/
def dupStmt (a b c : K) (here next : Λ) : TM2.Stmt (fun _ : K => Bool) Λ (Option Bool × W) :=
  .pop a setBit (.branch (fun v => v.1.isSome)
    (.push b (fun v => v.1.getD false) (.push c (fun v => v.1.getD false)
      (.goto fun _ => here)))
    (.goto fun _ => next))

variable (P : Λ → TM2.Stmt (fun _ : K => Bool) Λ (Option Bool × W))

theorem dup_loop (a b c : K) (here next : Λ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hP : P here = dupStmt a b c here next) :
    ∀ (xs : List Bool) (S : K → List Bool) (o : Option Bool) (w : W), S a = xs →
      (advance P)^[xs.length + 1] ⟨some here, (o, w), S⟩ =
        ⟨some next, (none, w),
          Function.update (Function.update (Function.update S b (xs.reverse ++ S b)) c
            (xs.reverse ++ S c)) a []⟩ := by
  intro xs
  induction xs with
  | nil =>
      intro S o w hS
      simp only [List.length_nil, zero_add, Function.iterate_one, List.reverse_nil,
        List.nil_append, Function.update_eq_self]
      simp [advance, TM2.step, TM2.stepAux, hP, dupStmt, setBit, hS]
  | cons x xs ih =>
      intro S o w hS
      have h1 : advance P ⟨some here, (o, w), S⟩ =
          ⟨some here, (some x, w),
            Function.update (Function.update (Function.update S a xs) b (x :: S b)) c
              (x :: S c)⟩ := by
        simp [advance, TM2.step, TM2.stepAux, hP, dupStmt, setBit, hS,
          Function.update_of_ne hab.symm, Function.update_of_ne hac.symm,
          Function.update_of_ne hbc.symm]
      rw [List.length_cons, Function.iterate_succ_apply, h1,
        ih _ _ _ (by simp [Function.update_of_ne hab, Function.update_of_ne hac])]
      congr 1
      funext j
      simp only [Function.update_apply]
      split_ifs <;> simp_all

end Dup

abbrev Control := Option Bool × Unit

/-! ## `DupField`: `field x ++ t ↦ field x ++ field x ++ t` -/

namespace DupField

inductive DL
  | d1 | d2 | d3 | d4 | d5 | d6 | d7 | done
  deriving DecidableEq, Fintype

abbrev Stack := Fin 4

def program : DL → TM2.Stmt (fun _ : Stack => Bool) DL Control
  | .d1 => parseStmt 0 1 .d1 .d2
  | .d2 => moveStmt 1 2 .d2 .d3
  | .d3 => dupStmt 2 1 3 .d3 .d4
  | .d4 => pushFalseStmt 0 .d5
  | .d5 => emitStmt 1 0 .d5 .d6
  | .d6 => pushFalseStmt 0 .d7
  | .d7 => emitStmt 3 0 .d7 .done
  | .done => .halt

noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Stack) (0 : Stack) DL.d1 ((none, ()) : Control) program

theorem machine_outputs (x t : List Bool) :
    machine.OutputsWithin (EncodedComplexity.pair x t)
      (EncodedComplexity.pair x (EncodedComplexity.pair x t))
      (6 * ((EncodedComplexity.pair x t).length + 1)) := by
  let S0 : Stack → List Bool := fun j => if j = 0 then EncodedComplexity.pair x t else []
  have e1 := parse_loop program (0 : Stack) 1 DL.d1 DL.d2 (by decide) rfl x t S0 none ()
    (by simp [S0, EncodedComplexity.pair])
  set S1 := Function.update (Function.update S0 1 (x.reverse ++ S0 1)) 0 t with hS1
  have h1 : S1 1 = x.reverse := by simp [hS1, S0]
  have e2 := move_loop program (1 : Stack) 2 DL.d2 DL.d3 (by decide) rfl x.reverse S1
    (some false) () h1
  rw [List.length_reverse] at e2
  set S2 := Function.update (Function.update S1 2 (x.reverse.reverse ++ S1 2)) 1 [] with hS2
  have h2 : S2 2 = x := by simp [hS2, hS1, S0]
  have e3 := dup_loop program (2 : Stack) 1 3 DL.d3 DL.d4 (by decide) (by decide) (by decide)
    rfl x S2 none () h2
  set S3 := Function.update (Function.update (Function.update S2 1 (x.reverse ++ S2 1)) 3
    (x.reverse ++ S2 3)) 2 [] with hS3
  have e4 := pushFalse_step program (0 : Stack) DL.d4 DL.d5 rfl (none, ()) S3
  set S4 := Function.update S3 0 (false :: S3 0) with hS4
  have h4 : S4 1 = x.reverse := by simp [hS4, hS3, hS2]
  have e5 := emit_loop program (1 : Stack) 0 DL.d5 DL.d6 (by decide) rfl x.reverse S4
    none () h4
  rw [List.length_reverse] at e5
  set S5 := Function.update (Function.update S4 0 (x.reverse.foldl emitFold (S4 0))) 1 []
    with hS5
  have h50 : S5 0 = EncodedCommunication.field x ++ t := by
    have : S4 0 = false :: t := by simp [hS4, hS3, hS2, hS1]
    simp only [hS5, Function.update_of_ne (by decide : (0 : Stack) ≠ 1), Function.update_self,
      this]
    exact emit_reverse_field x t
  have e6 := pushFalse_step program (0 : Stack) DL.d6 DL.d7 rfl (none, ()) S5
  set S6 := Function.update S5 0 (false :: S5 0) with hS6
  have h6 : S6 3 = x.reverse := by simp [hS6, hS5, hS4, hS3, hS2, hS1, S0]
  have e7 := emit_loop program (3 : Stack) 0 DL.d7 DL.done (by decide) rfl x.reverse S6
    none () h6
  rw [List.length_reverse] at e7
  set S7 := Function.update (Function.update S6 0 (x.reverse.foldl emitFold (S6 0))) 3 []
    with hS7
  have h70 : S7 0 = EncodedCommunication.field x ++ (EncodedCommunication.field x ++ t) := by
    have : S6 0 = false :: (EncodedCommunication.field x ++ t) := by
      simp only [hS6, Function.update_self, h50]
    simp only [hS7, Function.update_of_ne (by decide : (0 : Stack) ≠ 3), Function.update_self,
      this]
    exact emit_reverse_field x _
  have e8 := halt_step program DL.done rfl (none, ()) S7
  have r := iter_chain (iter_chain (iter_chain (iter_chain (iter_chain (iter_chain
    (iter_chain e1 e2) e3) (show (advance program)^[1] _ = _ from e4)) e5)
    (show (advance program)^[1] _ = _ from e6)) e7)
    (show (advance program)^[1] _ = _ from e8)
  have hraw : rawInit (0 : Stack) DL.d1 ((none, ()) : Control)
      (EncodedComplexity.pair x t) = ⟨some DL.d1, (none, ()), S0⟩ := rfl
  refine outputsWithin_of_raw_run (0 : Stack) (0 : Stack) DL.d1 ((none, ()) : Control)
    program (EncodedComplexity.pair x t)
    (EncodedComplexity.pair x (EncodedComplexity.pair x t))
    (x.length + 1 + (x.length + 1) + (x.length + 1) + 1 + (x.length + 1) + 1 +
      (x.length + 1) + 1) _ ?_ ?_ ?_
  · rw [EncodedComplexity.pair_length]
    omega
  · rw [hraw, r]
  · rw [hraw, r]
    simp only [EncodedComplexity.pair]
    exact h70

end DupField

/-! ## `WrapDup`: `1^N ↦ field (1^N) ++ field (1^N) ++ [false, false, false, false]` -/

namespace WrapDup

inductive WL
  | w1 | w2 | f1 | f2 | f3 | f4 | w3 | w4 | w5 | w6 | done
  deriving DecidableEq, Fintype

abbrev Stack := Fin 4

def program : WL → TM2.Stmt (fun _ : Stack => Bool) WL Control
  | .w1 => moveStmt 0 1 .w1 .w2
  | .w2 => dupStmt 1 2 3 .w2 .f1
  | .f1 => pushFalseStmt 0 .f2
  | .f2 => pushFalseStmt 0 .f3
  | .f3 => pushFalseStmt 0 .f4
  | .f4 => pushFalseStmt 0 .w3
  | .w3 => pushFalseStmt 0 .w4
  | .w4 => emitStmt 2 0 .w4 .w5
  | .w5 => pushFalseStmt 0 .w6
  | .w6 => emitStmt 3 0 .w6 .done
  | .done => .halt

noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Stack) (0 : Stack) WL.w1 ((none, ()) : Control) program

/-- The output word. -/
def out (N : ℕ) : List Bool :=
  EncodedCommunication.field (List.replicate N true) ++
    (EncodedCommunication.field (List.replicate N true) ++ [false, false, false, false])

theorem machine_outputs (N : ℕ) :
    machine.OutputsWithin (List.replicate N true) (out N) (4 * N + 12) := by
  set U := List.replicate N true with hU
  have hUr : U.reverse = U := by simp [hU]
  let S0 : Stack → List Bool := fun j => if j = 0 then U else []
  have e1 := move_loop program (0 : Stack) 1 WL.w1 WL.w2 (by decide) rfl U S0 none ()
    (by simp [S0])
  set S1 := Function.update (Function.update S0 1 (U.reverse ++ S0 1)) 0 [] with hS1
  have h1 : S1 1 = U := by simp [hS1, S0, hUr]
  have e2 := dup_loop program (1 : Stack) 2 3 WL.w2 WL.f1 (by decide) (by decide) (by decide)
    rfl U S1 none () h1
  set S2 := Function.update (Function.update (Function.update S1 2 (U.reverse ++ S1 2)) 3
    (U.reverse ++ S1 3)) 1 [] with hS2
  have ef1 := pushFalse_step program (0 : Stack) WL.f1 WL.f2 rfl (none, ()) S2
  set T1 := Function.update S2 0 (false :: S2 0) with hT1
  have ef2 := pushFalse_step program (0 : Stack) WL.f2 WL.f3 rfl (none, ()) T1
  set T2 := Function.update T1 0 (false :: T1 0) with hT2
  have ef3 := pushFalse_step program (0 : Stack) WL.f3 WL.f4 rfl (none, ()) T2
  set T3 := Function.update T2 0 (false :: T2 0) with hT3
  have ef4 := pushFalse_step program (0 : Stack) WL.f4 WL.w3 rfl (none, ()) T3
  set T4 := Function.update T3 0 (false :: T3 0) with hT4
  have ew3 := pushFalse_step program (0 : Stack) WL.w3 WL.w4 rfl (none, ()) T4
  set T5 := Function.update T4 0 (false :: T4 0) with hT5
  have h5 : T5 2 = U := by simp [hT5, hT4, hT3, hT2, hT1, hS2, hS1, S0, hUr]
  have e4 := emit_loop program (2 : Stack) 0 WL.w4 WL.w5 (by decide) rfl U T5 none () h5
  set T6 := Function.update (Function.update T5 0 (U.foldl emitFold (T5 0))) 2 [] with hT6
  have h60 : T6 0 = EncodedCommunication.field U ++ [false, false, false, false] := by
    have : T5 0 = false :: [false, false, false, false] := by
      simp [hT5, hT4, hT3, hT2, hT1, hS2, hS1]
    simp only [hT6, Function.update_of_ne (by decide : (0 : Stack) ≠ 2), Function.update_self,
      this]
    have := emit_reverse_field U [false, false, false, false]
    rwa [hUr] at this
  have ew5 := pushFalse_step program (0 : Stack) WL.w5 WL.w6 rfl (none, ()) T6
  set T7 := Function.update T6 0 (false :: T6 0) with hT7
  have h7 : T7 3 = U := by simp [hT7, hT6, hT5, hT4, hT3, hT2, hT1, hS2, hS1, S0, hUr]
  have e6 := emit_loop program (3 : Stack) 0 WL.w6 WL.done (by decide) rfl U T7 none () h7
  set T8 := Function.update (Function.update T7 0 (U.foldl emitFold (T7 0))) 3 [] with hT8
  have h80 : T8 0 = out N := by
    have : T7 0 = false :: (EncodedCommunication.field U ++ [false, false, false, false]) := by
      simp only [hT7, Function.update_self, h60]
    simp only [hT8, Function.update_of_ne (by decide : (0 : Stack) ≠ 3), Function.update_self,
      this, out, ← hU]
    have := emit_reverse_field U (EncodedCommunication.field U ++ [false, false, false, false])
    rwa [hUr] at this
  have e7 := halt_step program WL.done rfl (none, ()) T8
  have r := iter_chain (iter_chain (iter_chain (iter_chain (iter_chain (iter_chain (iter_chain
    (iter_chain (iter_chain (iter_chain e1 e2)
    (show (advance program)^[1] _ = _ from ef1))
    (show (advance program)^[1] _ = _ from ef2))
    (show (advance program)^[1] _ = _ from ef3))
    (show (advance program)^[1] _ = _ from ef4))
    (show (advance program)^[1] _ = _ from ew3)) e4)
    (show (advance program)^[1] _ = _ from ew5)) e6)
    (show (advance program)^[1] _ = _ from e7)
  have hraw : rawInit (0 : Stack) WL.w1 ((none, ()) : Control) U =
      ⟨some WL.w1, (none, ()), S0⟩ := rfl
  have hUl : U.length = N := by simp [hU]
  refine outputsWithin_of_raw_run (0 : Stack) (0 : Stack) WL.w1 ((none, ()) : Control)
    program U (out N)
    (U.length + 1 + (U.length + 1) + 1 + 1 + 1 + 1 + 1 + (U.length + 1) + 1 +
      (U.length + 1) + 1) _ ?_ ?_ ?_
  · omega
  · rw [hraw, r]
  · rw [hraw, r]
    exact h80

theorem out_length (N : ℕ) : (out N).length = 4 * N + 6 := by
  simp [out, EncodedCommunication.field_length]
  omega

end WrapDup

/-! ## `Swap`: `field a ++ field b ++ t ↦ field b ++ field a ++ t` -/

namespace Swap

inductive SL
  | s1 | s2 | s3 | s4 | s5 | s6 | done
  deriving DecidableEq, Fintype

abbrev Stack := Fin 3

def program : SL → TM2.Stmt (fun _ : Stack => Bool) SL Control
  | .s1 => parseStmt 0 1 .s1 .s2
  | .s2 => parseStmt 0 2 .s2 .s3
  | .s3 => pushFalseStmt 0 .s4
  | .s4 => emitStmt 1 0 .s4 .s5
  | .s5 => pushFalseStmt 0 .s6
  | .s6 => emitStmt 2 0 .s6 .done
  | .done => .halt

noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Stack) (0 : Stack) SL.s1 ((none, ()) : Control) program

theorem machine_outputs (a b t : List Bool) :
    machine.OutputsWithin (EncodedComplexity.pair a (EncodedComplexity.pair b t))
      (EncodedComplexity.pair b (EncodedComplexity.pair a t))
      (3 * ((EncodedComplexity.pair a (EncodedComplexity.pair b t)).length + 1)) := by
  let S0 : Stack → List Bool := fun j =>
    if j = 0 then EncodedComplexity.pair a (EncodedComplexity.pair b t) else []
  have e1 := parse_loop program (0 : Stack) 1 SL.s1 SL.s2 (by decide) rfl a
    (EncodedComplexity.pair b t) S0 none () (by simp [S0, EncodedComplexity.pair])
  set S1 := Function.update (Function.update S0 1 (a.reverse ++ S0 1)) 0
    (EncodedComplexity.pair b t) with hS1
  have e2 := parse_loop program (0 : Stack) 2 SL.s2 SL.s3 (by decide) rfl b t S1
    (some false) () (by simp [hS1, EncodedComplexity.pair])
  set S2 := Function.update (Function.update S1 2 (b.reverse ++ S1 2)) 0 t with hS2
  have e3 := pushFalse_step program (0 : Stack) SL.s3 SL.s4 rfl (some false, ()) S2
  set S3 := Function.update S2 0 (false :: S2 0) with hS3
  have h3 : S3 1 = a.reverse := by simp [hS3, hS2, hS1, S0]
  have e4 := emit_loop program (1 : Stack) 0 SL.s4 SL.s5 (by decide) rfl a.reverse S3
    (some false) () h3
  rw [List.length_reverse] at e4
  set S4 := Function.update (Function.update S3 0 (a.reverse.foldl emitFold (S3 0))) 1 []
    with hS4
  have h40 : S4 0 = EncodedCommunication.field a ++ t := by
    have : S3 0 = false :: t := by simp [hS3, hS2]
    simp only [hS4, Function.update_of_ne (by decide : (0 : Stack) ≠ 1), Function.update_self,
      this]
    exact emit_reverse_field a t
  have e5 := pushFalse_step program (0 : Stack) SL.s5 SL.s6 rfl (none, ()) S4
  set S5 := Function.update S4 0 (false :: S4 0) with hS5
  have h5 : S5 2 = b.reverse := by simp [hS5, hS4, hS3, hS2, hS1, S0]
  have e6 := emit_loop program (2 : Stack) 0 SL.s6 SL.done (by decide) rfl b.reverse S5
    none () h5
  rw [List.length_reverse] at e6
  set S6 := Function.update (Function.update S5 0 (b.reverse.foldl emitFold (S5 0))) 2 []
    with hS6
  have h60 : S6 0 = EncodedCommunication.field b ++ (EncodedCommunication.field a ++ t) := by
    have : S5 0 = false :: (EncodedCommunication.field a ++ t) := by
      simp only [hS5, Function.update_self, h40]
    simp only [hS6, Function.update_of_ne (by decide : (0 : Stack) ≠ 2), Function.update_self,
      this]
    exact emit_reverse_field b _
  have e7 := halt_step program SL.done rfl (none, ()) S6
  have r := iter_chain (iter_chain (iter_chain (iter_chain (iter_chain (iter_chain e1 e2)
    (show (advance program)^[1] _ = _ from e3)) e4)
    (show (advance program)^[1] _ = _ from e5)) e6)
    (show (advance program)^[1] _ = _ from e7)
  have hraw : rawInit (0 : Stack) SL.s1 ((none, ()) : Control)
      (EncodedComplexity.pair a (EncodedComplexity.pair b t)) = ⟨some SL.s1, (none, ()), S0⟩ :=
    rfl
  refine outputsWithin_of_raw_run (0 : Stack) (0 : Stack) SL.s1 ((none, ()) : Control)
    program (EncodedComplexity.pair a (EncodedComplexity.pair b t))
    (EncodedComplexity.pair b (EncodedComplexity.pair a t))
    (a.length + 1 + (b.length + 1) + 1 + (a.length + 1) + 1 + (b.length + 1) + 1) _ ?_ ?_ ?_
  · rw [EncodedComplexity.pair_length, EncodedComplexity.pair_length]
    omega
  · rw [hraw, r]
  · rw [hraw, r]
    simp only [EncodedComplexity.pair]
    exact h60

end Swap

#print axioms dup_loop
#print axioms DupField.machine_outputs
#print axioms WrapDup.machine_outputs
#print axioms Swap.machine_outputs

end Paper2.Unit4Shell.KofLoops
