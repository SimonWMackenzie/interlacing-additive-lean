import Paper2.A4BankOut

/-!
# Unit 4 (Paper A), N-4: the `k`-UNIFORM bank assembler

Owner lane `owner:a-unit4-shell-4` (private, 26 September 2026).

ONE fixed finite machine `machine` (it does NOT depend on `k`) maps the literal word
`pair (packet n w) (pair (1^k) t) = field (field (1^n) ++ field w) ++ field (1^k) ++ t`
to the literal H-A3 bank `BitMachineBankCodec.encode ![w, 1^k, t]`, for every `k`, `n`, `w`,
`t`. The unary `k` is READ from the input (parsed into its own stack and re-emitted), in place
of the fixed-`k` statement `unaryFieldStmt k` of `BankOut.machine k`. Five stacks: `0` (input
AND output), `1` (temp), `2` (packet), `3` (junk), `4` (unary `k`). Phases (fixed statements
of `R3Loops`):

1. parse the outer field (the packet) from stack 0 onto temp; stack 0 keeps `field (1^k) ++ t`;
2. move temp to stack 2 (stack 2 = the packet);
3. parse the unary field `1^n` off stack 2 into the junk stack (stack 2 = `field w`);
4. parse the unary field `1^k` off stack 0 into stack 4 (stack 0 = `t`);
5. move `t` from stack 0 to temp; push `false`; emit temp onto stack 0 (stack 0 = `field t`);
6. push `false`; emit stack 4 onto stack 0 (stack 0 = `field (1^k) ++ field t`);
7. move `field w` from stack 2 to temp, then from temp to stack 0; `done` halts.

Linear clock `10·(|input| + 1)`. Every step is one `TM2.step` of a literal statement;
`pushBound` of every statement is at most `2`. No input is inserted: the machine starts from
`Machine.init`. **No ledger row is closed.**
-/

namespace Paper2.Unit4Shell.BankOutU

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.Unit4Shell.Loops

inductive BL
  | p1 | p2 | p3 | pk | p4 | p5a | p5 | p6a | p6 | p7 | p8 | done
  deriving DecidableEq, Fintype

abbrev Stack := Fin 5
abbrev Control := Option Bool × Unit

/-- The fixed program (no parameter). -/
def program : BL → TM2.Stmt (fun _ : Stack => Bool) BL Control
  | .p1 => parseStmt 0 1 .p1 .p2
  | .p2 => moveStmt 1 2 .p2 .p3
  | .p3 => parseStmt 2 3 .p3 .pk
  | .pk => parseStmt 0 4 .pk .p4
  | .p4 => moveStmt 0 1 .p4 .p5a
  | .p5a => pushFalseStmt 0 .p5
  | .p5 => emitStmt 1 0 .p5 .p6a
  | .p6a => pushFalseStmt 0 .p6
  | .p6 => emitStmt 4 0 .p6 .p7
  | .p7 => moveStmt 2 1 .p7 .p8
  | .p8 => moveStmt 1 0 .p8 .done
  | .done => .halt

/-- THE fixed `k`-uniform bank assembler. -/
noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Stack) (0 : Stack) BL.p1 ((none, ()) : Control) program

theorem machine_outputs (k n : ℕ) (w t : List Bool) :
    machine.OutputsWithin
      (EncodedComplexity.pair (SourceOriginalBranchPackets.packet n w)
        (EncodedComplexity.pair (List.replicate k true) t))
      (BitMachineBankCodec.encode ![w, List.replicate k true, t])
      (10 * ((EncodedComplexity.pair (SourceOriginalBranchPackets.packet n w)
        (EncodedComplexity.pair (List.replicate k true) t)).length + 1)) := by
  set P := SourceOriginalBranchPackets.packet n w with hP
  set FW := EncodedCommunication.field w with hFW
  set U := List.replicate k true with hU
  set Q := EncodedComplexity.pair U t with hQ
  let S0 : Stack → List Bool := fun j => if j = 0 then EncodedComplexity.pair P Q else []
  -- 1. parse the packet field
  have e1 := parse_loop program (0 : Stack) 1 BL.p1 BL.p2 (by decide) rfl P Q S0 none ()
    (by simp [S0, EncodedComplexity.pair])
  set S1 := Function.update (Function.update S0 1 (P.reverse ++ S0 1)) 0 Q with hS1
  -- 2. restore the packet on stack 2
  have h1 : S1 1 = P.reverse := by simp [hS1, S0]
  have e2 := move_loop program (1 : Stack) 2 BL.p2 BL.p3 (by decide) rfl P.reverse S1
    (some false) () h1
  rw [List.length_reverse] at e2
  set S2 := Function.update (Function.update S1 2 (P.reverse.reverse ++ S1 2)) 1 [] with hS2
  -- 3. discard the unary field `1^n`
  have h2 : S2 2 = EncodedCommunication.field (List.replicate n true) ++ FW := by
    simp [hS2, hS1, S0, hP, hFW, BankOut.packet_eq]
  have e3 := parse_loop program (2 : Stack) 3 BL.p3 BL.pk (by decide) rfl
    (List.replicate n true) FW S2 none () h2
  rw [List.length_replicate] at e3
  set S3 := Function.update (Function.update S2 3 ((List.replicate n true).reverse ++ S2 3))
    2 FW with hS3
  -- 4. read the unary field `1^k` into stack 4
  have hk3 : S3 0 = EncodedCommunication.field U ++ t := by
    simp [hS3, hS2, hS1, S0, hQ, EncodedComplexity.pair]
  have ek := parse_loop program (0 : Stack) 4 BL.pk BL.p4 (by decide) rfl U t S3
    (some false) () hk3
  set S3k := Function.update (Function.update S3 4 (U.reverse ++ S3 4)) 0 t with hS3k
  -- 5. reverse `t` onto temp, then write `field t`
  have h3 : S3k 0 = t := by simp [hS3k]
  have e4 := move_loop program (0 : Stack) 1 BL.p4 BL.p5a (by decide) rfl t S3k
    (some false) () h3
  set S4 := Function.update (Function.update S3k 1 (t.reverse ++ S3k 1)) 0 [] with hS4
  have e5 := pushFalse_step program (0 : Stack) BL.p5a BL.p5 rfl (none, ()) S4
  set S5 := Function.update S4 0 (false :: S4 0) with hS5
  have h5 : S5 1 = t.reverse := by simp [hS5, hS4, hS3k, hS3, hS2, hS1, S0]
  have e6 := emit_loop program (1 : Stack) 0 BL.p5 BL.p6a (by decide) rfl t.reverse S5
    none () h5
  rw [List.length_reverse] at e6
  set S6 := Function.update (Function.update S5 0 (t.reverse.foldl emitFold (S5 0))) 1 []
    with hS6
  have h60 : S6 0 = EncodedCommunication.field t ++ [] := by
    have : S5 0 = false :: [] := by simp [hS5, hS4]
    simp only [hS6, Function.update_of_ne (by decide : (0 : Stack) ≠ 1), Function.update_self,
      this]
    exact emit_reverse_field t []
  -- 6. write `field (1^k)` from stack 4
  have e7 := pushFalse_step program (0 : Stack) BL.p6a BL.p6 rfl (none, ()) S6
  set S6a := Function.update S6 0 (false :: S6 0) with hS6a
  have h6a : S6a 4 = U.reverse := by simp [hS6a, hS6, hS5, hS4, hS3k, hS3, hS2, hS1, S0]
  have e7b := emit_loop program (4 : Stack) 0 BL.p6 BL.p7 (by decide) rfl U.reverse S6a
    none () h6a
  rw [List.length_reverse] at e7b
  set S7 := Function.update (Function.update S6a 0 (U.reverse.foldl emitFold (S6a 0))) 4 []
    with hS7
  have h70 : S7 0 = EncodedCommunication.field U ++ (EncodedCommunication.field t ++ []) := by
    have : S6a 0 = false :: (EncodedCommunication.field t ++ []) := by
      simp only [hS6a, Function.update_self, h60]
    simp only [hS7, Function.update_of_ne (by decide : (0 : Stack) ≠ 4), Function.update_self,
      this]
    exact emit_reverse_field U _
  -- 7, 8. write `field w`
  have h7 : S7 2 = FW := by simp [hS7, hS6a, hS6, hS5, hS4, hS3k, hS3]
  have e8 := move_loop program (2 : Stack) 1 BL.p7 BL.p8 (by decide) rfl FW S7 none () h7
  set S8 := Function.update (Function.update S7 1 (FW.reverse ++ S7 1)) 2 [] with hS8
  have h8 : S8 1 = FW.reverse := by simp [hS8, hS7, hS6a, hS6]
  have e9 := move_loop program (1 : Stack) 0 BL.p8 BL.done (by decide) rfl FW.reverse S8
    none () h8
  rw [List.length_reverse] at e9
  set S9 := Function.update (Function.update S8 0 (FW.reverse.reverse ++ S8 0)) 1 [] with hS9
  have e10 := halt_step program BL.done rfl (none, ()) S9
  have h9 : S9 0 = BitMachineBankCodec.encode ![w, List.replicate k true, t] := by
    rw [BankOut.bank3_eq, ← hFW, ← hU, ← h70]
    simp [hS9, hS8]
  -- chain
  have r := iter_chain (iter_chain (iter_chain (iter_chain (iter_chain (iter_chain
    (iter_chain (iter_chain (iter_chain (iter_chain (iter_chain e1 e2) e3) ek) e4)
    (show (advance program)^[1] _ = _ from e5)) e6)
    (show (advance program)^[1] _ = _ from e7)) e7b) e8) e9)
    (show (advance program)^[1] _ = _ from e10)
  have hraw : rawInit (0 : Stack) BL.p1 ((none, ()) : Control)
      (EncodedComplexity.pair P Q) = ⟨some BL.p1, (none, ()), S0⟩ := rfl
  have hPl := SourceOriginalBranchPackets.packet_length n w
  have hFl := EncodedCommunication.field_length w
  have hUl : U.length = k := by simp [hU]
  refine outputsWithin_of_raw_run (0 : Stack) (0 : Stack) BL.p1 ((none, ()) : Control)
    program (EncodedComplexity.pair P Q)
    (BitMachineBankCodec.encode ![w, List.replicate k true, t])
    (P.length + 1 + (P.length + 1) + (n + 1) + (U.length + 1) + (t.length + 1) + 1 +
      (t.length + 1) + 1 + (U.length + 1) + (FW.length + 1) + (FW.length + 1) + 1) _ ?_ ?_ ?_
  · rw [hQ, EncodedComplexity.pair_length, EncodedComplexity.pair_length]
    rw [← hP] at hPl
    rw [← hFW] at hFl
    omega
  · rw [hraw, r]
  · rw [hraw, r]
    exact h9

/-- **The `k`-uniform bank assembler.** ONE fixed machine, linear clock, for every `k`.
Does not close a ledger row. -/
theorem bank_out_uniform :
    ∃ (MB : BitMachine.Machine) (CB EB : ℕ), ∀ (k n : ℕ) (w t : List Bool),
      MB.OutputsWithin
        (EncodedComplexity.pair (SourceOriginalBranchPackets.packet n w)
          (EncodedComplexity.pair (List.replicate k true) t))
        (BitMachineBankCodec.encode ![w, List.replicate k true, t])
        (CB * ((EncodedComplexity.pair (SourceOriginalBranchPackets.packet n w)
          (EncodedComplexity.pair (List.replicate k true) t)).length + 1) ^ EB) :=
  ⟨machine, 10, 1, fun k n w t => by
    simpa only [pow_one] using machine_outputs k n w t⟩

#print axioms machine_outputs
#print axioms bank_out_uniform

end Paper2.Unit4Shell.BankOutU
