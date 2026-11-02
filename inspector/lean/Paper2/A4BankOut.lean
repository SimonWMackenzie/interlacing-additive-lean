import Paper2.A4Loops
import EthInapproximability.CurrentPaper.EncodedComplexity
import EthInapproximability.CurrentPaper.SourceOriginalBranchPackets

/-!
# Unit 4 (Paper A) glue: the physical bank assembler `H_BankOut k`

Owner lane `owner:a-unit4-shell-3` (private, 26 September 2026).

For every fixed `k` ONE fixed finite machine `machine k` maps the literal word
`pair (packet n w) t = field (field (1^n) ++ field w) ++ t` to the literal H-A3 bank
`BitMachineBankCodec.encode ![w, 1^k, t] = field w ++ field (1^k) ++ field t`, for every
`n`, `w`, `t`. Four stacks: `0` (input AND output), `1` (temp), `2` (packet), `3` (junk).
Phases (fixed statements of `R3Loops`):

1. parse the outer field (the packet) from stack 0 onto temp (reversed); stack 0 keeps `t`;
2. move temp to stack 2 (stack 2 = the packet);
3. parse the unary field `1^n` off stack 2 into the junk stack (stack 2 = `field w`);
4. move `t` from stack 0 to temp (reversed);
5. push `false`, then emit the reversed `t` onto stack 0 (stack 0 = `field t`);
6. push `field (1^k)` onto stack 0 in one step (`k` is a constant of the statement);
7. move `field w` from stack 2 to temp, 8. then from temp to stack 0; `done` halts.

Linear clock `10·(|input| + 1)`. The unary `n` is discarded (charged, not used). No input
is inserted: the machine starts from `Machine.init`. **No ledger row is closed.**
-/

namespace Paper2.Unit4Shell.BankOut

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.Unit4Shell.Loops

inductive BL
  | p1 | p2 | p3 | p4 | p5a | p5 | p6 | p7 | p8 | done
  deriving DecidableEq, Fintype

abbrev Stack := Fin 4
abbrev Control := Option Bool × Unit

def program (k : ℕ) : BL → TM2.Stmt (fun _ : Stack => Bool) BL Control
  | .p1 => parseStmt 0 1 .p1 .p2
  | .p2 => moveStmt 1 2 .p2 .p3
  | .p3 => parseStmt 2 3 .p3 .p4
  | .p4 => moveStmt 0 1 .p4 .p5a
  | .p5a => pushFalseStmt 0 .p5
  | .p5 => emitStmt 1 0 .p5 .p6
  | .p6 => unaryFieldStmt 0 k .p7
  | .p7 => moveStmt 2 1 .p7 .p8
  | .p8 => moveStmt 1 0 .p8 .done
  | .done => .halt

/-- THE fixed bank assembler for `k`. -/
noncomputable def machine (k : ℕ) : BitMachine.Machine :=
  ofFinite (0 : Stack) (0 : Stack) BL.p1 ((none, ()) : Control) (program k)

theorem packet_eq (n : ℕ) (w : List Bool) :
    SourceOriginalBranchPackets.packet n w =
      EncodedCommunication.field (List.replicate n true) ++ EncodedCommunication.field w := by
  simp [SourceOriginalBranchPackets.packet, SourceOriginalBranchPackets.bank,
    BitMachineBankCodec.encode_eq_list, List.ofFn_succ]

theorem bank3_eq (w r t : List Bool) :
    BitMachineBankCodec.encode ![w, r, t] =
      EncodedCommunication.field w ++ (EncodedCommunication.field r ++
        (EncodedCommunication.field t ++ [])) := by
  simp [BitMachineBankCodec.encode_eq_list, List.ofFn_succ]

theorem machine_outputs (k n : ℕ) (w t : List Bool) :
    (machine k).OutputsWithin
      (EncodedComplexity.pair (SourceOriginalBranchPackets.packet n w) t)
      (BitMachineBankCodec.encode ![w, List.replicate k true, t])
      (10 * ((EncodedComplexity.pair (SourceOriginalBranchPackets.packet n w) t).length + 1)) := by
  set P := SourceOriginalBranchPackets.packet n w with hP
  set FW := EncodedCommunication.field w with hFW
  let S0 : Stack → List Bool := fun j => if j = 0 then EncodedComplexity.pair P t else []
  -- 1. parse the packet field
  have e1 := parse_loop (program k) (0 : Stack) 1 BL.p1 BL.p2 (by decide) rfl P t S0 none ()
    (by simp [S0, EncodedComplexity.pair])
  set S1 := Function.update (Function.update S0 1 (P.reverse ++ S0 1)) 0 t with hS1
  -- 2. restore the packet on stack 2
  have h1 : S1 1 = P.reverse := by simp [hS1, S0]
  have e2 := move_loop (program k) (1 : Stack) 2 BL.p2 BL.p3 (by decide) rfl P.reverse S1
    (some false) () h1
  rw [List.length_reverse] at e2
  set S2 := Function.update (Function.update S1 2 (P.reverse.reverse ++ S1 2)) 1 [] with hS2
  -- 3. discard the unary field
  have h2 : S2 2 = EncodedCommunication.field (List.replicate n true) ++ FW := by
    simp [hS2, hS1, S0, hP, hFW, packet_eq]
  have e3 := parse_loop (program k) (2 : Stack) 3 BL.p3 BL.p4 (by decide) rfl
    (List.replicate n true) FW S2 none () h2
  rw [List.length_replicate] at e3
  set S3 := Function.update (Function.update S2 3 ((List.replicate n true).reverse ++ S2 3))
    2 FW with hS3
  -- 4. reverse `t` onto temp
  have h3 : S3 0 = t := by simp [hS3, hS2, hS1, S0]
  have e4 := move_loop (program k) (0 : Stack) 1 BL.p4 BL.p5a (by decide) rfl t S3
    (some false) () h3
  set S4 := Function.update (Function.update S3 1 (t.reverse ++ S3 1)) 0 [] with hS4
  -- 5. write `field t`
  have e5 := pushFalse_step (program k) (0 : Stack) BL.p5a BL.p5 rfl (none, ()) S4
  set S5 := Function.update S4 0 (false :: S4 0) with hS5
  have h5 : S5 1 = t.reverse := by simp [hS5, hS4, hS3, hS2, hS1, S0]
  have e6 := emit_loop (program k) (1 : Stack) 0 BL.p5 BL.p6 (by decide) rfl t.reverse S5
    none () h5
  rw [List.length_reverse] at e6
  set S6 := Function.update (Function.update S5 0 (t.reverse.foldl emitFold (S5 0))) 1 []
    with hS6
  -- 6. write `field (1^k)`
  have e7 := unaryField_step (program k) (0 : Stack) k BL.p6 BL.p7 rfl (none, ()) S6
  set S7 := Function.update S6 0
    (EncodedCommunication.field (List.replicate k true) ++ S6 0) with hS7
  -- 7, 8. write `field w`
  have h7 : S7 2 = FW := by simp [hS7, hS6, hS5, hS4, hS3]
  have e8 := move_loop (program k) (2 : Stack) 1 BL.p7 BL.p8 (by decide) rfl FW S7 none () h7
  set S8 := Function.update (Function.update S7 1 (FW.reverse ++ S7 1)) 2 [] with hS8
  have h8 : S8 1 = FW.reverse := by simp [hS8, hS7, hS6]
  have e9 := move_loop (program k) (1 : Stack) 0 BL.p8 BL.done (by decide) rfl FW.reverse S8
    none () h8
  rw [List.length_reverse] at e9
  set S9 := Function.update (Function.update S8 0 (FW.reverse.reverse ++ S8 0)) 1 [] with hS9
  have e10 := halt_step (program k) BL.done rfl (none, ()) S9
  have h60 : S6 0 = EncodedCommunication.field t ++ [] := by
    have : S5 0 = false :: [] := by simp [hS5, hS4]
    simp only [hS6, Function.update_of_ne (by decide : (0 : Stack) ≠ 1), Function.update_self,
      this]
    exact emit_reverse_field t []
  have h9 : S9 0 = BitMachineBankCodec.encode ![w, List.replicate k true, t] := by
    rw [bank3_eq, ← hFW, ← h60]
    simp [hS9, hS8, hS7]
  -- chain
  have r := iter_chain (iter_chain (iter_chain (iter_chain (iter_chain (iter_chain
    (iter_chain (iter_chain (iter_chain e1 e2) e3) e4)
    (show (advance (program k))^[1] _ = _ from e5)) e6)
    (show (advance (program k))^[1] _ = _ from e7)) e8) e9)
    (show (advance (program k))^[1] _ = _ from e10)
  have hraw : rawInit (0 : Stack) BL.p1 ((none, ()) : Control)
      (EncodedComplexity.pair P t) = ⟨some BL.p1, (none, ()), S0⟩ := rfl
  have hPl := SourceOriginalBranchPackets.packet_length n w
  have hFl := EncodedCommunication.field_length w
  refine outputsWithin_of_raw_run (0 : Stack) (0 : Stack) BL.p1 ((none, ()) : Control)
    (program k) (EncodedComplexity.pair P t)
    (BitMachineBankCodec.encode ![w, List.replicate k true, t])
    (P.length + 1 + (P.length + 1) + (n + 1) + (t.length + 1) + 1 + (t.length + 1) + 1 +
      (FW.length + 1) + (FW.length + 1) + 1) _ ?_ ?_ ?_
  · rw [EncodedComplexity.pair_length]
    rw [← hP] at hPl
    rw [← hFW] at hFl
    omega
  · rw [hraw, r]
  · rw [hraw, r]
    exact h9

/-- **The bank assembler (generic glue contract `H_BankOut k`, literal body).** Does not
close a ledger row. -/
theorem bank_out (k : ℕ) :
    ∃ (MB : BitMachine.Machine) (CB EB : ℕ), ∀ (n : ℕ) (w t : List Bool),
      MB.OutputsWithin (EncodedComplexity.pair (SourceOriginalBranchPackets.packet n w) t)
        (BitMachineBankCodec.encode ![w, List.replicate k true, t])
        (CB * ((EncodedComplexity.pair (SourceOriginalBranchPackets.packet n w) t).length + 1)
          ^ EB) :=
  ⟨machine k, 10, 1, fun n w t => by
    simpa only [pow_one] using machine_outputs k n w t⟩

end Paper2.Unit4Shell.BankOut
