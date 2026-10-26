import Paper2.OutputSkipperLoops

/-! One-subtree correctness of the whole-Code output skipper.

`skip_one`: a `false` marker skips exactly one serialized subtree (no output).
`trav_one`: for every code of the admissible shape and every word the code
can actually produce, a `true` marker consumes exactly that word from the
front of the forward output and records it (reversed) on `used`.
Clocks: `8 * codeSize c` and `8 * codeSize c * (w.length + 1)`. -/

namespace Paper2.OutputSkipper

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineComposition
open GeneratorCode GeneratorSerialization
open RecursiveRequestCodeShape

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- Scanner-ready configuration: all header cells and peek empty. -/
def ready (h0 P O U : List Bool) : Config :=
  ⟨some (.inr .check), ctl0, bk h0 [] [] [] [] [] [] P O U []⟩

def postHeader (c : Code) (rest : List Bool) (m : Bool) (P O U : List Bool) : Config :=
  ⟨some (.inr .after), ((none, some (CodeHeaderMachine.headerKind c)), (none, (some m, 0))),
    bk (CodeHeaderMachine.headerTail c rest) (CodeHeaderMachine.headerN c)
      (CodeHeaderMachine.headerA c) (CodeHeaderMachine.headerB c) []
      (CodeHeaderMachine.headerWord c) [] P O U []⟩

theorem node_prefix (c : Code) (rest : List Bool) (m : Bool) (P O U : List Bool) :
    ∃ t ≤ 1 + CodeHeaderMachine.headerCost c,
      run t (ready (encodeCode c ++ rest) (m :: P) O U) = postHeader c rest m P O U := by
  obtain ⟨t, ht, hr⟩ := header_run c rest P O U [] (none, (some m, 0))
  refine ⟨1 + t, by omega, ?_⟩
  rw [run_add, run_one, ready, check_cons]
  exact hr

/-! ### The dispatch step after the header -/

section After
variable (rest P O U : List Bool)

theorem after_skip_emit (bits : List Bool) :
    advance program (postHeader (.emit bits) rest false P O U) =
      ⟨some (.inr (.clear 0)), ((none, some .emit), (none, (some false, 0))),
        bk rest (List.replicate bits.length true) [] [] [] bits [] P O U []⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, goClear, postHeader,
    CodeHeaderMachine.headerKind, CodeHeaderMachine.headerTail, CodeHeaderMachine.headerN,
    CodeHeaderMachine.headerA, CodeHeaderMachine.headerB, CodeHeaderMachine.headerWord]

theorem after_skip_ticket (n : Nat) :
    advance program (postHeader (.ticket n) rest false P O U) =
      ⟨some (.inr (.clear 0)), ((none, some .ticket), (none, (some false, 0))),
        bk rest (List.replicate n true) [] [] [] [] [] P O U []⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, goClear, postHeader,
    CodeHeaderMachine.headerKind, CodeHeaderMachine.headerTail, CodeHeaderMachine.headerN,
    CodeHeaderMachine.headerA, CodeHeaderMachine.headerB, CodeHeaderMachine.headerWord]

theorem after_skip_bit :
    advance program (postHeader .bit rest false P O U) =
      ⟨some (.inr (.clear 0)), ((none, some .bit), (none, (some false, 0))),
        bk rest [] [] [] [] [] [] P O U []⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, goClear, postHeader,
    CodeHeaderMachine.headerKind, CodeHeaderMachine.headerTail, CodeHeaderMachine.headerN,
    CodeHeaderMachine.headerA, CodeHeaderMachine.headerB, CodeHeaderMachine.headerWord]

theorem after_skip_append (a b : Code) :
    advance program (postHeader (.append a b) rest false P O U) =
      ⟨some (.inr (.clear 0)), ((none, some .append), (none, (some false, 0))),
        bk (encodeCode a ++ encodeCode b ++ rest) [] [] [] [] [] []
          (false :: false :: P) O U []⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, goClear, postHeader,
    CodeHeaderMachine.headerKind, CodeHeaderMachine.headerTail, CodeHeaderMachine.headerN,
    CodeHeaderMachine.headerA, CodeHeaderMachine.headerB, CodeHeaderMachine.headerWord]

theorem after_skip_branch (n a b : Nat) (f s t : Code) :
    advance program (postHeader (.branch3 n a b f s t) rest false P O U) =
      ⟨some (.inr (.clear 0)), ((none, some .branch3), (none, (some false, 0))),
        bk (encodeCode f ++ encodeCode s ++ encodeCode t ++ rest)
          (List.replicate n true) (List.replicate a true) (List.replicate b true) [] [] []
          (false :: false :: false :: P) O U []⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, goClear, postHeader,
    CodeHeaderMachine.headerKind, CodeHeaderMachine.headerTail, CodeHeaderMachine.headerN,
    CodeHeaderMachine.headerA, CodeHeaderMachine.headerB, CodeHeaderMachine.headerWord]

theorem after_trav_emit (bits : List Bool) :
    advance program (postHeader (.emit bits) rest true P O U) =
      ⟨some (.inr .emitNext), ((none, some .emit), (none, (some true, 0))),
        bk rest (List.replicate bits.length true) [] [] [] bits [] P O U []⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, postHeader,
    CodeHeaderMachine.headerKind, CodeHeaderMachine.headerTail, CodeHeaderMachine.headerN,
    CodeHeaderMachine.headerA, CodeHeaderMachine.headerB, CodeHeaderMachine.headerWord]

theorem after_trav_ticket (n : Nat) :
    advance program (postHeader (.ticket n) rest true P O U) =
      ⟨some (.inr .ticketCheck), ((none, some .ticket), (none, (some true, 0))),
        bk rest (List.replicate n true) [] [] [] [] [] P O U []⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, postHeader,
    CodeHeaderMachine.headerKind, CodeHeaderMachine.headerTail, CodeHeaderMachine.headerN,
    CodeHeaderMachine.headerA, CodeHeaderMachine.headerB, CodeHeaderMachine.headerWord]

theorem after_trav_bit :
    advance program (postHeader .bit rest true P O U) =
      ⟨some (.inr .bitTake), ((none, some .bit), (none, (some true, 0))),
        bk rest [] [] [] [] [] [] P O U []⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, postHeader,
    CodeHeaderMachine.headerKind, CodeHeaderMachine.headerTail, CodeHeaderMachine.headerN,
    CodeHeaderMachine.headerA, CodeHeaderMachine.headerB, CodeHeaderMachine.headerWord]

theorem after_trav_append (a b : Code) :
    advance program (postHeader (.append a b) rest true P O U) =
      ⟨some (.inr (.clear 0)), ((none, some .append), (none, (some true, 0))),
        bk (encodeCode a ++ encodeCode b ++ rest) [] [] [] [] [] []
          (true :: true :: P) O U []⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, goClear, postHeader,
    CodeHeaderMachine.headerKind, CodeHeaderMachine.headerTail, CodeHeaderMachine.headerN,
    CodeHeaderMachine.headerA, CodeHeaderMachine.headerB, CodeHeaderMachine.headerWord]

theorem after_trav_branch (n a b : Nat) (f s t : Code) :
    advance program (postHeader (.branch3 n a b f s t) rest true P O U) =
      ⟨some (.inr .branchStart), ((none, some .branch3), (none, (some true, 0))),
        bk (encodeCode f ++ encodeCode s ++ encodeCode t ++ rest)
          (List.replicate n true) (List.replicate a true) (List.replicate b true) [] [] []
          P O U []⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, postHeader,
    CodeHeaderMachine.headerKind, CodeHeaderMachine.headerTail, CodeHeaderMachine.headerN,
    CodeHeaderMachine.headerA, CodeHeaderMachine.headerB, CodeHeaderMachine.headerWord]

end After

#print axioms node_prefix
#print axioms after_trav_branch

end Paper2.OutputSkipper
