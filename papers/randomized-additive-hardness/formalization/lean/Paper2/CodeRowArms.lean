import Paper2.GeneratorSource
import Paper2.GeneratorSerialization
import Paper2.CodeAtomCountInput
import Paper2.CodeConstructorMachine
import Mathlib.Tactic

/-! A direct fixed-controller serialization of the two non-template graph-row
arms. It reuses their exact syntax/byte definitions, but specializes the
physical copy phases rather than inlining the frozen constructor programs. -/

namespace Paper2.CodeRowArms

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorSource

abbrev Stack := Fin 7
abbrev Control := Option Bool

inductive Label where
  | childCopy | childRestore | nDelim | nCopy | nRestore | nTicket
  | subCopy | subRestore | subTicket | mid
  | fourCopy | fourRestore | finalHeader | accept
  deriving DecidableEq, Fintype

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def sourceSlot (i : Fin 4) : Stack := ⟨i.val, by omega⟩

def contents (words : Fin 4 → List Bool) (vertex auxiliary scratch : List Bool) :
    Stack → List Bool :=
  fun i => if h : i.val < 4 then words ⟨i.val, h⟩ else
    if i = 4 then vertex else if i = 5 then auxiliary else scratch

def cfg (l : Option Label) (v : Control) (words : Fin 4 → List Bool)
    (vertex auxiliary scratch : List Bool) : Config :=
  ⟨l, v, contents words vertex auxiliary scratch⟩

def copyStmt (src : Fin 4) (copy restore : Label) :
    TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  pop (sourceSlot src) (fun _ b => b)
    (branch Option.isSome
      (push 6 (fun b => b.getD false) (goto (fun _ => copy)))
      (goto (fun _ => restore)))

def restoreStmt (src : Fin 4) (toVertex toAuxiliary : Bool)
    (restore next : Label) :
    TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  pop 6 (fun _ b => b)
    (branch Option.isSome
      (push (sourceSlot src) (fun b => b.getD false)
        (if toVertex then
          push 4 (fun b => b.getD false)
            (if toAuxiliary then push 5 (fun b => b.getD false)
              (goto (fun _ => restore)) else goto (fun _ => restore))
         else if toAuxiliary then push 5 (fun b => b.getD false)
              (goto (fun _ => restore)) else goto (fun _ => restore)))
      (goto (fun _ => next)))

def appendHeader : List Bool := [false,true,true]
def ticketHeader : List Bool := [false,false,true]
def emitTrue : List Bool := encodeCode (.emit [true])
def emitFalse : List Bool := encodeCode (.emit [false])

def pushWord (dst : Stack) : List Bool →
    TM2.Stmt (fun _ : Stack => Bool) Label Control →
    TM2.Stmt (fun _ : Stack => Bool) Label Control
  | [], q => q
  | b :: bs, q => push dst (fun _ => b) (pushWord dst bs q)

def prepend (dst : Stack) (word : List Bool)
    (next : Label) : TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  pushWord dst word.reverse (goto (fun _ => next))

private theorem stepAux_pushWord (dst : Stack) (bits : List Bool)
    (q : TM2.Stmt (fun _ : Stack => Bool) Label Control)
    (control : Control) (S : Stack → List Bool) :
    TM2.stepAux (pushWord dst bits q) control S =
      TM2.stepAux q control
        (Function.update S dst (bits.reverse ++ S dst)) := by
  induction bits generalizing S with
  | nil => simp [pushWord, Function.update_eq_self]
  | cons bit bits ih =>
      simp only [pushWord, TM2.stepAux, ih, List.reverse_cons,
        List.append_assoc, List.singleton_append]
      congr 1
      funext i
      by_cases h : i = dst <;> simp [Function.update, h]

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .childCopy => copyStmt 3 .childCopy .childRestore
  | .childRestore => restoreStmt 3 true true .childRestore .nDelim
  | .nDelim => push 4 (fun _ => false) (goto (fun _ => .nCopy))
  | .nCopy => copyStmt 0 .nCopy .nRestore
  | .nRestore => restoreStmt 0 true false .nRestore .nTicket
  | .nTicket => prepend 4 ticketHeader .subCopy
  | .subCopy => copyStmt 2 .subCopy .subRestore
  | .subRestore => restoreStmt 2 false true .subRestore .subTicket
  | .subTicket => prepend 5 ticketHeader .mid
  | .mid => pushWord 4 (appendHeader ++ emitFalse).reverse
      (prepend 5 (appendHeader ++ emitTrue) .fourCopy)
  | .fourCopy => copyStmt 1 .fourCopy .fourRestore
  | .fourRestore => restoreStmt 1 true true .fourRestore .finalHeader
  | .finalHeader => pushWord 4
      (appendHeader ++ emitTrue ++ appendHeader ++ appendHeader ++ ticketHeader).reverse
      (prepend 5
        (appendHeader ++ emitTrue ++ appendHeader ++ appendHeader ++ ticketHeader)
        .accept)
  | .accept => halt

def run (steps : Nat) (c : Config) := ((advance program)^[steps]) c

private theorem run_add (a b : Nat) (c : Config) :
    run (a+b) c = run b (run a c) := by
  simpa only [run, Nat.add_comm] using Function.iterate_add_apply (advance program) b a c

private theorem update_twice (words : Fin 4 → List Bool) (src : Fin 4)
    (x y : List Bool) :
    Function.update (Function.update words src x) src y =
      Function.update words src y := by
  funext i
  by_cases h : i = src <;> simp [Function.update, h]

private theorem step_copy_cons (src : Fin 4) (copy restore : Label)
    (hp : program copy = copyStmt src copy restore)
    (bit : Bool) (control : Control) (words : Fin 4 → List Bool)
    (vertex auxiliary scratch rest : List Bool) :
    advance program
      (cfg (some copy) control (Function.update words src (bit :: rest))
        vertex auxiliary scratch) =
      cfg (some copy) (some bit) (Function.update words src rest)
        vertex auxiliary (bit :: scratch) := by
  fin_cases src <;>
    simp [advance, TM2.step, TM2.stepAux, hp, copyStmt,
      cfg, contents, sourceSlot, Function.update] <;>
    (funext i; fin_cases i <;> simp [contents, Function.update])

private theorem step_copy_nil (src : Fin 4) (copy restore : Label)
    (hp : program copy = copyStmt src copy restore)
    (control : Control) (words : Fin 4 → List Bool)
    (vertex auxiliary scratch : List Bool) :
    advance program
      (cfg (some copy) control (Function.update words src [])
        vertex auxiliary scratch) =
      cfg (some restore) none (Function.update words src [])
        vertex auxiliary scratch := by
  fin_cases src <;>
    simp [advance, TM2.step, TM2.stepAux, hp, copyStmt,
      cfg, contents, sourceSlot, Function.update]

private theorem step_restore_cons (src : Fin 4) (toV toA : Bool)
    (restore next : Label)
    (hp : program restore = restoreStmt src toV toA restore next)
    (bit : Bool) (control : Control) (words : Fin 4 → List Bool)
    (vertex auxiliary scratch : List Bool) :
    advance program
      (cfg (some restore) control words vertex auxiliary (bit :: scratch)) =
      cfg (some restore) (some bit)
        (Function.update words src (bit :: words src))
        (if toV then bit :: vertex else vertex)
        (if toA then bit :: auxiliary else auxiliary) scratch := by
  cases toV <;> cases toA <;> fin_cases src <;>
    simp [advance, TM2.step, TM2.stepAux, hp, restoreStmt,
      cfg, contents, sourceSlot, Function.update] <;>
    (funext i; fin_cases i <;> simp [contents, Function.update])

private theorem step_restore_nil (src : Fin 4) (toV toA : Bool)
    (restore next : Label)
    (hp : program restore = restoreStmt src toV toA restore next)
    (control : Control) (words : Fin 4 → List Bool)
    (vertex auxiliary : List Bool) :
    advance program (cfg (some restore) control words vertex auxiliary []) =
      cfg (some next) none words vertex auxiliary [] := by
  simp [advance, TM2.step, TM2.stepAux, hp, restoreStmt, cfg, contents]

private theorem run_copy (src : Fin 4) (copy restore : Label)
    (hp : program copy = copyStmt src copy restore)
    (bits : List Bool) (control : Control) (words : Fin 4 → List Bool)
    (vertex auxiliary scratch : List Bool) :
    run (bits.length+1)
      (cfg (some copy) control (Function.update words src bits)
        vertex auxiliary scratch) =
      cfg (some restore) none (Function.update words src [])
        vertex auxiliary (bits.reverse ++ scratch) := by
  induction bits generalizing words scratch control with
  | nil =>
      simpa only [List.length_nil, zero_add, List.reverse_nil, List.nil_append]
        using step_copy_nil src copy restore hp control words vertex auxiliary scratch
  | cons bit bits ih =>
      have hstep := step_copy_cons src copy restore hp bit control
        (Function.update words src bits) vertex auxiliary scratch bits
      simp only [update_twice] at hstep
      rw [show (bit :: bits).length+1 = 1+(bits.length+1) by simp; omega,
        run_add 1 (bits.length+1)]
      change run (bits.length+1)
        (advance program (cfg (some copy) control
          (Function.update words src (bit :: bits)) vertex auxiliary scratch)) = _
      rw [hstep]
      simpa [update_twice, List.reverse_cons, List.append_assoc] using
        ih (some bit) (Function.update words src bits) (bit :: scratch)

private theorem run_restore (src : Fin 4) (toV toA : Bool)
    (restore next : Label)
    (hp : program restore = restoreStmt src toV toA restore next)
    (bits : List Bool) (control : Control) (words : Fin 4 → List Bool)
    (vertex auxiliary : List Bool) :
    run (bits.length+1)
      (cfg (some restore) control words vertex auxiliary bits) =
      cfg (some next) none
        (Function.update words src (bits.reverse ++ words src))
        (if toV then bits.reverse ++ vertex else vertex)
        (if toA then bits.reverse ++ auxiliary else auxiliary) [] := by
  induction bits generalizing control words vertex auxiliary with
  | nil =>
      simpa only [List.length_nil, zero_add, List.reverse_nil, List.nil_append,
        Function.update_eq_self, ite_self] using
        step_restore_nil src toV toA restore next hp control words vertex auxiliary
  | cons bit bits ih =>
      rw [show (bit :: bits).length+1 = 1+(bits.length+1) by simp; omega,
        run_add 1 (bits.length+1)]
      change run (bits.length+1)
        (advance program (cfg (some restore) control words vertex auxiliary
          (bit :: bits))) = _
      rw [step_restore_cons src toV toA restore next hp bit control
        words vertex auxiliary bits]
      have h := ih (some bit) (Function.update words src (bit :: words src))
        (if toV then bit :: vertex else vertex)
        (if toA then bit :: auxiliary else auxiliary)
      cases toV <;> cases toA <;>
        simpa [update_twice, List.reverse_cons, List.append_assoc] using h

theorem run_phase (src : Fin 4) (toV toA : Bool)
    (copy restore next : Label)
    (hc : program copy = copyStmt src copy restore)
    (hr : program restore = restoreStmt src toV toA restore next)
    (words : Fin 4 → List Bool) (vertex auxiliary : List Bool) :
    run (2*(words src).length+2)
      (cfg (some copy) none words vertex auxiliary []) =
      cfg (some next) none words
        (if toV then words src ++ vertex else vertex)
        (if toA then words src ++ auxiliary else auxiliary) [] := by
  have hcopy := run_copy src copy restore hc (words src) none words
    vertex auxiliary []
  have hrestore := run_restore src toV toA restore next hr
    (words src).reverse none (Function.update words src []) vertex auxiliary
  simp only [Function.update_eq_self] at hcopy
  rw [show 2*(words src).length+2 =
      ((words src).length+1)+((words src).length+1) by omega,
    run_add, hcopy]
  simpa [List.length_reverse, List.reverse_reverse, List.append_nil,
    Function.update_self, update_twice, Function.update_eq_self] using hrestore

def initial (n s : Nat) (c : Code) : Config :=
  cfg (some .childCopy) none
    ![List.replicate n true, unary (4*s), unary (s-3), encodeCode c] [] [] []

def vertexArm (n s : Nat) (c : Code) : Code :=
  .append (.emit [true]) (.append (vertexLabelsCode (V := Fin n) s) c)

def auxiliaryArm (s : Nat) (c : Code) : Code :=
  .append (.emit [true]) (.append (auxiliaryLabelsCode s) c)

def final (n s : Nat) (c : Code) : Config :=
  cfg none none
    ![List.replicate n true, unary (4*s), unary (s-3), encodeCode c]
    (encodeCode (vertexArm n s c)) (encodeCode (auxiliaryArm s c)) []

def clock (n s : Nat) (c : Code) : Nat :=
  2 * ((encodeCode c).length + n + (unary (s-3)).length +
    (unary (4*s)).length) + 14

private theorem step_nDelim (w : Fin 4 → List Bool) (v a : List Bool) :
    advance program (cfg (some .nDelim) none w v a []) =
      cfg (some .nCopy) none w (false :: v) a [] := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, contents]
  funext i; fin_cases i <;> simp [contents]

private theorem step_nTicket (w : Fin 4 → List Bool) (v a : List Bool) :
    advance program (cfg (some .nTicket) none w v a []) =
      cfg (some .subCopy) none w (ticketHeader ++ v) a [] := by
  simp [advance, TM2.step, TM2.stepAux, program, prepend, stepAux_pushWord,
    ticketHeader, cfg, contents]
  funext i; fin_cases i <;> simp [contents]

private theorem step_subTicket (w : Fin 4 → List Bool) (v a : List Bool) :
    advance program (cfg (some .subTicket) none w v a []) =
      cfg (some .mid) none w v (ticketHeader ++ a) [] := by
  simp [advance, TM2.step, TM2.stepAux, program, prepend, stepAux_pushWord,
    ticketHeader, cfg, contents]
  funext i; fin_cases i <;> simp [contents]

private theorem step_mid (w : Fin 4 → List Bool) (v a : List Bool) :
    advance program (cfg (some .mid) none w v a []) =
      cfg (some .fourCopy) none w
        ((appendHeader ++ emitFalse) ++ v)
        ((appendHeader ++ emitTrue) ++ a) [] := by
  simp [advance, TM2.step, TM2.stepAux, program, prepend, stepAux_pushWord,
    appendHeader, emitFalse, emitTrue, encodeCode, unary, cfg, contents]
  funext i; fin_cases i <;> simp [contents]

private theorem step_finalHeader (w : Fin 4 → List Bool) (v a : List Bool) :
    advance program (cfg (some .finalHeader) none w v a []) =
      cfg (some .accept) none w
        ((appendHeader ++ emitTrue ++ appendHeader ++ appendHeader ++ ticketHeader) ++ v)
        ((appendHeader ++ emitTrue ++ appendHeader ++ appendHeader ++ ticketHeader) ++ a) [] := by
  simp [advance, TM2.step, TM2.stepAux, program, prepend, stepAux_pushWord,
    appendHeader, ticketHeader, emitTrue, encodeCode, unary, cfg, contents]
  funext i; fin_cases i <;> simp [contents]

private theorem step_accept (w : Fin 4 → List Bool) (v a : List Bool) :
    advance program (cfg (some .accept) none w v a []) =
      cfg none none w v a [] := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]

def wordsClock (w : Fin 4 → List Bool) : Nat :=
  2 * ((w 3).length + (w 0).length + (w 2).length + (w 1).length) + 14

private theorem run_one (c : Config) : run 1 c = advance program c := rfl

theorem run_words (w : Fin 4 → List Bool) :
    run (wordsClock w) (cfg (some .childCopy) none w [] [] []) =
      cfg none none w
        ((appendHeader ++ emitTrue ++ appendHeader ++ appendHeader ++ ticketHeader) ++
          (w 1) ++ (appendHeader ++ emitFalse) ++ ticketHeader ++
          (w 0) ++ [false] ++ (w 3))
        ((appendHeader ++ emitTrue ++ appendHeader ++ appendHeader ++ ticketHeader) ++
          (w 1) ++ (appendHeader ++ emitTrue) ++ ticketHeader ++
          (w 2) ++ (w 3)) [] := by
  have hc := run_phase 3 true true .childCopy .childRestore .nDelim
    rfl rfl w [] []
  have hn := run_phase 0 true false .nCopy .nRestore .nTicket
    rfl rfl w (false :: w 3) (w 3)
  have hs := run_phase 2 false true .subCopy .subRestore .subTicket
    rfl rfl w (ticketHeader ++ w 0 ++ [false] ++ w 3) (w 3)
  have hf := run_phase 1 true true .fourCopy .fourRestore .finalHeader
    rfl rfl w
    ((appendHeader ++ emitFalse) ++ ticketHeader ++ w 0 ++ [false] ++ w 3)
    ((appendHeader ++ emitTrue) ++ ticketHeader ++ w 2 ++ w 3)
  calc
    run (wordsClock w) (cfg (some .childCopy) none w [] [] []) =
        run ((2*(w 3).length+2) +
          (1 + ((2*(w 0).length+2) +
          (1 + ((2*(w 2).length+2) +
          (1 + (1 + ((2*(w 1).length+2) + (1+1)))))))))
          (cfg (some .childCopy) none w [] [] []) := by
            congr 1; simp [wordsClock]; omega
    _ = run (1 + ((2*(w 0).length+2) +
          (1 + ((2*(w 2).length+2) +
          (1 + (1 + ((2*(w 1).length+2) + (1+1))))))))
          (cfg (some .nDelim) none w (w 3) (w 3) []) := by
            rw [run_add, hc]; simp
    _ = run ((2*(w 0).length+2) +
          (1 + ((2*(w 2).length+2) +
          (1 + (1 + ((2*(w 1).length+2) + (1+1)))))))
          (cfg (some .nCopy) none w (false :: w 3) (w 3) []) := by
            rw [run_add, run_one, step_nDelim]
    _ = run (1 + ((2*(w 2).length+2) +
          (1 + (1 + ((2*(w 1).length+2) + (1+1))))))
          (cfg (some .nTicket) none w (w 0 ++ [false] ++ w 3) (w 3) []) := by
            rw [run_add, hn]; simp [List.append_assoc]
    _ = run ((2*(w 2).length+2) +
          (1 + (1 + ((2*(w 1).length+2) + (1+1)))))
          (cfg (some .subCopy) none w
            (ticketHeader ++ w 0 ++ [false] ++ w 3) (w 3) []) := by
            rw [run_add, run_one, step_nTicket]; simp [List.append_assoc]
    _ = run (1 + (1 + ((2*(w 1).length+2) + (1+1))))
          (cfg (some .subTicket) none w
            (ticketHeader ++ w 0 ++ [false] ++ w 3) (w 2 ++ w 3) []) := by
            rw [run_add, hs]; simp [List.append_assoc]
    _ = run (1 + ((2*(w 1).length+2) + (1+1)))
          (cfg (some .mid) none w
            (ticketHeader ++ w 0 ++ [false] ++ w 3)
            (ticketHeader ++ w 2 ++ w 3) []) := by
            rw [run_add, run_one, step_subTicket]; simp [List.append_assoc]
    _ = run ((2*(w 1).length+2) + (1+1))
          (cfg (some .fourCopy) none w
            ((appendHeader ++ emitFalse) ++ ticketHeader ++ w 0 ++ [false] ++ w 3)
            ((appendHeader ++ emitTrue) ++ ticketHeader ++ w 2 ++ w 3) []) := by
            rw [run_add 1, run_one, step_mid]
            simp [List.append_assoc]
    _ = run (1+1)
          (cfg (some .finalHeader) none w
            (w 1 ++ (appendHeader ++ emitFalse) ++ ticketHeader ++ w 0 ++ [false] ++ w 3)
            (w 1 ++ (appendHeader ++ emitTrue) ++ ticketHeader ++ w 2 ++ w 3) []) := by
            rw [run_add, hf]; simp [List.append_assoc]
    _ = run 1
          (cfg (some .accept) none w
            ((appendHeader ++ emitTrue ++ appendHeader ++ appendHeader ++ ticketHeader) ++
              w 1 ++ (appendHeader ++ emitFalse) ++ ticketHeader ++ w 0 ++ [false] ++ w 3)
            ((appendHeader ++ emitTrue ++ appendHeader ++ appendHeader ++ ticketHeader) ++
              w 1 ++ (appendHeader ++ emitTrue) ++ ticketHeader ++ w 2 ++ w 3) []) := by
            rw [run_add 1 1]
            change run 1 (advance program (cfg (some .finalHeader) none w
              (w 1 ++ (appendHeader ++ emitFalse) ++ ticketHeader ++ w 0 ++ [false] ++ w 3)
              (w 1 ++ (appendHeader ++ emitTrue) ++ ticketHeader ++ w 2 ++ w 3) [])) = _
            rw [step_finalHeader]
            simp [List.append_assoc]
    _ = _ := by rw [run_one, step_accept]

theorem run_exact (n s : Nat) (c : Code) :
    run (clock n s c) (initial n s c) = final n s c := by
  have h := run_words
    (![List.replicate n true, unary (4*s), unary (s-3), encodeCode c] :
      Fin 4 → List Bool)
  have ht : clock n s c =
      wordsClock (![List.replicate n true, unary (4*s), unary (s-3), encodeCode c] :
        Fin 4 → List Bool) := by
    simp [clock, wordsClock]
  rw [ht]
  simpa [initial, final, vertexArm, auxiliaryArm, vertexLabelsCode,
    auxiliaryLabelsCode, appendHeader, ticketHeader, emitTrue, emitFalse,
    encodeCode, unary, List.append_assoc] using h

#print axioms run_exact

end Paper2.CodeRowArms
