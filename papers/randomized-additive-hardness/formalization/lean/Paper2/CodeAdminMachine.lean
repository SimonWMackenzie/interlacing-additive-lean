import Paper2.CodeScanner

namespace Paper2.CodeAdminMachine

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineComposition
open GeneratorCode GeneratorSerialization
open scoped BigOperators

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

abbrev Stack := CodeScanner.Stack
inductive Admin where
  | start | dispatch | emit | clear (i : Fin 7)
  deriving DecidableEq, Fintype
abbrev Label := CodeHeaderMachine.Label ⊕ Admin
abbrev Control := CodeHeaderMachine.Control × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some Admin.dispatch) (CodeHeaderMachine.program l)
  | .inr .start => pop (.inl 0) (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (push (.inl 0) (fun v => v.2.getD false)
          (load (fun _ => ((none,none),none)) (goto (fun _ => .inl .first))))
        (load (fun _ => ((none,none),none)) halt))
  | .inr .dispatch => branch (fun v => decide (v.1.2 = some .emit))
      (load (fun _ => ((none,none),none)) (goto (fun _ => .inr .emit)))
      (branch (fun v => decide (v.1.2 = some .append))
        (load (fun _ => ((none,none),none)) (goto (fun _ => .inr (.clear 0)))) halt)
  | .inr .emit => pop (.inl 5) (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (push (.inr 0) (fun v => v.2.getD false) (goto (fun _ => .inr .emit)))
        (load (fun _ => ((none,none),none)) (goto (fun _ => .inr (.clear 0)))))
  | .inr (.clear i) => if h : i.val < 6 then
      BitMachineClearBank.clearStep (.inl ⟨i.val+1, by omega⟩)
        (.inr (.clear i)) (.inr (.clear ⟨i.val+1, by omega⟩))
    else BitMachineClearBank.finishStep (fun _ => (none,none)) (.inr .start)

def cfg (l : Option Label) (v : Control)
    (input n a b work literal used output : List Bool) : Config :=
  ⟨l,v,CodeScanner.bank (CodeHeaderMachine.contents input n a b work literal used) output⟩

def ready (input output : List Bool) : Config :=
  cfg (some (.inr .start)) ((none,none),none) input [] [] [] [] [] [] output

theorem header_run (c : Code) (rest output : List Bool) :
    ∃ t ≤ CodeHeaderMachine.headerCost c,
      ((advance program)^[t])
        (cfg (some (.inl .first)) ((none,none),none)
          (encodeCode c ++ rest) [] [] [] [] [] [] output) =
        cfg (some (.inr .dispatch)) ((none,some (CodeHeaderMachine.headerKind c)),none)
          (CodeHeaderMachine.headerTail c rest)
          (CodeHeaderMachine.headerN c) (CodeHeaderMachine.headerA c)
          (CodeHeaderMachine.headerB c) [] (CodeHeaderMachine.headerWord c) [] output := by
  have hh := CodeHeaderMachine.run_header c rest
  have hhalt : (((advance CodeHeaderMachine.program)^[CodeHeaderMachine.headerCost c])
      (CodeHeaderMachine.initial (encodeCode c ++ rest))).l = none := by
    rw [← CodeHeaderMachine.run, hh]; rfl
  obtain ⟨t, ht, hr⟩ := BitMachineSubroutine.lift_outputs
    CodeHeaderMachine.program program (some Admin.dispatch) (by intro l; rfl)
    (none : Option Bool) (fun _ : Fin 1 => output)
    (CodeHeaderMachine.initial (encodeCode c ++ rest))
    (CodeHeaderMachine.headerCost c) hhalt
  refine ⟨t,ht,?_⟩
  change ((advance program)^[t]) _ =
    liftCfg (some Admin.dispatch) (none : Option Bool) (fun _ : Fin 1 => output)
      (CodeHeaderMachine.run (CodeHeaderMachine.headerCost c)
        (CodeHeaderMachine.initial (encodeCode c ++ rest))) at hr
  rw [hh] at hr
  simpa only [liftCfg, CodeHeaderMachine.initial, CodeHeaderMachine.cfg,
    cfg, CodeScanner.bank] using hr

theorem emit_step (v : Control) (S : Stack → List Bool)
    (bit : Bool) (tail : List Bool) (hb : S (.inl 5) = bit :: tail) :
    advance program ⟨some (.inr .emit),v,S⟩ =
      (⟨some (.inr .emit),(v.1,some bit),
        Function.update (Function.update S (.inl 5) tail)
          (.inr 0) (bit :: S (.inr 0))⟩ : Config) := by
  simp only [advance, TM2.step, program, TM2.stepAux, hb, List.head?_cons,
    List.tail_cons, Option.isSome_some, Option.getD_some,
    Function.update_of_ne (show (Sum.inr (0 : Fin 1) : Stack) ≠ .inl 5 by decide)]
  rfl

theorem emit_bank (bit : Bool) (input n a b work literal used output : List Bool) :
    Function.update (Function.update
      (CodeScanner.bank (CodeHeaderMachine.contents input n a b work (bit::literal) used) output)
      (.inl 5) literal) (.inr 0) (bit::output) =
    CodeScanner.bank (CodeHeaderMachine.contents input n a b work literal used) (bit::output) := by
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem emit_nil (last : Option Bool) (input n a b work used output : List Bool) :
    advance program (cfg (some (.inr .emit)) ((none,none),last)
      input n a b work [] used output) =
    cfg (some (.inr (.clear 0))) ((none,none),none)
      input n a b work [] used output := by
  change (⟨some (.inr (.clear 0)),((none,none),none),
    Function.update (CodeScanner.bank
      (CodeHeaderMachine.contents input n a b work [] used) output) (.inl 5) []⟩ : Config) = _
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem emit_run (literal : List Bool) (last : Option Bool)
    (input n a b work used output : List Bool) :
    ((advance program)^[literal.length+1])
      (cfg (some (.inr .emit)) ((none,none),last)
        input n a b work literal used output) =
      cfg (some (.inr (.clear 0))) ((none,none),none)
        input n a b work [] used (literal.reverse ++ output) := by
  induction literal generalizing last output with
  | nil => simpa using emit_nil last input n a b work used output
  | cons bit tail ih =>
      have hs := emit_step ((none,none),last)
        (CodeScanner.bank (CodeHeaderMachine.contents input n a b work (bit::tail) used) output)
        bit tail rfl
      have hv : CodeScanner.bank
          (CodeHeaderMachine.contents input n a b work (bit::tail) used) output (.inr 0) = output := rfl
      rw [hv, emit_bank] at hs
      rw [List.length_cons, Function.iterate_succ_apply]
      change ((advance program)^[tail.length+1]) (advance program _) = _
      rw [show advance program (cfg (some (.inr .emit)) ((none,none),last)
          input n a b work (bit::tail) used output) =
          cfg (some (.inr .emit)) ((none,none),some bit)
            input n a b work tail used (bit::output) from hs]
      simpa [List.reverse_cons, List.append_assoc] using ih (some bit) (bit::output)

theorem cleared_basic (input n a b output : List Bool) :
    BitMachineClearBank.cleared CodeScanner.clearBank
      (CodeScanner.bank (CodeHeaderMachine.contents input n a b [] [] []) output) =
      CodeScanner.blank input output := by
  funext k
  cases k with
  | inr k =>
      rw [BitMachineClearBank.cleared_foreign]
      · rfl
      · intro i; simp [CodeScanner.clearBank]
  | inl k =>
      refine Fin.cases ?_ (fun i => ?_) k
      · rw [BitMachineClearBank.cleared_foreign]
        · rfl
        · intro i h
          have hv := congrArg (fun k : Stack => match k with | .inl k => k.val | .inr _ => 0) h
          simp only [CodeScanner.clearBank] at hv
          omega
      · change BitMachineClearBank.cleared CodeScanner.clearBank _
          (CodeScanner.clearBank i) = _
        rw [BitMachineClearBank.cleared_bank]
        fin_cases i <;> rfl

theorem clear_run (input n a b output : List Bool) :
    ((advance program)^[n.length+a.length+b.length+7])
      (cfg (some (.inr (.clear 0))) ((none,none),none)
        input n a b [] [] [] output) = ready input output := by
  have hsteps : ∀ i : Fin 6, program (.inr (.clear i.castSucc)) =
      BitMachineClearBank.clearStep (CodeScanner.clearBank i)
        (.inr (.clear i.castSucc)) (.inr (.clear i.succ)) := by
    intro i
    simp only [program, Fin.val_castSucc, i.isLt, dite_true, CodeScanner.clearBank]
    rfl
  have hf : program (.inr (.clear (Fin.last 6))) =
      BitMachineClearBank.finishStep (fun _ => (none,none)) (.inr .start) := rfl
  let S := CodeScanner.bank (CodeHeaderMachine.contents input n a b [] [] []) output
  have hr := BitMachineClearBank.clear_bank_run program
    (fun _ => (none,none)) (.inr .start) 6 CodeScanner.clearBank
    CodeScanner.clearBank_injective (fun i => .inr (.clear i)) hsteps hf (none,none) S
  have hc : (∑ i : Fin 6, (S (CodeScanner.clearBank i)).length) + 6 + 1 =
      n.length+a.length+b.length+7 := by
    simp [S, Fin.sum_univ_succ, CodeScanner.clearBank, CodeScanner.bank,
      CodeHeaderMachine.contents]
    omega
  rw [hc] at hr
  simpa only [S, cleared_basic, ready, cfg, CodeScanner.blank] using hr

theorem start_cons (bit : Bool) (tail output : List Bool) :
    advance program (ready (bit::tail) output) =
      cfg (some (.inl .first)) ((none,none),none) (bit::tail) [] [] [] [] [] [] output := by
  change (⟨some (.inl .first),((none,none),none),
    Function.update (Function.update
      (CodeScanner.bank (CodeHeaderMachine.contents (bit::tail) [] [] [] [] [] []) output)
      (.inl 0) tail) (.inl 0) (bit::tail)⟩ : Config) = _
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem start_code (c : Code) (rest output : List Bool) :
    advance program (ready (encodeCode c ++ rest) output) =
      cfg (some (.inl .first)) ((none,none),none)
        (encodeCode c ++ rest) [] [] [] [] [] [] output := by
  cases c <;> exact start_cons _ _ _

theorem start_empty (output : List Bool) :
    advance program (ready [] output) =
      cfg none ((none,none),none) [] [] [] [] [] [] [] output := by
  change (⟨none,((none,none),none),
    Function.update (CodeScanner.bank
      (CodeHeaderMachine.contents [] [] [] [] [] [] []) output) (.inl 0) []⟩ : Config) = _
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem emit_operation (bits rest output : List Bool) :
    ∃ t ≤ 6*bits.length+18, ((advance program)^[t])
      (ready (encodeCode (.emit bits) ++ rest) output) =
      ready rest (bits.reverse ++ output) := by
  obtain ⟨h, hh, hr⟩ := header_run (.emit bits) rest output
  have hd : advance program
      (cfg (some (.inr .dispatch)) ((none,some .emit),none)
        rest (List.replicate bits.length true) [] [] [] bits [] output) =
      cfg (some (.inr .emit)) ((none,none),none)
        rest (List.replicate bits.length true) [] [] [] bits [] output := rfl
  have he := emit_run bits none rest (List.replicate bits.length true) [] [] [] [] output
  have hc := clear_run rest (List.replicate bits.length true) [] [] (bits.reverse ++ output)
  simp only [List.length_replicate, List.length_nil, Nat.add_zero] at hc
  refine ⟨(bits.length+7)+(bits.length+1)+1+h+1, ?_, ?_⟩
  · simp only [CodeHeaderMachine.headerCost] at hh
    omega
  · rw [Function.iterate_add_apply, Function.iterate_one, start_code,
      Function.iterate_add_apply, hr]
    change ((advance program)^[(bits.length+7)+(bits.length+1)+1])
      (cfg (some (.inr .dispatch)) ((none,some .emit),none)
        rest (List.replicate bits.length true) [] [] [] bits [] output) = _
    rw [Function.iterate_add_apply, Function.iterate_one, hd,
      Function.iterate_add_apply, he, hc]

theorem append_operation (a b : Code) (rest output : List Bool) :
    ∃ t ≤ 13, ((advance program)^[t])
      (ready (encodeCode (.append a b) ++ rest) output) =
      ready (encodeCode a ++ encodeCode b ++ rest) output := by
  obtain ⟨h, hh, hr⟩ := header_run (.append a b) rest output
  have hd : advance program
      (cfg (some (.inr .dispatch)) ((none,some .append),none)
        (encodeCode a ++ encodeCode b ++ rest) [] [] [] [] [] [] output) =
      cfg (some (.inr (.clear 0))) ((none,none),none)
        (encodeCode a ++ encodeCode b ++ rest) [] [] [] [] [] [] output := rfl
  have hc := clear_run (encodeCode a ++ encodeCode b ++ rest) [] [] [] output
  refine ⟨7+1+h+1, ?_, ?_⟩
  · simp only [CodeHeaderMachine.headerCost] at hh
    omega
  · rw [Function.iterate_add_apply, Function.iterate_one, start_code,
      Function.iterate_add_apply, hr]
    change ((advance program)^[7+1])
      (cfg (some (.inr .dispatch)) ((none,some .append),none)
        (encodeCode a ++ encodeCode b ++ rest) [] [] [] [] [] [] output) = _
    rw [Function.iterate_add_apply, Function.iterate_one, hd]
    exact hc

#print axioms emit_operation
#print axioms append_operation

/-- Nonadministrative headers are returned with their actual operands and
finite tag. No draw is executed here, and zero alphabets are not normalized. -/
theorem draw_header (c : Code) (rest output : List Bool)
    (he : CodeHeaderMachine.headerKind c ≠ .emit)
    (ha : CodeHeaderMachine.headerKind c ≠ .append) :
    ∃ t ≤ CodeHeaderMachine.headerCost c + 2, ((advance program)^[t])
      (ready (encodeCode c ++ rest) output) =
      cfg none ((none,some (CodeHeaderMachine.headerKind c)),none)
        (CodeHeaderMachine.headerTail c rest)
        (CodeHeaderMachine.headerN c) (CodeHeaderMachine.headerA c)
        (CodeHeaderMachine.headerB c) [] (CodeHeaderMachine.headerWord c) [] output := by
  obtain ⟨h,hh,hr⟩ := header_run c rest output
  have hd : advance program
      (cfg (some (.inr .dispatch)) ((none,some (CodeHeaderMachine.headerKind c)),none)
        (CodeHeaderMachine.headerTail c rest)
        (CodeHeaderMachine.headerN c) (CodeHeaderMachine.headerA c)
        (CodeHeaderMachine.headerB c) [] (CodeHeaderMachine.headerWord c) [] output) =
      cfg none ((none,some (CodeHeaderMachine.headerKind c)),none)
        (CodeHeaderMachine.headerTail c rest)
        (CodeHeaderMachine.headerN c) (CodeHeaderMachine.headerA c)
        (CodeHeaderMachine.headerB c) [] (CodeHeaderMachine.headerWord c) [] output := by
    simp only [advance, TM2.step, program, cfg, TM2.stepAux, Option.some.injEq,
      he, ha, decide_false, Option.getD_some]
    rfl
  refine ⟨1+h+1,by omega,?_⟩
  rw [Function.iterate_add_apply, Function.iterate_one, start_code,
    Function.iterate_add_apply, hr, Function.iterate_one, hd]

#print axioms draw_header

end Paper2.CodeAdminMachine
