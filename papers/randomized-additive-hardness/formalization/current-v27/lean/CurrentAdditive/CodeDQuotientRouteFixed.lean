import CurrentAdditive.CodeDBankTransferV2
import CurrentAdditive.CodeDPairProductTargetV2
import EthInapproximability.CurrentPaper.BitMachineBankWrapper

/-!
Physical routing from the twelve-field staging packet to the four operand
fields of the signed rational product machine. The source rational-pair parser
is a separate physical component.
-/

namespace CurrentAdditive.CodeDQuotientRouteFixed

open EthInapproximability.CurrentPaper
open Turing TM2.Stmt BitMachineEncoding
open CodeDBankTransferV2
open RationalProductSignedPhysical

abbrev Bank := BitMachineBankCodec.Bank 12

inductive Label where
  | signX | signY | denX | numY | denYOne | denYTwo
  | scanNumX | choose | pad | restoreNumX | done
  deriving DecidableEq, Fintype

structure Flags where
  signX : Bool
  signY : Bool
  parity : Bool
  deriving DecidableEq, Fintype

abbrev Control := Flags × Option Bool
def initial : Control := (⟨false,false,false⟩, none)

def program : Label → TM2.Stmt (fun _ : Fin 12 => Bool) Label Control
  | .signX => pop 0 (fun v b => ({v.1 with signX := b.getD false}, b))
      (goto (fun _ => .signY))
  | .signY => pop 6 (fun v b => ({v.1 with signY := b.getD false}, b))
      (goto (fun _ => .denX))
  | .denX => BitMachineBroadcast.scanStep 2 9 .denX .numY
  | .numY => BitMachineBroadcast.scanStep 7 10 .numY .denYOne
  | .denYOne => BitMachineBroadcast.scanStep 8 11 .denYOne .denYTwo
  | .denYTwo => BitMachineBroadcast.scanStep 11 4 .denYTwo .scanNumX
  | .scanNumX => pop 1
      (fun v b => ({v.1 with parity := if b.isSome then !v.1.parity else v.1.parity}, b))
      (branch (fun v => v.2.isSome)
        (push 5 (fun v => v.2.getD false) (goto (fun _ => .scanNumX)))
        (goto (fun _ => .choose)))
  | .choose => branch (fun v => v.1.parity != (v.1.signX != v.1.signY))
      (goto (fun _ => .pad)) (goto (fun _ => .restoreNumX))
  | .pad => push 3 (fun _ => false) (goto (fun _ => .restoreNumX))
  | .restoreNumX => BitMachineBroadcast.scanStep 5 3 .restoreNumX .done
  | .done => halt

def cfg (l : Option Label) (v : Control) (S : Bank) :
    TM2.Cfg (fun _ : Fin 12 => Bool) Label Control := ⟨l,v,S⟩

def run (t : Nat) (c : TM2.Cfg (fun _ : Fin 12 => Bool) Label Control) :=
  ((advance program)^[t]) c

theorem run_succ (t : Nat) (c : TM2.Cfg (fun _ : Fin 12 => Bool) Label Control) :
    run (t+1) c = run t (advance program c) :=
  Function.iterate_succ_apply _ _ _

theorem run_add (t u : Nat) (c : TM2.Cfg (fun _ : Fin 12 => Bool) Label Control) :
    run (t+u) c = run u (run t c) := by
  simpa only [run, Nat.add_comm] using Function.iterate_add_apply (advance program) u t c

def dropSigns (S : Bank) : Bank :=
  Function.update (Function.update S 0 ((S 0).drop 1)) 6 ((S 6).drop 1)

def transferredOperands (S : Bank) : Bank :=
  transferred 11 4 (transferred 8 11 (transferred 7 10 (transferred 2 9 (dropSigns S))))

def scannedNum (S : Bank) : Bank :=
  transferred 1 5 S

def paddedNum (S : Bank) (sx sy : Bool) : Bank :=
  if RationalProductSignedRepack.signParity (S 1) != (sx != sy) then
    Function.update (scannedNum S) 3 (false :: (scannedNum S) 3)
  else scannedNum S

def outputBank (S : Bank) : Bank :=
  transferred 5 3 (paddedNum (transferredOperands S)
    ((S 0).headD false) ((S 6).headD false))

theorem signX_step (v : Control) (S : Bank) :
    advance program (cfg (some .signX) v S) =
      cfg (some .signY) ({v.1 with signX := (S 0).headD false}, (S 0).head?)
        (Function.update S 0 ((S 0).drop 1)) := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]

theorem signY_step (v : Control) (S : Bank) :
    advance program (cfg (some .signY) v S) =
      cfg (some .denX) ({v.1 with signY := (S 6).headD false}, (S 6).head?)
        (Function.update S 6 ((S 6).drop 1)) := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]

theorem denX_run (v : Control) (S : Bank) :
    run ((S 2).length+1) (cfg (some .denX) v S) =
      cfg (some .numY) (v.1, none) (transferred 2 9 S) := by
  exact transfer_run program 2 9 (by decide) .denX .numY rfl v.1 v.2 S

theorem numY_run (v : Control) (S : Bank) :
    run ((S 7).length+1) (cfg (some .numY) v S) =
      cfg (some .denYOne) (v.1, none) (transferred 7 10 S) := by
  exact transfer_run program 7 10 (by decide) .numY .denYOne rfl v.1 v.2 S

theorem denYOne_run (v : Control) (S : Bank) :
    run ((S 8).length+1) (cfg (some .denYOne) v S) =
      cfg (some .denYTwo) (v.1, none) (transferred 8 11 S) := by
  exact transfer_run program 8 11 (by decide) .denYOne .denYTwo rfl v.1 v.2 S

theorem denYTwo_run (v : Control) (S : Bank) :
    run ((S 11).length+1) (cfg (some .denYTwo) v S) =
      cfg (some .scanNumX) (v.1, none) (transferred 11 4 S) := by
  exact transfer_run program 11 4 (by decide) .denYTwo .scanNumX rfl v.1 v.2 S

def numContents (S : Bank) (word saved : List Bool) : Bank :=
  Function.update (Function.update S 1 word) 5 saved

theorem scanNumX_cons (f : Flags) (p : Option Bool) (S : Bank)
    (b : Bool) (rest saved : List Bool) :
    advance program (cfg (some .scanNumX) (f,p) (numContents S (b::rest) saved)) =
      cfg (some .scanNumX) ({f with parity := !f.parity}, some b)
        (numContents S rest (b::saved)) := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux, numContents]
  funext k; fin_cases k <;> simp

theorem scanNumX_nil (f : Flags) (p : Option Bool) (S : Bank)
    (saved : List Bool) :
    advance program (cfg (some .scanNumX) (f,p) (numContents S [] saved)) =
      cfg (some .choose) (f,none) (numContents S [] saved) := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux, numContents]

theorem scanNumX_run (f : Flags) (p : Option Bool) (S : Bank)
    (word saved : List Bool) :
    run (word.length+1) (cfg (some .scanNumX) (f,p) (numContents S word saved)) =
      cfg (some .choose)
        ({f with parity := f.parity != RationalProductSignedRepack.signParity word},none)
        (numContents S [] (word.reverse ++ saved)) := by
  induction word generalizing f p saved with
  | nil => simpa [run, RationalProductSignedRepack.signParity] using
      scanNumX_nil f p S saved
  | cons b rest ih =>
      rw [List.length_cons,
        show rest.length+1+1 = (rest.length+1)+1 by omega,
        run_succ, scanNumX_cons]
      simpa [RationalProductSignedRepack.signParity, List.reverse_cons,
        Bool.xor_assoc] using ih {f with parity := !f.parity} (some b) (b::saved)

theorem scanNumX_run_bank (f : Flags) (p : Option Bool) (S : Bank) :
    run ((S 1).length+1) (cfg (some .scanNumX) (f,p) S) =
      cfg (some .choose)
        ({f with parity := f.parity != RationalProductSignedRepack.signParity (S 1)},none)
        (transferred 1 5 S) := by
  have h := scanNumX_run f p S (S 1) (S 5)
  have hi : numContents S (S 1) (S 5) = S := by simp [numContents]
  have ho : numContents S [] ((S 1).reverse ++ S 5) = transferred 1 5 S := by
    rfl
  simpa only [hi, ho] using h

theorem choose_step (v : Control) (S : Bank) :
    advance program (cfg (some .choose) v S) =
      cfg (some (if v.1.parity != (v.1.signX != v.1.signY)
        then .pad else .restoreNumX)) v S := by
  cases h : v.1.parity != (v.1.signX != v.1.signY) <;>
    simp [advance, program, cfg, TM2.step, TM2.stepAux, h]

theorem pad_step (v : Control) (S : Bank) :
    advance program (cfg (some .pad) v S) =
      cfg (some .restoreNumX) v (Function.update S 3 (false :: S 3)) := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]

theorem restoreNumX_run (v : Control) (S : Bank) :
    run ((S 5).length+1) (cfg (some .restoreNumX) v S) =
      cfg (some .done) (v.1, none) (transferred 5 3 S) := by
  exact transfer_run program 5 3 (by decide) .restoreNumX .done rfl v.1 v.2 S

theorem done_step (v : Control) (S : Bank) :
    advance program (cfg (some .done) v S) = cfg none v S := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]

theorem signs_run (S : Bank) :
    run 2 (cfg (some .signX) initial S) =
      cfg (some .denX)
        (⟨(S 0).headD false, (S 6).headD false, false⟩, (S 6).head?)
        (dropSigns S) := by
  rw [show (2 : Nat) = 1+1 by omega, run_add]
  change run 1 (advance program (cfg (some .signX) initial S)) = _
  rw [signX_step]
  simp only [run, Function.iterate_one]
  rw [signY_step]
  simp [initial, dropSigns]

def preTime (S : Bank) : Nat :=
  let A := dropSigns S
  let B := transferred 2 9 A
  let C := transferred 7 10 B
  let D := transferred 8 11 C
  let E := transferred 11 4 D
  2 + ((A 2).length+1) + ((B 7).length+1) +
    ((C 8).length+1) + ((D 11).length+1) + ((E 1).length+1)

theorem pre_run (S : Bank) :
    run (preTime S) (cfg (some .signX) initial S) =
      cfg (some .choose)
        (⟨(S 0).headD false, (S 6).headD false,
          RationalProductSignedRepack.signParity (S 1)⟩, none)
        (scannedNum (transferredOperands S)) := by
  let A := dropSigns S
  let B := transferred 2 9 A
  let C := transferred 7 10 B
  let D := transferred 8 11 C
  let E := transferred 11 4 D
  let f : Flags := ⟨(S 0).headD false, (S 6).headD false, false⟩
  have h₀ : run 2 (cfg (some .signX) initial S) =
      cfg (some .denX) (f, (S 6).head?) A := by
    simpa [A, f] using signs_run S
  have h₁ : run (2+((A 2).length+1)) (cfg (some .signX) initial S) =
      cfg (some .numY) (f,none) B := by
    rw [run_add, h₀]
    simpa [B] using denX_run (f,(S 6).head?) A
  have h₂ : run (2+((A 2).length+1)+((B 7).length+1))
      (cfg (some .signX) initial S) = cfg (some .denYOne) (f,none) C := by
    rw [run_add, h₁]
    simpa [C] using numY_run (f,none) B
  have h₃ : run (2+((A 2).length+1)+((B 7).length+1)+((C 8).length+1))
      (cfg (some .signX) initial S) = cfg (some .denYTwo) (f,none) D := by
    rw [run_add, h₂]
    simpa [D] using denYOne_run (f,none) C
  have h₄ : run (2+((A 2).length+1)+((B 7).length+1)+
      ((C 8).length+1)+((D 11).length+1))
      (cfg (some .signX) initial S) = cfg (some .scanNumX) (f,none) E := by
    rw [run_add, h₃]
    simpa [E] using denYTwo_run (f,none) D
  have h₅ : run (2+((A 2).length+1)+((B 7).length+1)+
      ((C 8).length+1)+((D 11).length+1)+((E 1).length+1))
      (cfg (some .signX) initial S) =
      cfg (some .choose)
        (⟨(S 0).headD false, (S 6).headD false,
          RationalProductSignedRepack.signParity (S 1)⟩,none)
        (scannedNum E) := by
    rw [run_add, h₄]
    have he : E 1 = S 1 := by
      simp [E, D, C, B, A, transferred, dropSigns]
    simpa [scannedNum, f, he] using scanNumX_run_bank f none E
  simpa [preTime, A, B, C, D, E, transferredOperands] using h₅

def needsPad (S : Bank) : Bool :=
  RationalProductSignedRepack.signParity (S 1) !=
    ((S 0).headD false != (S 6).headD false)

def routeTime (S : Bank) : Nat :=
  preTime S + 1 + (if needsPad S then 1 else 0) +
    ((paddedNum (transferredOperands S)
      ((S 0).headD false) ((S 6).headD false)) 5).length + 2

theorem choose_pad_run (S : Bank) :
    run (1 + if needsPad S then 1 else 0)
      (cfg (some .choose)
        (⟨(S 0).headD false, (S 6).headD false,
          RationalProductSignedRepack.signParity (S 1)⟩,none)
        (scannedNum (transferredOperands S))) =
      cfg (some .restoreNumX)
        (⟨(S 0).headD false, (S 6).headD false,
          RationalProductSignedRepack.signParity (S 1)⟩,none)
        (paddedNum (transferredOperands S)
          ((S 0).headD false) ((S 6).headD false)) := by
  let E := transferredOperands S
  let f : Flags := ⟨(S 0).headD false, (S 6).headD false,
    RationalProductSignedRepack.signParity (S 1)⟩
  have he : E 1 = S 1 := by
    simp [E, transferredOperands, transferred, dropSigns]
  by_cases h : needsPad S = true
  · have hm : (f.parity != (f.signX != f.signY)) = true := by
      simpa [needsPad, f] using h
    have hp : paddedNum E ((S 0).headD false) ((S 6).headD false) =
        Function.update (scannedNum E) 3 (false :: (scannedNum E) 3) := by
      simp [paddedNum, he, needsPad] at h ⊢
      exact h
    simp only [if_pos h]
    rw [show (1+1 : Nat) = 1+1 by rfl, run_add]
    change run 1 (advance program (cfg (some .choose) (f,none) (scannedNum E))) = _
    rw [choose_step]
    simp only [hm, if_pos]
    simp only [run, Function.iterate_one]
    rw [pad_step]
    simpa [E, f] using
      congrArg (cfg (some .restoreNumX) (f,none)) hp.symm
  · have hm : (f.parity != (f.signX != f.signY)) = false := by
      simpa [needsPad, f] using Bool.eq_false_iff.mpr h
    have hp : paddedNum E ((S 0).headD false) ((S 6).headD false) = scannedNum E := by
      simp [paddedNum, he, needsPad] at h ⊢
      simp [h]
    simp only [if_neg h, Nat.add_zero]
    change advance program (cfg (some .choose) (f,none) (scannedNum E)) = _
    rw [choose_step]
    simp only [hm]
    simpa [E, f] using
      congrArg (cfg (some .restoreNumX) (f,none)) hp.symm

theorem local_run (S : Bank) :
    run (routeTime S) (cfg (some .signX) initial S) =
      cfg none
        (⟨(S 0).headD false, (S 6).headD false,
          RationalProductSignedRepack.signParity (S 1)⟩,none)
        (outputBank S) := by
  let P := paddedNum (transferredOperands S)
    ((S 0).headD false) ((S 6).headD false)
  let f : Flags := ⟨(S 0).headD false, (S 6).headD false,
    RationalProductSignedRepack.signParity (S 1)⟩
  have h₀ := pre_run S
  have h₁ := choose_pad_run S
  have h₂ := restoreNumX_run (f,none) P
  have h₃ := done_step (f,none) (transferred 5 3 P)
  have h₀₁ : run (preTime S + (1 + if needsPad S then 1 else 0))
      (cfg (some .signX) initial S) = cfg (some .restoreNumX) (f,none) P := by
    rw [run_add, h₀]
    simpa [P, f] using h₁
  have h₀₂ : run ((preTime S + (1 + if needsPad S then 1 else 0)) +
      ((P 5).length+1)) (cfg (some .signX) initial S) =
      cfg (some .done) (f,none) (transferred 5 3 P) := by
    rw [run_add, h₀₁]
    simpa using h₂
  have h₀₃ : run (((preTime S + (1 + if needsPad S then 1 else 0)) +
      ((P 5).length+1))+1) (cfg (some .signX) initial S) =
      cfg none (f,none) (transferred 5 3 P) := by
    rw [run_add, h₀₂]
    simpa [run] using h₃
  simpa [routeTime, outputBank, P, f, Nat.add_assoc] using h₀₃

#print axioms local_run

end CurrentAdditive.CodeDQuotientRouteFixed
