import CurrentAdditive.UnsignedCompare
import EthInapproximability.CurrentPaper.BitMachineBinaryAddAny
import EthInapproximability.CurrentPaper.BitMachineBankWrapper

/-!
A literal fixed-width stack scan for signed magnitude subtraction. Input stacks
0,1 are sign words and 2,3 are little-endian magnitudes. The scan computes
both unsigned differences and their sum at once; its finite control chooses
the correct sign and magnitude. No unbounded integer lives in control.
-/

namespace EthInapproximability.CurrentPaper.SignedMagnitudeSubtract

set_option maxRecDepth 2048
set_option maxHeartbeats 0

open Turing Turing.TM2.Stmt BitMachineEncoding
open BitMachineBinarySubtract (outBit nextBorrow)
open BitMachineBinaryAdd (sumBit nextCarry)

abbrev Bank := Fin 9 → List Bool

structure Control where
  negativeA : Bool
  negativeB : Bool
  borrowAB : Bool
  borrowBA : Bool
  carry : Bool
  a : Option Bool
  b : Option Bool
  deriving DecidableEq

def controlEquiv : Control ≃
    Bool × Bool × Bool × Bool × Bool × Option Bool × Option Bool where
  toFun := fun s => ⟨s.negativeA,s.negativeB,s.borrowAB,s.borrowBA,s.carry,s.a,s.b⟩
  invFun := fun ⟨a,b,c,d,e,f,g⟩ => ⟨a,b,c,d,e,f,g⟩
  left_inv := by intro ⟨a,b,c,d,e,f,g⟩; rfl
  right_inv := by intro ⟨a,b,c,d,e,f,g⟩; rfl

instance : Fintype Control := Fintype.ofEquiv _ controlEquiv.symm

def initial : Control := ⟨false, false, false, false, false, none, none⟩

inductive Label where
  | signA | signB | scan | choose | dropAB | dropBA | dropSum
  | moveAB | moveBA | moveSum | emitNegative | done
  deriving DecidableEq, Fintype

def program : Label → TM2.Stmt (fun _ : Fin 9 => Bool) Label Control
  | .signA => pop 0 (fun s bit => {s with negativeA := bit.getD false})
      (goto (fun _ => .signB))
  | .signB => pop 1 (fun s bit => {s with negativeB := bit.getD false})
      (goto (fun _ => .scan))
  | .scan => pop 2 (fun s bit => {s with a := bit})
      (pop 3 (fun s bit => {s with b := bit})
        (branch (fun s => s.a.isSome || s.b.isSome)
          (push 4 (fun s => outBit (s.a.getD false) (s.b.getD false) s.borrowAB)
            (push 5 (fun s => outBit (s.b.getD false) (s.a.getD false) s.borrowBA)
              (push 6 (fun s => sumBit (s.a.getD false) (s.b.getD false) s.carry)
                (load (fun s => {s with
                  borrowAB := nextBorrow (s.a.getD false) (s.b.getD false) s.borrowAB,
                  borrowBA := nextBorrow (s.b.getD false) (s.a.getD false) s.borrowBA,
                  carry := nextCarry (s.a.getD false) (s.b.getD false) s.carry,
                  a := none, b := none})
                  (goto (fun _ => .scan))))))
          (goto (fun _ => .choose))))
  | .choose =>
      push 6 (fun s => s.carry)
        (branch (fun s => s.negativeA == s.negativeB)
          (branch (fun s => s.borrowAB)
            (goto (fun _ => .dropAB))
            (goto (fun _ => .dropBA)))
          (goto (fun _ => .dropAB)))
  | .dropAB => pop 4 (fun s bit => {s with a := bit})
      (branch (fun s => s.a.isSome) (goto (fun _ => .dropAB))
        (branch (fun s => s.negativeA == s.negativeB)
          (goto (fun _ => .dropSum))
          (goto (fun _ => .dropBA))))
  | .dropBA => pop 5 (fun s bit => {s with a := bit})
      (branch (fun s => s.a.isSome) (goto (fun _ => .dropBA))
        (branch (fun s => s.negativeA == s.negativeB)
          (goto (fun _ => .dropSum))
          (goto (fun _ => .moveSum))))
  | .dropSum => pop 6 (fun s bit => {s with a := bit})
      (branch (fun s => s.a.isSome) (goto (fun _ => .dropSum))
        (branch (fun s => s.negativeA == s.negativeB)
          (branch (fun s => s.borrowAB)
            (goto (fun _ => .moveBA))
            (goto (fun _ => .moveAB)))
          (goto (fun _ => .moveSum))))
  | .moveAB => pop 4 (fun s bit => {s with a := bit})
      (branch (fun s => s.a.isSome)
        (push 8 (fun s => s.a.getD false) (goto (fun _ => .moveAB)))
        (goto (fun _ => .emitNegative)))
  | .moveBA => pop 5 (fun s bit => {s with a := bit})
      (branch (fun s => s.a.isSome)
        (push 8 (fun s => s.a.getD false) (goto (fun _ => .moveBA)))
        (goto (fun _ => .emitNegative)))
  | .moveSum => pop 6 (fun s bit => {s with a := bit})
      (branch (fun s => s.a.isSome)
        (push 8 (fun s => s.a.getD false) (goto (fun _ => .moveSum)))
        (goto (fun _ => .emitNegative)))
  | .emitNegative =>
      branch (fun s => s.negativeA != (s.negativeA == s.negativeB && s.borrowAB))
        (push 7 (fun _ => true) (goto (fun _ => .done)))
        (goto (fun _ => .done))
  | .done => load (fun _ => initial) halt

def contents (signA signB a b ab ba sum signOut out : List Bool) : Bank :=
  ![signA,signB,a,b,ab,ba,sum,signOut,out]

def cfg (label : Option Label) (state : Control)
    (signA signB a b ab ba sum signOut out : List Bool) :
    TM2.Cfg (fun _ : Fin 9 => Bool) Label Control :=
  ⟨label,state,contents signA signB a b ab ba sum signOut out⟩

def run (t : ℕ) (c : TM2.Cfg (fun _ : Fin 9 => Bool) Label Control) :=
  ((advance program)^[t]) c

def scanState (negA negB borrowAB borrowBA carry : Bool) : Control :=
  ⟨negA,negB,borrowAB,borrowBA,carry,none,none⟩

private theorem scan_nil (nA nB q r c : Bool)
    (signA signB ab ba sum signOut out : List Bool) :
    advance program
      (cfg (some .scan) (scanState nA nB q r c)
        signA signB [] [] ab ba sum signOut out) =
    cfg (some .choose) (scanState nA nB q r c)
      signA signB [] [] ab ba sum signOut out := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, contents, scanState]
  funext k; fin_cases k <;> simp [contents]

private theorem scan_left (nA nB q r c x : Bool)
    (signA signB xs ab ba sum signOut out : List Bool) :
    advance program
      (cfg (some .scan) (scanState nA nB q r c)
        signA signB (x::xs) [] ab ba sum signOut out) =
    cfg (some .scan)
      (scanState nA nB (nextBorrow x false q)
        (nextBorrow false x r) (nextCarry x false c))
      signA signB xs [] (outBit x false q :: ab)
        (outBit false x r :: ba) (sumBit x false c :: sum) signOut out := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, contents, scanState]
  funext k; fin_cases k <;> simp [contents]

private theorem scan_right (nA nB q r c y : Bool)
    (signA signB ys ab ba sum signOut out : List Bool) :
    advance program
      (cfg (some .scan) (scanState nA nB q r c)
        signA signB [] (y::ys) ab ba sum signOut out) =
    cfg (some .scan)
      (scanState nA nB (nextBorrow false y q)
        (nextBorrow y false r) (nextCarry false y c))
      signA signB [] ys (outBit false y q :: ab)
        (outBit y false r :: ba) (sumBit false y c :: sum) signOut out := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, contents, scanState]
  funext k; fin_cases k <;> simp [contents]

private theorem scan_both (nA nB q r c x y : Bool)
    (signA signB xs ys ab ba sum signOut out : List Bool) :
    advance program
      (cfg (some .scan) (scanState nA nB q r c)
        signA signB (x::xs) (y::ys) ab ba sum signOut out) =
    cfg (some .scan)
      (scanState nA nB (nextBorrow x y q)
        (nextBorrow y x r) (nextCarry x y c))
      signA signB xs ys (outBit x y q :: ab)
        (outBit y x r :: ba) (sumBit x y c :: sum) signOut out := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, contents, scanState]
  funext k; fin_cases k <;> simp [contents]

private theorem step_run (c : TM2.Cfg (fun _ : Fin 9 => Bool) Label Control)
    (t : ℕ) : run (t+1) c = run t (advance program c) :=
  Function.iterate_succ_apply _ _ _

private theorem run_add (c : TM2.Cfg (fun _ : Fin 9 => Bool) Label Control)
    (t u : ℕ) : run (t+u) c = run u (run t c) := by
  simpa only [run, Nat.add_comm] using
    Function.iterate_add_apply (advance program) u t c

structure ScanWords where
  ab : List Bool
  ba : List Bool
  sum : List Bool
  borrowAB : Bool
  borrowBA : Bool
  carry : Bool

def scanWords : List Bool → List Bool → Bool → Bool → Bool → ScanWords
  | [], [], q, r, c => ⟨[],[],[],q,r,c⟩
  | x::xs, [], q, r, c =>
      let t := scanWords xs [] (nextBorrow x false q)
        (nextBorrow false x r) (nextCarry x false c)
      ⟨outBit x false q :: t.ab, outBit false x r :: t.ba,
        sumBit x false c :: t.sum, t.borrowAB, t.borrowBA, t.carry⟩
  | [], y::ys, q, r, c =>
      let t := scanWords [] ys (nextBorrow false y q)
        (nextBorrow y false r) (nextCarry false y c)
      ⟨outBit false y q :: t.ab, outBit y false r :: t.ba,
        sumBit false y c :: t.sum, t.borrowAB, t.borrowBA, t.carry⟩
  | x::xs, y::ys, q, r, c =>
      let t := scanWords xs ys (nextBorrow x y q)
        (nextBorrow y x r) (nextCarry x y c)
      ⟨outBit x y q :: t.ab, outBit y x r :: t.ba,
        sumBit x y c :: t.sum, t.borrowAB, t.borrowBA, t.carry⟩

theorem scan_run (signA signB a b ab ba sum signOut out : List Bool)
    (nA nB q r c : Bool) :
    let t := scanWords a b q r c
    run (max a.length b.length + 1)
      (cfg (some .scan) (scanState nA nB q r c)
        signA signB a b ab ba sum signOut out) =
    cfg (some .choose)
      (scanState nA nB t.borrowAB t.borrowBA t.carry)
      signA signB [] [] (t.ab.reverse ++ ab) (t.ba.reverse ++ ba)
        (t.sum.reverse ++ sum) signOut out := by
  induction a generalizing b ab ba sum q r c with
  | nil =>
      induction b generalizing ab ba sum q r c with
      | nil => simp [scanWords, run, scan_nil]
      | cons y ys ih =>
          simp only [List.length_nil, List.length_cons, Nat.zero_le,
            max_eq_right, scanWords]
          rw [show ys.length + 1 + 1 = (ys.length + 1) + 1 by omega,
            step_run, scan_right]
          simpa [scanWords, List.reverse_cons, List.append_assoc] using
            ih (outBit false y q :: ab) (outBit y false r :: ba)
              (sumBit false y c :: sum) (nextBorrow false y q)
              (nextBorrow y false r) (nextCarry false y c)
  | cons x xs ih =>
      cases b with
      | nil =>
          simp only [List.length_cons, List.length_nil, Nat.zero_le,
            max_eq_left, scanWords]
          rw [show xs.length + 1 + 1 = (xs.length + 1) + 1 by omega,
            step_run, scan_left]
          simpa [scanWords, List.reverse_cons, List.append_assoc] using
            ih [] (outBit x false q :: ab) (outBit false x r :: ba)
              (sumBit x false c :: sum) (nextBorrow x false q)
              (nextBorrow false x r) (nextCarry x false c)
      | cons y ys =>
          simp only [List.length_cons, Nat.succ_max_succ, scanWords]
          rw [show max xs.length ys.length + 1 + 1 =
              (max xs.length ys.length + 1) + 1 by omega,
            step_run, scan_both]
          simpa [scanWords, List.reverse_cons, List.append_assoc] using
            ih ys (outBit x y q :: ab) (outBit y x r :: ba)
              (sumBit x y c :: sum) (nextBorrow x y q)
              (nextBorrow y x r) (nextCarry x y c)

theorem scanWords_spec (a b : List Bool) (q r c : Bool) :
    let t := scanWords a b q r c
    (t.ab, t.borrowAB) = BitMachineBinaryDivision.subAny a b q ∧
    (t.ba, t.borrowBA) = BitMachineBinaryDivision.subAny b a r ∧
    t.sum ++ [t.carry] = BitMachineBinaryAddAny.addAny a b c := by
  induction a generalizing b q r c with
  | nil =>
      induction b generalizing q r c with
      | nil => simp [scanWords, BitMachineBinaryDivision.subAny,
          BitMachineBinaryAddAny.addAny]
      | cons y ys ih =>
          have h := ih (nextBorrow false y q) (nextBorrow y false r)
            (nextCarry false y c)
          simp only [scanWords, BitMachineBinaryDivision.subAny,
            BitMachineBinaryAddAny.addAny]
          have ha := congrArg Prod.fst h.1
          have hq := congrArg Prod.snd h.1
          have hb := congrArg Prod.fst h.2.1
          have hr := congrArg Prod.snd h.2.1
          simp only [Prod.fst, Prod.snd] at ha hq hb hr
          simp [ha, hq, hb, hr, h.2.2]

  | cons x xs ih =>
      cases b with
      | nil =>
          have h := ih [] (nextBorrow x false q) (nextBorrow false x r)
            (nextCarry x false c)
          simp only [scanWords, BitMachineBinaryDivision.subAny,
            BitMachineBinaryAddAny.addAny]
          have ha := congrArg Prod.fst h.1
          have hq := congrArg Prod.snd h.1
          have hb := congrArg Prod.fst h.2.1
          have hr := congrArg Prod.snd h.2.1
          simp only [Prod.fst, Prod.snd] at ha hq hb hr
          simp [ha, hq, hb, hr, h.2.2]

      | cons y ys =>
          have h := ih ys (nextBorrow x y q) (nextBorrow y x r)
            (nextCarry x y c)
          simp only [scanWords, BitMachineBinaryDivision.subAny,
            BitMachineBinaryAddAny.addAny]
          have ha := congrArg Prod.fst h.1
          have hq := congrArg Prod.snd h.1
          have hb := congrArg Prod.fst h.2.1
          have hr := congrArg Prod.snd h.2.1
          simp only [Prod.fst, Prod.snd] at ha hq hb hr
          simp [ha, hq, hb, hr, h.2.2]

private theorem dropAB_run (s : Control)
    (signA signB a b ab ba sum signOut out : List Bool) :
    run (ab.length+1)
      (cfg (some .dropAB) s signA signB a b ab ba sum signOut out) =
    cfg (some (if s.negativeA == s.negativeB then .dropSum else .dropBA))
      {s with a := none} signA signB a b [] ba sum signOut out := by
  induction ab generalizing s with
  | nil =>
      cases hA : s.negativeA <;> cases hB : s.negativeB <;>
        simp [run, advance, TM2.step, TM2.stepAux, program,
          cfg, contents, hA, hB]
      all_goals funext k; fin_cases k <;> simp [contents]
  | cons x xs ih =>
      rw [List.length_cons, step_run]
      have hs : advance program
          (cfg (some .dropAB) s signA signB a b (x::xs) ba sum signOut out) =
          cfg (some .dropAB) {s with a := some x}
            signA signB a b xs ba sum signOut out := by
        simp [advance, TM2.step, TM2.stepAux, program, cfg, contents]
        funext k; fin_cases k <;> simp [contents]
      rw [hs, ih]

private theorem dropBA_run (s : Control)
    (signA signB a b ab ba sum signOut out : List Bool) :
    run (ba.length+1)
      (cfg (some .dropBA) s signA signB a b ab ba sum signOut out) =
    cfg (some (if s.negativeA == s.negativeB then .dropSum else .moveSum))
      {s with a := none} signA signB a b ab [] sum signOut out := by
  induction ba generalizing s with
  | nil =>
      cases hA : s.negativeA <;> cases hB : s.negativeB <;>
        simp [run, advance, TM2.step, TM2.stepAux, program,
          cfg, contents, hA, hB]
  | cons x xs ih =>
      rw [List.length_cons, step_run]
      have hs : advance program
          (cfg (some .dropBA) s signA signB a b ab (x::xs) sum signOut out) =
          cfg (some .dropBA) {s with a := some x}
            signA signB a b ab xs sum signOut out := by
        simp [advance, TM2.step, TM2.stepAux, program, cfg, contents]
        funext k; fin_cases k <;> simp [contents]
      rw [hs, ih]

private theorem dropSum_run (s : Control)
    (signA signB a b ab ba sum signOut out : List Bool) :
    run (sum.length+1)
      (cfg (some .dropSum) s signA signB a b ab ba sum signOut out) =
    cfg (some (if s.negativeA == s.negativeB then
        if s.borrowAB then .moveBA else .moveAB else .moveSum))
      {s with a := none} signA signB a b ab ba [] signOut out := by
  induction sum generalizing s with
  | nil =>
      cases hA : s.negativeA <;> cases hB : s.negativeB <;>
        cases hQ : s.borrowAB <;>
        simp [run, advance, TM2.step, TM2.stepAux, program,
          cfg, contents, hA, hB, hQ]
  | cons x xs ih =>
      rw [List.length_cons, step_run]
      have hs : advance program
          (cfg (some .dropSum) s signA signB a b ab ba (x::xs) signOut out) =
          cfg (some .dropSum) {s with a := some x}
            signA signB a b ab ba xs signOut out := by
        simp [advance, TM2.step, TM2.stepAux, program, cfg, contents]
        funext k; fin_cases k <;> simp [contents]
      rw [hs, ih]

private theorem moveAB_run (s : Control)
    (signA signB a b ab ba sum signOut out : List Bool) :
    run (ab.length+1)
      (cfg (some .moveAB) s signA signB a b ab ba sum signOut out) =
    cfg (some .emitNegative) {s with a := none}
      signA signB a b [] ba sum signOut (ab.reverse ++ out) := by
  induction ab generalizing s out with
  | nil =>
      simp [run, advance, TM2.step, TM2.stepAux, program, cfg, contents]
  | cons x xs ih =>
      rw [List.length_cons, step_run]
      have hs : advance program
          (cfg (some .moveAB) s signA signB a b (x::xs) ba sum signOut out) =
          cfg (some .moveAB) {s with a := some x}
            signA signB a b xs ba sum signOut (x::out) := by
        simp [advance, TM2.step, TM2.stepAux, program, cfg, contents]
        funext k; fin_cases k <;> simp [contents]
      rw [hs, ih]
      simp [List.reverse_cons, List.append_assoc]

private theorem moveBA_run (s : Control)
    (signA signB a b ab ba sum signOut out : List Bool) :
    run (ba.length+1)
      (cfg (some .moveBA) s signA signB a b ab ba sum signOut out) =
    cfg (some .emitNegative) {s with a := none}
      signA signB a b ab [] sum signOut (ba.reverse ++ out) := by
  induction ba generalizing s out with
  | nil =>
      simp [run, advance, TM2.step, TM2.stepAux, program, cfg, contents]
  | cons x xs ih =>
      rw [List.length_cons, step_run]
      have hs : advance program
          (cfg (some .moveBA) s signA signB a b ab (x::xs) sum signOut out) =
          cfg (some .moveBA) {s with a := some x}
            signA signB a b ab xs sum signOut (x::out) := by
        simp [advance, TM2.step, TM2.stepAux, program, cfg, contents]
        funext k; fin_cases k <;> simp [contents]
      rw [hs, ih]
      simp [List.reverse_cons, List.append_assoc]

private theorem moveSum_run (s : Control)
    (signA signB a b ab ba sum signOut out : List Bool) :
    run (sum.length+1)
      (cfg (some .moveSum) s signA signB a b ab ba sum signOut out) =
    cfg (some .emitNegative) {s with a := none}
      signA signB a b ab ba [] signOut (sum.reverse ++ out) := by
  induction sum generalizing s out with
  | nil =>
      simp [run, advance, TM2.step, TM2.stepAux, program, cfg, contents]
  | cons x xs ih =>
      rw [List.length_cons, step_run]
      have hs : advance program
          (cfg (some .moveSum) s signA signB a b ab ba (x::xs) signOut out) =
          cfg (some .moveSum) {s with a := some x}
            signA signB a b ab ba xs signOut (x::out) := by
        simp [advance, TM2.step, TM2.stepAux, program, cfg, contents]
        funext k; fin_cases k <;> simp [contents]
      rw [hs, ih]
      simp [List.reverse_cons, List.append_assoc]

def outputNegative (s : Control) : Bool :=
  s.negativeA != ((s.negativeA == s.negativeB) && s.borrowAB)

def selectedWord (s : Control) (ab ba sum : List Bool) : List Bool :=
  if s.negativeA == s.negativeB then
    if s.borrowAB then ba.reverse else ab.reverse
  else sum.reverse ++ [s.carry]

private theorem choose_step (s : Control)
    (signA signB a b ab ba sum signOut out : List Bool) :
    run 1 (cfg (some .choose) s signA signB a b ab ba sum signOut out) =
    cfg (some (if s.negativeA == s.negativeB then
        if s.borrowAB then .dropAB else .dropBA else .dropAB)) s
      signA signB a b ab ba (s.carry :: sum) signOut out := by
  cases hA : s.negativeA <;> cases hB : s.negativeB <;>
    cases hQ : s.borrowAB <;>
    simp [run, advance, TM2.step, TM2.stepAux, program, cfg,
      contents, hA, hB, hQ]
  all_goals funext k; fin_cases k <;> simp [contents]

private theorem finish_run (s : Control)
    (signA signB a b ab ba sum signOut out : List Bool) :
    run 2 (cfg (some .emitNegative) s signA signB a b ab ba sum signOut out) =
    cfg none initial signA signB a b ab ba sum
      (if outputNegative s then true :: signOut else signOut) out := by
  cases hA : s.negativeA <;> cases hB : s.negativeB <;>
    cases hQ : s.borrowAB <;>
    simp [run, advance, TM2.step, TM2.stepAux, program, cfg,
      contents, outputNegative, hA, hB, hQ]
  all_goals funext k; fin_cases k <;> simp [contents]

private theorem chain5 (c0 c1 c2 c3 c4 c5 :
    TM2.Cfg (fun _ : Fin 9 => Bool) Label Control)
    (t1 t2 t3 t4 t5 : ℕ)
    (h1 : run t1 c0 = c1) (h2 : run t2 c1 = c2)
    (h3 : run t3 c2 = c3) (h4 : run t4 c3 = c4)
    (h5 : run t5 c4 = c5) :
    run (t1+t2+t3+t4+t5) c0 = c5 := by
  rw [run_add, run_add, run_add, run_add, h1, h2, h3, h4, h5]

private theorem post_opposite (s : Control)
    (signA signB a b ab ba sum signOut out : List Bool)
    (hS : (s.negativeA == s.negativeB) = false) :
    run (ab.length + ba.length + sum.length + 7)
      (cfg (some .choose) s signA signB a b ab ba sum signOut out) =
    cfg none initial signA signB a b [] [] []
      (if outputNegative s then true :: signOut else signOut)
      (sum.reverse ++ [s.carry] ++ out) := by
  let s' : Control := {s with a := none}
  have h1 := choose_step s signA signB a b ab ba sum signOut out
  have h2 := dropAB_run s signA signB a b ab ba (s.carry::sum) signOut out
  have h3 := dropBA_run s' signA signB a b [] ba (s.carry::sum) signOut out
  have h4 := moveSum_run s' signA signB a b [] [] (s.carry::sum) signOut out
  have h5 := finish_run s' signA signB a b [] [] [] signOut
    ((s.carry::sum).reverse ++ out)
  simp only [hS, Bool.false_eq_true, ite_false] at h1 h2 h3
  have h3' : run (ba.length+1)
      (cfg (some .dropBA) s' signA signB a b [] ba (s.carry::sum) signOut out) =
      cfg (some .moveSum) s' signA signB a b [] [] (s.carry::sum) signOut out := by
    simpa [s', hS] using h3
  have h : run (1 + (ab.length+1) + (ba.length+1) +
        ((s.carry::sum).length+1) + 2)
      (cfg (some .choose) s signA signB a b ab ba sum signOut out) =
      cfg none initial signA signB a b [] [] []
        (if outputNegative s then true::signOut else signOut)
        ((s.carry::sum).reverse ++ out) := by
    exact chain5 _ _ _ _ _ _ 1 (ab.length+1) (ba.length+1)
      ((s.carry::sum).length+1) 2 h1 h2 h3' h4
        (by simpa [s', outputNegative] using h5)
  have ht : ab.length + ba.length + sum.length + 7 =
      1 + (ab.length+1) + (ba.length+1) + ((s.carry::sum).length+1) + 2 := by
    simp; omega
  rw [ht]
  simpa [List.reverse_cons, List.append_assoc] using h

private theorem post_same_no_borrow (s : Control)
    (signA signB a b ab ba sum signOut out : List Bool)
    (hS : (s.negativeA == s.negativeB) = true)
    (hQ : s.borrowAB = false) :
    run (ab.length + ba.length + sum.length + 7)
      (cfg (some .choose) s signA signB a b ab ba sum signOut out) =
    cfg none initial signA signB a b [] [] []
      (if outputNegative s then true :: signOut else signOut)
      (ab.reverse ++ out) := by
  let s' : Control := {s with a := none}
  have h1 := choose_step s signA signB a b ab ba sum signOut out
  have h2 := dropBA_run s signA signB a b ab ba (s.carry::sum) signOut out
  have h3 := dropSum_run s' signA signB a b ab [] (s.carry::sum) signOut out
  have h4 := moveAB_run s' signA signB a b ab [] [] signOut out
  have h5 := finish_run s' signA signB a b [] [] [] signOut
    (ab.reverse ++ out)
  simp only [hS, hQ, ite_true, ite_false] at h1
  simp only [hS, ite_true] at h2
  have h3' : run ((s.carry::sum).length+1)
      (cfg (some .dropSum) s' signA signB a b ab [] (s.carry::sum) signOut out) =
      cfg (some .moveAB) s' signA signB a b ab [] [] signOut out := by
    simpa [s', hS, hQ] using h3
  have h : run (1 + (ba.length+1) +
        ((s.carry::sum).length+1) + (ab.length+1) + 2)
      (cfg (some .choose) s signA signB a b ab ba sum signOut out) =
      cfg none initial signA signB a b [] [] []
        (if outputNegative s then true::signOut else signOut)
        (ab.reverse ++ out) := by
    exact chain5 _ _ _ _ _ _ 1 (ba.length+1)
      ((s.carry::sum).length+1) (ab.length+1) 2 h1 h2 h3' h4
        (by simpa [s', outputNegative] using h5)
  have ht : ab.length + ba.length + sum.length + 7 =
      1 + (ba.length+1) + ((s.carry::sum).length+1) + (ab.length+1) + 2 := by
    simp; omega
  rw [ht]
  exact h

private theorem post_same_borrow (s : Control)
    (signA signB a b ab ba sum signOut out : List Bool)
    (hS : (s.negativeA == s.negativeB) = true)
    (hQ : s.borrowAB = true) :
    run (ab.length + ba.length + sum.length + 7)
      (cfg (some .choose) s signA signB a b ab ba sum signOut out) =
    cfg none initial signA signB a b [] [] []
      (if outputNegative s then true :: signOut else signOut)
      (ba.reverse ++ out) := by
  let s' : Control := {s with a := none}
  have h1 := choose_step s signA signB a b ab ba sum signOut out
  have h2 := dropAB_run s signA signB a b ab ba (s.carry::sum) signOut out
  have h3 := dropSum_run s' signA signB a b [] ba (s.carry::sum) signOut out
  have h4 := moveBA_run s' signA signB a b [] ba [] signOut out
  have h5 := finish_run s' signA signB a b [] [] [] signOut
    (ba.reverse ++ out)
  simp only [hS, hQ, ite_true, ite_false] at h1
  simp only [hS, ite_true] at h2
  have h3' : run ((s.carry::sum).length+1)
      (cfg (some .dropSum) s' signA signB a b [] ba (s.carry::sum) signOut out) =
      cfg (some .moveBA) s' signA signB a b [] ba [] signOut out := by
    simpa [s', hS, hQ] using h3
  have h : run (1 + (ab.length+1) +
        ((s.carry::sum).length+1) + (ba.length+1) + 2)
      (cfg (some .choose) s signA signB a b ab ba sum signOut out) =
      cfg none initial signA signB a b [] [] []
        (if outputNegative s then true::signOut else signOut)
        (ba.reverse ++ out) := by
    exact chain5 _ _ _ _ _ _ 1 (ab.length+1)
      ((s.carry::sum).length+1) (ba.length+1) 2 h1 h2 h3' h4
        (by simpa [s', outputNegative] using h5)
  have ht : ab.length + ba.length + sum.length + 7 =
      1 + (ab.length+1) + ((s.carry::sum).length+1) + (ba.length+1) + 2 := by
    simp; omega
  rw [ht]
  exact h

theorem post_run (s : Control)
    (signA signB a b ab ba sum signOut out : List Bool) :
    run (ab.length + ba.length + sum.length + 7)
      (cfg (some .choose) s signA signB a b ab ba sum signOut out) =
    cfg none initial signA signB a b [] [] []
      (if outputNegative s then true :: signOut else signOut)
      (selectedWord s ab ba sum ++ out) := by
  cases hS : (s.negativeA == s.negativeB) with
  | false => simpa [selectedWord, hS] using
      post_opposite s signA signB a b ab ba sum signOut out hS
  | true =>
      cases hQ : s.borrowAB with
      | false => simpa [selectedWord, hS, hQ] using
          post_same_no_borrow s signA signB a b ab ba sum signOut out hS hQ
      | true => simpa [selectedWord, hS, hQ] using
          post_same_borrow s signA signB a b ab ba sum signOut out hS hQ

private theorem signA_step (S : Bank) :
    advance program ⟨some .signA, initial, S⟩ =
    ⟨some .signB, {initial with negativeA := (S 0).head?.getD false},
      Function.update S 0 (S 0).tail⟩ := by
  simp [advance, TM2.step, TM2.stepAux, program]

private theorem signB_step (S : Bank) (s : Control) :
    advance program ⟨some .signB, s, S⟩ =
    ⟨some .scan, {s with negativeB := (S 1).head?.getD false},
      Function.update S 1 (S 1).tail⟩ := by
  simp [advance, TM2.step, TM2.stepAux, program]

theorem scanWords_lengths (a b : List Bool) (q r c : Bool) :
    let t := scanWords a b q r c
    t.ab.length = max a.length b.length ∧
    t.ba.length = max a.length b.length ∧
    t.sum.length = max a.length b.length := by
  have h := scanWords_spec a b q r c
  have h1 := BitMachineBinaryDivision.subAny_length a b q
  have h2 := BitMachineBinaryDivision.subAny_length b a r
  have h3 := BitMachineBinaryAddAny.addAny_length a b c
  have ha := congrArg (fun v : List Bool × Bool => v.1.length) h.1
  have hb := congrArg (fun v : List Bool × Bool => v.1.length) h.2.1
  have hc := congrArg List.length h.2.2
  simp only [List.length_append, List.length_singleton] at hc
  simp only [h1] at ha
  simp only [h2, Nat.max_comm] at hb
  omega

private theorem signs_run (signA signB a b ab ba sum signOut out : List Bool) :
    run 2 (cfg (some .signA) initial
      signA signB a b ab ba sum signOut out) =
    cfg (some .scan)
      (scanState (signA.head?.getD false) (signB.head?.getD false)
        false false false)
      signA.tail signB.tail a b ab ba sum signOut out := by
  simp [run, advance, TM2.step, TM2.stepAux, program,
    cfg, contents, scanState, initial]
  funext k; fin_cases k <;> simp [contents]

def finalBank (S : Bank) : Bank :=
  let t := scanWords (S 2) (S 3) false false false
  let s := scanState ((S 0).head?.getD false) ((S 1).head?.getD false)
    t.borrowAB t.borrowBA t.carry
  contents (S 0).tail (S 1).tail [] [] [] [] []
    (if outputNegative s then true :: S 7 else S 7)
    (selectedWord s (t.ab.reverse ++ S 4) (t.ba.reverse ++ S 5)
      (t.sum.reverse ++ S 6) ++ S 8)

def localTime (S : Bank) : ℕ :=
  let t := scanWords (S 2) (S 3) false false false
  2 + (max (S 2).length (S 3).length + 1) +
    ((t.ab.reverse ++ S 4).length +
      (t.ba.reverse ++ S 5).length +
      (t.sum.reverse ++ S 6).length + 7)

private theorem physical_run_words
    (signA signB a b ab ba sum signOut out : List Bool) :
    let t := scanWords a b false false false
    let s := scanState (signA.head?.getD false) (signB.head?.getD false)
      t.borrowAB t.borrowBA t.carry
    run (2 + (max a.length b.length + 1) +
      ((t.ab.reverse ++ ab).length + (t.ba.reverse ++ ba).length +
        (t.sum.reverse ++ sum).length + 7))
      (cfg (some .signA) initial signA signB a b ab ba sum signOut out) =
    cfg none initial signA.tail signB.tail [] [] [] [] []
      (if outputNegative s then true::signOut else signOut)
      (selectedWord s (t.ab.reverse ++ ab) (t.ba.reverse ++ ba)
        (t.sum.reverse ++ sum) ++ out) := by
  let post := (scanWords a b false false false).ab.reverse ++ ab
  let postB := (scanWords a b false false false).ba.reverse ++ ba
  let postC := (scanWords a b false false false).sum.reverse ++ sum
  have hcomp : run (2 + (max a.length b.length + 1) +
      (post.length + postB.length + postC.length + 7))
        (cfg (some .signA) initial signA signB a b ab ba sum signOut out) =
      run (post.length + postB.length + postC.length + 7)
        (run (max a.length b.length + 1)
          (run 2 (cfg (some .signA) initial
            signA signB a b ab ba sum signOut out))) := by
    rw [← run_add, ← run_add]
    simp [Nat.add_assoc]
  dsimp only [post, postB, postC] at hcomp
  dsimp only
  rw [hcomp, signs_run, scan_run, post_run]

theorem local_run (S : Bank) :
    run (localTime S) ⟨some .signA, initial, S⟩ =
      ⟨none, initial, finalBank S⟩ := by
  have h := physical_run_words (S 0) (S 1) (S 2) (S 3)
    (S 4) (S 5) (S 6) (S 7) (S 8)
  have hS : contents (S 0) (S 1) (S 2) (S 3)
      (S 4) (S 5) (S 6) (S 7) (S 8) = S := by
    funext k; fin_cases k <;> rfl
  simpa only [localTime, finalBank, cfg, hS] using h

theorem time_bound (S : Bank) :
    localTime S ≤ 15*((BitMachineBankCodec.encode S).length+1) := by
  let n := (BitMachineBankCodec.encode S).length
  let m := max (S 2).length (S 3).length
  have h2 := BitMachineBankCodec.word_length_le_encode S 2
  have h3 := BitMachineBankCodec.word_length_le_encode S 3
  have h4 := BitMachineBankCodec.word_length_le_encode S 4
  have h5 := BitMachineBankCodec.word_length_le_encode S 5
  have h6 := BitMachineBankCodec.word_length_le_encode S 6
  have hl := scanWords_lengths (S 2) (S 3) false false false
  dsimp only [localTime]
  simp only [List.length_append, List.length_reverse]
  dsimp only at hl
  omega

theorem selected_length_bound (S : Bank) :
    let t := scanWords (S 2) (S 3) false false false
    let s := scanState ((S 0).head?.getD false) ((S 1).head?.getD false)
      t.borrowAB t.borrowBA t.carry
    (selectedWord s (t.ab.reverse ++ S 4) (t.ba.reverse ++ S 5)
      (t.sum.reverse ++ S 6)).length ≤
      2*(BitMachineBankCodec.encode S).length+1 := by
  let n := (BitMachineBankCodec.encode S).length
  have h2 := BitMachineBankCodec.word_length_le_encode S 2
  have h3 := BitMachineBankCodec.word_length_le_encode S 3
  have h4 := BitMachineBankCodec.word_length_le_encode S 4
  have h5 := BitMachineBankCodec.word_length_le_encode S 5
  have h6 := BitMachineBankCodec.word_length_le_encode S 6
  have hl := scanWords_lengths (S 2) (S 3) false false false
  dsimp only at hl
  dsimp only
  unfold selectedWord
  split_ifs <;>
    simp only [List.length_append, List.length_reverse,
      List.length_singleton] <;> omega

theorem output_word_bound (S : Bank) (j : Fin 9) :
    (finalBank S j).length ≤
      5*((BitMachineBankCodec.encode S).length+1) := by
  let n := (BitMachineBankCodec.encode S).length
  have h0 := BitMachineBankCodec.word_length_le_encode S 0
  have h1 := BitMachineBankCodec.word_length_le_encode S 1
  have h7 := BitMachineBankCodec.word_length_le_encode S 7
  have h8 := BitMachineBankCodec.word_length_le_encode S 8
  have hs := selected_length_bound S
  have hsign :
      (if outputNegative
          (scanState ((S 0).head?.getD false) ((S 1).head?.getD false)
            (scanWords (S 2) (S 3) false false false).borrowAB
            (scanWords (S 2) (S 3) false false false).borrowBA
            (scanWords (S 2) (S 3) false false false).carry)
        then true :: S 7 else S 7).length ≤ (S 7).length+1 := by
    split_ifs <;> simp
  fin_cases j <;>
    simp only [finalBank, contents, Matrix.cons_val_zero,
      Matrix.cons_val_one] at * <;>
    simp [finalBank, contents, List.length_append] at * <;>
    omega

theorem size_bound (S : Bank) :
    (BitMachineBankCodec.encode (finalBank S)).length ≤
      100*((BitMachineBankCodec.encode S).length+1) := by
  let n := (BitMachineBankCodec.encode S).length
  have hs : (∑ j : Fin 9, (finalBank S j).length) ≤
      ∑ _j : Fin 9, 5*(n+1) :=
    Finset.sum_le_sum (by intro j _; exact output_word_bound S j)
  rw [BitMachineBankCodec.encode_length]
  simp at hs
  omega

def result (input : List Bool) : List Bool :=
  BitMachineBankWrapper.result finalBank input

noncomputable def machine : BitMachine.Machine :=
  BitMachineBankWrapper.machine program .signA initial

theorem polytime : BitMachine.Polytime result := by
  apply BitMachineBankWrapper.polytime program .signA initial finalBank 15 1 100 1
  · intro S
    refine ⟨localTime S, ⟨none, initial, finalBank S⟩, ?_, ?_, rfl, rfl⟩
    · simpa only [pow_one] using time_bound S
    · exact local_run S
  · intro S
    simpa only [pow_one] using size_bound S

def signedValue (negative : Bool) (magnitude : List Bool) : ℤ :=
  if negative then -(EncodedCommunication.bitsValue magnitude : ℤ)
  else (EncodedCommunication.bitsValue magnitude : ℤ)

theorem scanWords_signed_value (negativeA negativeB : Bool)
    (a b : List Bool) :
    let t := scanWords a b false false false
    let s := scanState negativeA negativeB t.borrowAB t.borrowBA t.carry
    signedValue (outputNegative s)
      (selectedWord s t.ab.reverse t.ba.reverse t.sum.reverse) =
      signedValue negativeA a - signedValue negativeB b := by
  let t := scanWords a b false false false
  let A := EncodedCommunication.bitsValue a
  let B := EncodedCommunication.bitsValue b
  have hs := scanWords_spec a b false false false
  have hA := BitMachineBinaryDivision.subAny_spec a b
  have hB := BitMachineBinaryDivision.subAny_spec b a
  have hAdd := BitMachineBinaryAddAny.addAny_value a b false
  have htAB : (t.ab,t.borrowAB) = BitMachineBinaryDivision.subAny a b false := hs.1
  have htBA : (t.ba,t.borrowBA) = BitMachineBinaryDivision.subAny b a false := hs.2.1
  have hqab : t.borrowAB = decide (A < B) := by
    have h := congrArg Prod.snd htAB
    simpa [A, B] using h.trans hA.1
  have hqba : t.borrowBA = decide (B < A) := by
    have h := congrArg Prod.snd htBA
    simpa [A, B] using h.trans hB.1
  have hsubAB := BitMachineBinaryDivision.subAny_value a b false
  have hsubBA := BitMachineBinaryDivision.subAny_value b a false
  rw [←htAB] at hsubAB
  rw [←htBA] at hsubBA
  simp only [Prod.fst, Prod.snd, Bool.toNat_false, Nat.add_zero] at hsubAB hsubBA
  have hsum : EncodedCommunication.bitsValue (t.sum ++ [t.carry]) = A+B := by
    rw [hs.2.2]
    simpa [A,B] using hAdd
  by_cases hlt : A < B
  · have hq : t.borrowAB = true := by simpa [hlt] using hqab
    have hqr : t.borrowBA = false := by
      rw [hqba]
      simp [show ¬ B < A by omega]
    have hdiffNat : B = A + EncodedCommunication.bitsValue t.ba := by
      simpa [hqr] using hsubBA
    have hdiff : (B : ℤ) = (A : ℤ) +
        (EncodedCommunication.bitsValue t.ba : ℤ) := by exact_mod_cast hdiffNat
    have hsumInt : (EncodedCommunication.bitsValue (t.sum ++ [t.carry]) : ℤ) =
        (A : ℤ) + (B : ℤ) := by exact_mod_cast hsum
    dsimp only [t, A, B] at hq hdiff hsumInt
    dsimp only
    cases negativeA <;> cases negativeB <;>
      simp [signedValue, selectedWord, outputNegative, scanState, hq,
        List.reverse_reverse] <;> omega

  · have hq : t.borrowAB = false := by simpa [hlt] using hqab
    have hdiffNat : A = B + EncodedCommunication.bitsValue t.ab := by
      simpa [hq] using hsubAB
    have hdiff : (A : ℤ) = (B : ℤ) +
        (EncodedCommunication.bitsValue t.ab : ℤ) := by exact_mod_cast hdiffNat
    have hsumInt : (EncodedCommunication.bitsValue (t.sum ++ [t.carry]) : ℤ) =
        (A : ℤ) + (B : ℤ) := by exact_mod_cast hsum
    dsimp only [t, A, B] at hq hdiff hsumInt
    dsimp only
    cases negativeA <;> cases negativeB <;>
      simp [signedValue, selectedWord, outputNegative, scanState, hq,
        List.reverse_reverse] <;> omega

def canonicalInput (negativeA negativeB : Bool) (a b : List Bool) : Bank :=
  contents (if negativeA then [true] else [])
    (if negativeB then [true] else []) a b [] [] [] [] []

private theorem sign_decode (b : Bool) :
    (!(if b then [true] else []).isEmpty) = b := by
  cases b <;> rfl

theorem canonical_output_value (negativeA negativeB : Bool)
    (a b : List Bool) :
    let O := finalBank (canonicalInput negativeA negativeB a b)
    signedValue (!(O 7).isEmpty) (O 8) =
      signedValue negativeA a - signedValue negativeB b := by
  have h := scanWords_signed_value negativeA negativeB a b
  cases negativeA <;> cases negativeB <;>
    simpa [canonicalInput, finalBank, contents,
      List.reverse_nil, List.append_nil, sign_decode] using h

theorem canonical_packet_output (negativeA negativeB : Bool)
    (a b : List Bool) :
    BitMachineBankCodec.decode 9
      (result (BitMachineBankCodec.encode
        (canonicalInput negativeA negativeB a b))) =
      some (finalBank (canonicalInput negativeA negativeB a b)) := by
  simp [result, BitMachineBankWrapper.result]

#print axioms scanWords_signed_value
#print axioms canonical_output_value
#print axioms canonical_packet_output

#print axioms scan_run
#print axioms scanWords_spec
#print axioms post_run
#print axioms local_run
#print axioms polytime

end EthInapproximability.CurrentPaper.SignedMagnitudeSubtract
