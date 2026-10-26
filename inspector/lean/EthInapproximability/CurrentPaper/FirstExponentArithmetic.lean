import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.BitMachineStackRun
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import Mathlib.Tactic

/-! A fixed finite program for unary `256*s*s`, preserving the source word. -/

namespace EthInapproximability.CurrentPaper.FirstExponentArithmetic

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineStackEmbedding

set_option maxRecDepth 4096

abbrev Stack := Fin 4

def copySlots : Fin 3 ↪ Stack := ⟨![0,1,3], by decide⟩
def copyProgram := MatrixStage4ScalarPreparationOps.copyProgram copySlots

inductive MulLabel where
  | outer | scan | restore
  deriving DecidableEq, Fintype

def pushMany : ℕ → TM2.Stmt (fun _ : Stack => Bool) MulLabel Bool →
    TM2.Stmt (fun _ : Stack => Bool) MulLabel Bool
  | 0, q => q
  | n+1, q => push 2 (fun _ => true) (pushMany n q)

def mulProgram : MulLabel → TM2.Stmt (fun _ : Stack => Bool) MulLabel Bool
  | .outer => pop 1 (fun _ b => b.isSome)
      (branch id (goto (fun _ => .scan)) (load (fun _ => false) halt))
  | .scan => pop 0 (fun _ b => b.isSome)
      (branch id (pushMany 256 (push 3 (fun _ => true) (goto (fun _ => .scan))))
        (goto (fun _ => .restore)))
  | .restore => pop 3 (fun _ b => b.isSome)
      (branch id (push 0 (fun _ => true) (goto (fun _ => .restore)))
        (goto (fun _ => .outer)))

def cfg (l : Option MulLabel) (b : Bool) (src counter out scratch : List Bool) :
    TM2.Cfg (fun _ : Stack => Bool) MulLabel Bool :=
  ⟨l,b,![src,counter,out,scratch]⟩

def run (t : ℕ) (c : TM2.Cfg (fun _ : Stack => Bool) MulLabel Bool) :=
  ((advance mulProgram)^[t]) c

private theorem replicate_commute (n : ℕ) (l : List Bool) :
    List.replicate n true ++ true :: l = true :: (List.replicate n true ++ l) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ] using congrArg (List.cons true) ih

theorem run_add (m n : ℕ) (c : TM2.Cfg (fun _ : Stack => Bool) MulLabel Bool) :
    run (m+n) c = run n (run m c) := by
  simpa only [run, Nat.add_comm] using Function.iterate_add_apply (advance mulProgram) n m c

private theorem pushMany_stepAux (n : ℕ) (q : TM2.Stmt (fun _ : Stack => Bool) MulLabel Bool)
    (b : Bool) (S : Stack → List Bool) :
    TM2.stepAux (pushMany n q) b S =
      TM2.stepAux q b (Function.update S 2 (List.replicate n true ++ S 2)) := by
  induction n generalizing S with
  | zero => simp [pushMany]
  | succ n ih =>
      simp only [pushMany, TM2.stepAux]
      rw [ih]
      congr 1
      funext k
      fin_cases k <;> simp [Function.update, List.replicate_succ, List.cons_append,
        replicate_commute]

private theorem outer_cons (s : Bool) (src counter out : List Bool) :
    advance mulProgram (cfg (some .outer) s src (true::counter) out []) =
      cfg (some .scan) true src counter out [] := by
  simp [advance, mulProgram, cfg, TM2.step, TM2.stepAux]
  funext k
  fin_cases k <;> rfl

private theorem outer_nil (s : Bool) (src out : List Bool) :
    advance mulProgram (cfg (some .outer) s src [] out []) =
      cfg none false src [] out [] := by
  simp [advance, mulProgram, cfg, TM2.step, TM2.stepAux]

private theorem scan_cons (s : Bool) (src counter out scratch : List Bool) :
    advance mulProgram (cfg (some .scan) s (true::src) counter out scratch) =
      cfg (some .scan) true src counter (List.replicate 256 true ++ out)
        (true::scratch) := by
  simp only [advance, TM2.step, mulProgram, cfg, TM2.stepAux]
  rw [pushMany_stepAux]
  simp only [TM2.stepAux]
  simp only [Matrix.cons_val_zero, List.head?_cons, Option.isSome_some,
    List.tail_cons, Option.getD_some]
  simp only [id_eq, cond_true]
  congr 1
  funext k
  fin_cases k <;> simp [Function.update]

private theorem scan_nil (s : Bool) (counter out scratch : List Bool) :
    advance mulProgram (cfg (some .scan) s [] counter out scratch) =
      cfg (some .restore) false [] counter out scratch := by
  simp [advance, mulProgram, cfg, TM2.step, TM2.stepAux]

private theorem restore_cons (s : Bool) (src counter out scratch : List Bool) :
    advance mulProgram (cfg (some .restore) s src counter out (true::scratch)) =
      cfg (some .restore) true (true::src) counter out scratch := by
  simp [advance, mulProgram, cfg, TM2.step, TM2.stepAux]
  funext k
  fin_cases k <;> rfl

private theorem restore_nil (s : Bool) (src counter out : List Bool) :
    advance mulProgram (cfg (some .restore) s src counter out []) =
      cfg (some .outer) false src counter out [] := by
  simp [advance, mulProgram, cfg, TM2.step, TM2.stepAux]

private theorem scan_run (n : ℕ) (counter out scratch : List Bool) (s : Bool) :
    run (n+1) (cfg (some .scan) s (List.replicate n true) counter out scratch) =
      cfg (some .restore) false [] counter
        (List.replicate (256*n) true ++ out)
        (List.replicate n true ++ scratch) := by
  induction n generalizing s out scratch with
  | zero => simpa [run] using scan_nil s counter out scratch
  | succ n ih =>
      rw [run, Function.iterate_succ_apply]
      rw [List.replicate_succ, scan_cons]
      have h := ih (List.replicate 256 true ++ out) (true::scratch) true
      have he : 256 * (n+1) = 256*n+256 := by omega
      have ho : List.replicate (256*n) true ++
          (List.replicate 256 true ++ out) =
          List.replicate (256*(n+1)) true ++ out := by
        rw [he, List.replicate_add, List.append_assoc]
      have hs : List.replicate n true ++ true :: scratch =
          List.replicate (n+1) true ++ scratch := by
        rw [replicate_commute, List.replicate_succ]
        rfl
      rw [ho, hs] at h
      simpa only [run] using h

private theorem restore_run (n m : ℕ) (counter out : List Bool) (s : Bool) :
    run (n+1) (cfg (some .restore) s (List.replicate m true)
      counter out (List.replicate n true)) =
      cfg (some .outer) false (List.replicate (n+m) true) counter out [] := by
  induction n generalizing s m with
  | zero => simpa [run] using restore_nil s (List.replicate m true) counter out
  | succ n ih =>
      rw [run, Function.iterate_succ_apply, List.replicate_succ, restore_cons]
      simpa [run, List.replicate_succ, Nat.add_assoc, Nat.add_comm 1 m] using ih (m+1) true

theorem mul_run (s outer out : ℕ) (b : Bool) :
    run (outer*(2*s+3)+1)
      (cfg (some .outer) b (List.replicate s true)
        (List.replicate outer true) (List.replicate out true) []) =
      cfg none false (List.replicate s true) []
        (List.replicate (256*s*outer+out) true) [] := by
  induction outer generalizing b out with
  | zero => simpa [run] using outer_nil b (List.replicate s true) (List.replicate out true)
  | succ outer ih =>
      have h1 := outer_cons b (List.replicate s true)
        (List.replicate outer true) (List.replicate out true)
      have h2 := scan_run s (List.replicate outer true) (List.replicate out true) [] true
      have h3 := restore_run s 0 (List.replicate outer true)
        (List.replicate (256*s) true ++ List.replicate out true) false
      have h4 := ih (256*s+out) false
      have h12 : run (1+(s+1))
          (cfg (some .outer) b (List.replicate s true)
            (List.replicate (outer+1) true) (List.replicate out true) []) =
          cfg (some .restore) false [] (List.replicate outer true)
            (List.replicate (256*s) true ++ List.replicate out true)
            (List.replicate s true) := by
        rw [run_add, show run 1
          (cfg (some .outer) b (List.replicate s true)
            (List.replicate (outer+1) true) (List.replicate out true) []) = _
          from (by simpa only [run, List.replicate_succ] using h1)]
        simpa only [List.append_nil] using h2
      have h123 : run (1+(s+1)+(s+1))
          (cfg (some .outer) b (List.replicate s true)
            (List.replicate (outer+1) true) (List.replicate out true) []) =
          cfg (some .outer) false (List.replicate s true)
            (List.replicate outer true)
            (List.replicate (256*s) true ++ List.replicate out true) [] := by
        rw [run_add, h12]
        simpa using h3
      have htime : (outer+1)*(2*s+3)+1 =
          1+(s+1)+(s+1)+(outer*(2*s+3)+1) := by ring
      rw [htime]
      rw [run_add, h123]
      have hsource : List.replicate (256*s) true ++ List.replicate out true =
          List.replicate (256*s+out) true := by rw [← List.replicate_add]
      rw [hsource, h4]
      congr 1
      congr 1
      ring

abbrev Label := BitMachineRawSequence.Label BitMachineCopy.Label MulLabel
abbrev Control := Option Bool × Bool

def program := BitMachineRawSequence.program copyProgram mulProgram
  MulLabel.outer (none : Option Bool) false

def initialBank (s : ℕ) : Stack → List Bool :=
  ![List.replicate s true, [], [], []]

def finalBank (s : ℕ) : Stack → List Bool :=
  ![List.replicate s true, [], List.replicate (256*s^2) true, []]

def bound (s : ℕ) : ℕ :=
  (2*s+2) + (s*(2*s+3)+1) + 1

theorem exact_run (s : ℕ) :
    ∃ t ≤ bound s,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none,false),initialBank s⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
        ⟨none,(none,false),finalBank s⟩ := by
  let S := initialBank s
  let T := Function.update S 1 (List.replicate s true)
  have hc : ((advance copyProgram)^[2*s+2])
      (⟨some BitMachineCopy.Label.scan,none,S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none,none,T⟩ := by
    have he := MatrixStage4ScalarPreparationOps.copy_run copySlots S
      (show S (copySlots 2) = [] by rfl)
    simpa [copyProgram, S, T, initialBank, copySlots] using he
  have hm : ((advance mulProgram)^[s*(2*s+3)+1])
      (⟨some MulLabel.outer,false,T⟩ :
        TM2.Cfg (fun _ : Stack => Bool) MulLabel Bool) =
      ⟨none,false,finalBank s⟩ := by
    have he := mul_run s s 0 false
    change ((advance mulProgram)^[s*(2*s+3)+1]) _ = _ at he
    have hT : T = ![List.replicate s true, List.replicate s true, [], []] := by
      funext k
      fin_cases k <;> simp [T, S, initialBank]
    rw [hT]
    simpa [finalBank, cfg, pow_two,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using he
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    copyProgram mulProgram BitMachineCopy.Label.scan MulLabel.outer
    (none : Option Bool) none false false S T (finalBank s)
    (2*s+2) (s*(2*s+3)+1) hc hm
  exact ⟨t, by simpa [bound] using ht, by simpa only [program, S] using hr⟩

#print axioms mul_run
#print axioms exact_run

end EthInapproximability.CurrentPaper.FirstExponentArithmetic
