import EthInapproximability.CurrentPaper.MatrixUnaryArithmetic

namespace V22UnaryLeaf
open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

inductive Mode where | first | second | sum
  deriving DecidableEq
def wants (m : Mode) (p : Bool) : Bool :=
  match m with | .first => !p | .second => p | .sum => true
def next (p b : Bool) : Bool := p || !b
def count (m : Mode) : List Bool → Bool → ℕ
  | [],_ => 0
  | b::q,p => (if b && wants m p then 1 else 0) + count m q (next p b)
def last : List Bool → Bool → Bool
  | [],p => p
  | b::q,p => last q (next p b)
abbrev Control := Bool × Option Bool
def program (m : Mode) : Unit → TM2.Stmt (fun _ : Fin 2 => Bool) Unit Control
  | () => .pop 0 (fun v b => (v.1,b))
      (.branch (fun v => v.2.isSome)
        (.branch (fun v => v.2.getD false && wants m v.1)
          (.push 1 (fun _ => true)
            (.load (fun v => (next v.1 (v.2.getD false),none)) (.goto fun _ => ())))
          (.load (fun v => (next v.1 (v.2.getD false),none)) (.goto fun _ => ())))
        .halt)
def cfg (l : Option Unit) (p : Bool) (q out : List Bool) :=
  (⟨l,(p,none),![q,out]⟩ : TM2.Cfg (fun _ : Fin 2 => Bool) Unit Control)

private theorem step_cons (m : Mode) (p b : Bool) (q out : List Bool) :
    advance (program m) (cfg (some ()) p (b::q) out) =
      cfg (some ()) (next p b) q
        (List.replicate (if b && wants m p then 1 else 0) true ++ out) := by
  cases p <;> cases b <;> cases m <;>
    simp [advance,program,cfg,wants,next,TM2.step,TM2.stepAux]
  all_goals funext i; fin_cases i <;> rfl

private theorem step_nil (m : Mode) (p : Bool) (out : List Bool) :
    advance (program m) (cfg (some ()) p [] out) = cfg none p [] out := by
  simp [advance,program,cfg,TM2.step,TM2.stepAux]

theorem run (m : Mode) (q out : List Bool) (p : Bool) :
    ((advance (program m))^[q.length+1]) (cfg (some ()) p q out) =
      cfg none (last q p) [] (List.replicate (count m q p) true ++ out) := by
  induction q generalizing p out with
  | nil => simpa [last,count] using step_nil m p out
  | cons b q ih =>
      rw [List.length_cons,Function.iterate_succ_apply,step_cons,ih]
      simp only [last,count]
      rw [←List.append_assoc,List.replicate_append_replicate]
      simp [Nat.add_comm]

theorem count_true (m : Mode) (n : ℕ) (p : Bool) :
    count m (List.replicate n true) p = if wants m p then n else 0 := by
  induction n with
  | zero => simp [count]
  | succ n ih =>
      simp only [List.replicate_succ,count,next,Bool.not_true,Bool.or_false,ih]
      cases wants m p <;> simp [Nat.add_comm]

theorem count_append (m : Mode) (a b : List Bool) (p : Bool) :
    count m (a++b) p = count m a p + count m b (last a p) := by
  induction a generalizing p with
  | nil => simp [count,last]
  | cons x a ih => simp [count,last,ih,Nat.add_assoc]
theorem last_true (n : ℕ) (p : Bool) : last (List.replicate n true) p = p := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ,last,next] using ih

def value (m : Mode) (a b : ℕ) :=
  match m with | .first => a | .second => b | .sum => a+b
theorem count_pair (m : Mode) (a b : ℕ) :
    count m (MatrixUnaryArithmetic.encodeInput a b) false = value m a b := by
  simp only [MatrixUnaryArithmetic.encodeInput,count_append,count_true,last_true,count,next]
  cases m <;> simp [wants,value]

noncomputable def machine (m : Mode) : BitMachine.Machine :=
  ofFinite (0 : Fin 2) 1 () (false,none) (program m)
theorem outputs (m : Mode) (a b : ℕ) :
    (machine m).OutputsWithin (MatrixUnaryArithmetic.encodeInput a b)
      (List.replicate (value m a b) true) (a+b+2) := by
  have hi : rawInit (0 : Fin 2) () (false,none) (MatrixUnaryArithmetic.encodeInput a b) =
    cfg (some ()) false (MatrixUnaryArithmetic.encodeInput a b) [] := by
    unfold rawInit cfg; congr 1; funext i; fin_cases i <;> rfl
  have hr := run m (MatrixUnaryArithmetic.encodeInput a b) [] false
  have hlen : (MatrixUnaryArithmetic.encodeInput a b).length+1=a+b+2 := by
    simp [MatrixUnaryArithmetic.encodeInput]; omega
  rw [hlen] at hr
  apply outputsWithin_of_raw_run (0 : Fin 2) 1 () (false,none) (program m) _ _
    (a+b+2) (a+b+2) (by omega)
  · rw [hi]; have h := congrArg TM2.Cfg.l hr; simpa [cfg] using h
  · rw [hi]; have h := congrArg (fun c => c.stk (1 : Fin 2)) hr
    simpa only [cfg, Matrix.cons_val_one, Matrix.cons_val_zero, List.append_nil, count_pair] using h

def pushN : ℕ → TM2.Stmt (fun _ : Fin 2 => Bool) Unit Unit
  | 0 => .halt
  | n+1 => .push 1 (fun _ => true) (pushN n)
private theorem pushN_aux (n : ℕ) (S : Fin 2 → List Bool) :
    TM2.stepAux (pushN n) () S =
      ⟨none,(),Function.update S 1 (List.replicate n true ++ S 1)⟩ := by
  induction n generalizing S with
  | zero => simp [pushN,TM2.stepAux]
  | succ n ih =>
      simp only [pushN,TM2.stepAux,ih,Function.update_self,Function.update_idem]
      congr 1
      simp only [List.replicate_succ',List.append_assoc,List.cons_append,List.nil_append]
noncomputable def constant (n : ℕ) : BitMachine.Machine :=
  ofFinite (0 : Fin 2) 1 () () (fun _ => pushN n)
theorem constant_outputs (n : ℕ) (input : List Bool) :
    (constant n).OutputsWithin input (List.replicate n true) 1 := by
  apply outputsWithin_of_raw_run (0 : Fin 2) 1 () () (fun _ => pushN n)
    input _ 1 1 (by omega)
  · simp [Function.iterate_succ_apply,advance,rawInit,TM2.step,pushN_aux]
  · simp [Function.iterate_succ_apply,advance,rawInit,TM2.step,pushN_aux]

#print axioms outputs
#print axioms constant_outputs
end V22UnaryLeaf
