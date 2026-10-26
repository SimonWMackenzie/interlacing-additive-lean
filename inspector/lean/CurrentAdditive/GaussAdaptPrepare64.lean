import CurrentAdditive.CodeDCanonicalSource
import EthInapproximability.CurrentPaper.BitMachineClearBank

/-! Literal adaptation of the two arithmetic operands and request flag. -/

namespace CurrentAdditive.GaussAdaptPrepare64

open Turing EthInapproximability.CurrentPaper BitMachineEncoding

abbrev Stack := Fin 64
abbrev Control := Unit × Option Bool

def zeroWord : List Bool :=
  CodeDCodec.encodeRawRat (CodeDCanonicalSource.rawOfRat (0 : ℚ))

def minusOneWord : List Bool :=
  CodeDCodec.encodeRawRat (CodeDCanonicalSource.rawOfRat (-1 : ℚ))

inductive Label where
  | start | clear24 | clear25 | write | done
  deriving DecidableEq, Fintype

def pushWord (bank : Stack) : List Bool →
    TM2.Stmt (fun _ : Stack => Bool) Label Control →
    TM2.Stmt (fun _ : Stack => Bool) Label Control
  | [], q => q
  | b :: bs, q => .push bank (fun _ => b) (pushWord bank bs q)

theorem pushWord_step (bank : Stack) (word : List Bool)
    (q : TM2.Stmt (fun _ : Stack => Bool) Label Control)
    (v : Control) (S : Stack → List Bool) :
    TM2.stepAux (pushWord bank word q) v S =
      TM2.stepAux q v
        (Function.update S bank (word.reverse ++ S bank)) := by
  induction word generalizing S with
  | nil => simp [pushWord]
  | cons b bs ih =>
      simp only [pushWord, TM2.stepAux]
      rw [ih]
      congr 1
      funext k
      by_cases hk : k = bank
      · subst k
        simp [Function.update_apply, List.reverse_cons,
          List.append_assoc]
      · simp [Function.update_apply, hk]

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .start => .peek 28 (fun _ b => ((), b))
      (.branch (fun v => v.2.getD false)
        (.load (fun _ => ((), none)) (.goto (fun _ => .clear24)))
        (.load (fun _ => ((), none)) (.goto (fun _ => .done))))
  | .clear24 => BitMachineClearBank.clearStep 24 .clear24 .clear25
  | .clear25 => BitMachineClearBank.clearStep 25 .clear25 .write
  | .write => .pop 28 (fun _ _ => ((), none))
      (.push 28 (fun _ => false)
        (pushWord 24 zeroWord.reverse
          (pushWord 25 minusOneWord.reverse (.goto (fun _ => .done)))))
  | .done => .halt

def prepared (S : Stack → List Bool) (flag : Bool) : Stack → List Bool :=
  if flag then
    Function.update (Function.update (Function.update S 24 zeroWord)
      25 minusOneWord) 28 [false]
  else S

theorem start_step (S : Stack → List Bool) (flag : Bool)
    (hflag : S 28 = [flag]) :
    advance program
      (⟨some .start, ((), none), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨some (if flag then .clear24 else .done), ((), none), S⟩ := by
  cases flag <;> simp [advance, TM2.step, program, TM2.stepAux, hflag]

theorem clear24_run (S : Stack → List Bool) :
    ((advance program)^[(S 24).length + 1])
      (⟨some .clear24, ((), none), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨some .clear25, ((), none), Function.update S 24 []⟩ :=
  BitMachineClearBank.clear_one_run program 24 .clear24 .clear25 rfl () S

theorem clear25_run (S : Stack → List Bool) :
    ((advance program)^[(S 25).length + 1])
      (⟨some .clear25, ((), none), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨some .write, ((), none), Function.update S 25 []⟩ :=
  BitMachineClearBank.clear_one_run program 25 .clear25 .write rfl () S

theorem write_step (S : Stack → List Bool)
    (h24 : S 24 = []) (h25 : S 25 = [])
    (h28 : S 28 = [true]) :
    advance program
      (⟨some .write, ((), none), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨some .done, ((), none),
        Function.update (Function.update (Function.update S 24 zeroWord)
          25 minusOneWord) 28 [false]⟩ := by
  simp only [advance, TM2.step, program, TM2.stepAux,
    h28, List.head?_cons, List.tail_cons]
  rw [pushWord_step, pushWord_step]
  simp only [TM2.stepAux, Option.getD_some, List.reverse_reverse]
  congr 1
  funext k
  by_cases h24k : k = 24
  · subst k
    simp [Function.update_apply, h24]
  · by_cases h25k : k = 25
    · subst k
      simp [Function.update_apply, h25]
    · by_cases h28k : k = 28
      · subst k
        simp [Function.update_apply]
      · simp [Function.update_apply, h24k, h25k, h28k]

theorem done_step (S : Stack → List Bool) :
    advance program
      (⟨some .done, ((), none), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨none, ((), none), S⟩ := rfl

private theorem join_run {α : Type*} (f : α → α)
    (a b c : α) (m n : ℕ)
    (hab : (f^[m]) a = b) (hbc : (f^[n]) b = c) :
    (f^[m+n]) a = c := by
  rw [show m + n = n + m by omega, Function.iterate_add_apply, hab, hbc]

theorem run_false (S : Stack → List Bool) (hflag : S 28 = [false]) :
    ((advance program)^[2])
      (⟨some .start, ((), none), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨none, ((), none), S⟩ := by
  have h1 := start_step S false hflag
  simpa only [ite_false, Function.iterate_succ_apply',
    Function.iterate_zero, id_eq, h1] using done_step S

theorem run_true (S : Stack → List Bool)
    (current column : List Bool)
    (hflag : S 28 = [true])
    (hcurrent : S 24 = current) (hcolumn : S 25 = column) :
    ((advance program)^[current.length + column.length + 5])
      (⟨some .start, ((), none), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨none, ((), none), prepared S true⟩ := by
  let S1 := Function.update S 24 []
  let S2 := Function.update S1 25 []
  let S3 := Function.update
    (Function.update (Function.update S2 24 zeroWord)
      25 minusOneWord) 28 [false]
  have h1 := start_step S true hflag
  have h2 := clear24_run S
  have hS1col : S1 25 = column := by simp [S1, hcolumn]
  have h3 := clear25_run S1
  rw [hS1col] at h3
  have hS2_24 : S2 24 = [] := by simp [S2, S1]
  have hS2_25 : S2 25 = [] := by simp [S2]
  have hS2_28 : S2 28 = [true] := by simp [S2, S1, hflag]
  have h4 := write_step S2 hS2_24 hS2_25 hS2_28
  have h5 := done_step S3
  have h1' : ((advance program)^[1])
      (⟨some .start, ((), none), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨some .clear24, ((), none), S⟩ := by simpa using h1
  have h4' : ((advance program)^[1])
      (⟨some .write, ((), none), S2⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨some .done, ((), none), S3⟩ := by simpa only [S3] using h4
  have h5' : ((advance program)^[1])
      (⟨some .done, ((), none), S3⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨none, ((), none), S3⟩ := by simpa using h5
  have h12 := join_run (advance program) _ _ _ 1
    (current.length+1) h1' (by simpa only [hcurrent, S1] using h2)
  have h123 := join_run (advance program) _ _ _
    (1+(current.length+1)) (column.length+1) h12
    (by simpa only [S2] using h3)
  have h1234 := join_run (advance program) _ _ _
    (1+(current.length+1)+(column.length+1)) 1 h123 h4'
  have h12345 := join_run (advance program) _ _ _
    (1+(current.length+1)+(column.length+1)+1) 1 h1234 h5'
  have hfinal : S3 = prepared S true := by
    funext k
    by_cases hk24 : k = 24
    · subst k; simp [S3, S2, S1, prepared]
    · by_cases hk25 : k = 25
      · subst k; simp [S3, S2, S1, prepared]
      · by_cases hk28 : k = 28
        · subst k; simp [S3, S2, S1, prepared]
        · simp [S3, S2, S1, prepared, hk24, hk25, hk28]
  rw [show current.length + column.length + 5 =
      1+(current.length+1)+(column.length+1)+1+1 by omega]
  simpa only [hfinal] using h12345

def time (flag : Bool) (current column : List Bool) : ℕ :=
  if flag then current.length + column.length + 5 else 2

theorem run (S : Stack → List Bool) (flag : Bool)
    (current column : List Bool)
    (hflag : S 28 = [flag])
    (hcurrent : S 24 = current) (hcolumn : S 25 = column) :
    ((advance program)^[time flag current column])
      (⟨some .start, ((), none), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨none, ((), none), prepared S flag⟩ := by
  cases flag
  · simpa [time, prepared] using run_false S hflag
  · simpa [time] using run_true S current column hflag hcurrent hcolumn

#print axioms pushWord_step
#print axioms write_step
#print axioms run

end CurrentAdditive.GaussAdaptPrepare64
