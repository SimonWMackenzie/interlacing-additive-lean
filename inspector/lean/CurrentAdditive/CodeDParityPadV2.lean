import CurrentAdditive.RationalProductSignedPhysical
import EthInapproximability.CurrentPaper.BitMachineEncoding

/-!
Physical high-zero padding of a little-endian unsigned word so its length
parity equals a desired sign bit. The desired bit is the first input cell;
the remaining cells are the magnitude word. This is one component of the
nested RawRat-pair to signed-product packet router.
-/

namespace CurrentAdditive.CodeDParityPadV2

open Turing TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open RationalProductSignedPhysical
open RationalProductSignedRepack

inductive Label where
  | read | scan | choose | pad | restore
  deriving DecidableEq, Fintype

structure Control where
  desired : Bool
  parity : Bool
  bit : Option Bool
  deriving DecidableEq, Fintype

def initial : Control := ⟨false, false, none⟩

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label Control
  | .read => pop 0 (fun s b => {s with bit := b})
      (branch (fun s => s.bit.isSome)
        (load (fun s => ⟨s.bit.getD false, false, none⟩)
          (goto (fun _ => .scan))) halt)
  | .scan => pop 0 (fun s b => ⟨s.desired, if b.isSome then !s.parity else s.parity, b⟩)
      (branch (fun s => s.bit.isSome)
        (push 1 (fun s => s.bit.getD false) (goto (fun _ => .scan)))
        (goto (fun _ => .choose)))
  | .choose => branch (fun s => s.parity != s.desired)
      (goto (fun _ => .pad)) (goto (fun _ => .restore))
  | .pad => push 2 (fun _ => false) (goto (fun _ => .restore))
  | .restore => pop 1 (fun s b => {s with bit := b})
      (branch (fun s => s.bit.isSome)
        (push 2 (fun s => s.bit.getD false) (goto (fun _ => .restore))) halt)

def cfg (l : Option Label) (s : Control)
    (input saved output : List Bool) :
    TM2.Cfg (fun _ : Fin 3 => Bool) Label Control :=
  ⟨l, s, ![input, saved, output]⟩

def run (n : Nat) (c : TM2.Cfg (fun _ : Fin 3 => Bool) Label Control) :=
  ((advance program)^[n]) c

theorem run_succ (n : Nat) (c : TM2.Cfg (fun _ : Fin 3 => Bool) Label Control) :
    run (n+1) c = run n (advance program c) := by
  simp only [run, Function.iterate_succ_apply]

theorem run_add (n m : Nat) (c : TM2.Cfg (fun _ : Fin 3 => Bool) Label Control) :
    run (n+m) c = run m (run n c) := by
  simp only [run, Nat.add_comm n m, Function.iterate_add_apply]

theorem read_good (desired : Bool) (word : List Bool) :
    advance program (cfg (some .read) initial (desired :: word) [] []) =
      cfg (some .scan) ⟨desired, false, none⟩ word [] [] := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux, initial]
  funext k; fin_cases k <;> rfl

theorem read_bad :
    advance program (cfg (some .read) initial [] [] []) =
      cfg none ⟨false, false, none⟩ [] [] [] := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux, initial]

theorem scan_cons (s : Control) (b : Bool) (rest saved out : List Bool) :
    advance program (cfg (some .scan) s (b :: rest) saved out) =
      cfg (some .scan) ⟨s.desired, !s.parity, some b⟩ rest (b :: saved) out := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]
  funext k; fin_cases k <;> rfl

theorem scan_nil (s : Control) (saved out : List Bool) :
    advance program (cfg (some .scan) s [] saved out) =
      cfg (some .choose) ⟨s.desired, s.parity, none⟩ [] saved out := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]

theorem scan_run (s : Control) (word saved out : List Bool) :
    run (word.length+1) (cfg (some .scan) s word saved out) =
      cfg (some .choose)
        ⟨s.desired, s.parity != signParity word, none⟩
        [] (word.reverse ++ saved) out := by
  induction word generalizing s saved with
  | nil =>
      simpa [run, signParity] using scan_nil s saved out
  | cons b rest ih =>
      rw [List.length_cons,
        show rest.length+1+1 = (rest.length+1)+1 by omega,
        run_succ, scan_cons]
      simpa [signParity, List.reverse_cons, Bool.xor_assoc] using
        ih ⟨s.desired, !s.parity, some b⟩ (b :: saved)

theorem choose_same (s : Control) (saved out : List Bool)
    (h : s.parity = s.desired) :
    advance program (cfg (some .choose) s [] saved out) =
      cfg (some .restore) s [] saved out := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux, h]

theorem choose_diff (s : Control) (saved out : List Bool)
    (h : s.parity ≠ s.desired) :
    advance program (cfg (some .choose) s [] saved out) =
      cfg (some .pad) s [] saved out := by
  cases hp : s.parity <;> cases hd : s.desired <;>
    simp_all [advance, program, cfg, TM2.step, TM2.stepAux]

theorem pad_step (s : Control) (saved out : List Bool) :
    advance program (cfg (some .pad) s [] saved out) =
      cfg (some .restore) s [] saved (false :: out) := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]
  funext k; fin_cases k <;> rfl

theorem restore_cons (s : Control) (b : Bool) (rest out : List Bool) :
    advance program (cfg (some .restore) s [] (b :: rest) out) =
      cfg (some .restore) {s with bit := some b} [] rest (b :: out) := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]
  funext k; fin_cases k <;> rfl

theorem restore_nil (s : Control) (out : List Bool) :
    advance program (cfg (some .restore) s [] [] out) =
      cfg none {s with bit := none} [] [] out := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]

theorem restore_run (s : Control) (saved out : List Bool) :
    run (saved.length+1) (cfg (some .restore) s [] saved out) =
      cfg none {s with bit := none} [] [] (saved.reverse ++ out) := by
  induction saved generalizing s out with
  | nil => simpa [run] using restore_nil s out
  | cons b rest ih =>
      rw [List.length_cons,
        show rest.length+1+1 = (rest.length+1)+1 by omega,
        run_succ, restore_cons]
      simpa [List.reverse_cons, List.append_assoc] using
        ih {s with bit := some b} (b :: out)

theorem scan_from_initial (desired : Bool) (word : List Bool) :
    run (word.length+1) (cfg (some .scan) ⟨desired, false, none⟩ word [] []) =
      cfg (some .choose) ⟨desired, signParity word, none⟩ [] word.reverse [] := by
  simpa [Bool.false_bne] using
    scan_run ⟨desired, false, none⟩ word [] []

theorem valid_run (desired : Bool) (word : List Bool) :
    ∃ t ≤ 2*word.length+5,
      (run t (cfg (some .read) initial (desired :: word) [] [])).l = none ∧
      (run t (cfg (some .read) initial (desired :: word) [] [])).stk 2 =
        parityPad word desired := by
  let c₀ := cfg (some .read) initial (desired :: word) [] []
  let c₁ := cfg (some .scan) ⟨desired, false, none⟩ word [] []
  let c₂ := cfg (some .choose) ⟨desired, signParity word, none⟩ [] word.reverse []
  have h₀ : run 1 c₀ = c₁ := by simpa [c₀, c₁, run] using read_good desired word
  have h₁ : run (word.length+1) c₁ = c₂ := by
    simpa [c₁, c₂] using scan_from_initial desired word
  by_cases h : signParity word = desired
  · let c₃ := cfg (some .restore) ⟨desired, signParity word, none⟩ [] word.reverse []
    have h₂ : run 1 c₂ = c₃ := by
      simpa [c₂, c₃, run] using
        choose_same ⟨desired, signParity word, none⟩ word.reverse [] h
    have h₃ := restore_run ⟨desired, signParity word, none⟩ word.reverse []
    simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h₃
    have h₀₁ : run (1+(word.length+1)) c₀ = c₂ := by
      rw [run_add, h₀, h₁]
    have h₀₂ : run (1+(word.length+1)+1) c₀ = c₃ := by
      rw [run_add, h₀₁, h₂]
    have hrun : run (2*word.length+4) c₀ =
        cfg none ⟨desired, signParity word, none⟩ [] [] word := by
      rw [show 2*word.length+4 =
        (1+(word.length+1)+1)+(word.length+1) by omega,
        run_add, h₀₂]
      simpa [c₃] using h₃
    refine ⟨2*word.length+4, by omega, ?_, ?_⟩
    · change (run (2*word.length+4) c₀).l = none
      rw [hrun]
      rfl
    · change (run (2*word.length+4) c₀).stk 2 = parityPad word desired
      rw [hrun]
      simp [cfg, parityPad, h]
  · let c₃ := cfg (some .pad) ⟨desired, signParity word, none⟩ [] word.reverse []
    let c₄ := cfg (some .restore) ⟨desired, signParity word, none⟩ [] word.reverse [false]
    have h₂ : run 1 c₂ = c₃ := by
      simpa [c₂, c₃, run] using
        choose_diff ⟨desired, signParity word, none⟩ word.reverse [] h
    have h₃ : run 1 c₃ = c₄ := by
      simpa [c₃, c₄, run] using
        pad_step ⟨desired, signParity word, none⟩ word.reverse []
    have h₄ := restore_run ⟨desired, signParity word, none⟩ word.reverse [false]
    simp only [List.length_reverse, List.reverse_reverse] at h₄
    have h₀₁ : run (1+(word.length+1)) c₀ = c₂ := by
      rw [run_add, h₀, h₁]
    have h₀₂ : run (1+(word.length+1)+1) c₀ = c₃ := by
      rw [run_add, h₀₁, h₂]
    have h₀₃ : run (1+(word.length+1)+1+1) c₀ = c₄ := by
      rw [run_add, h₀₂, h₃]
    have hrun : run (2*word.length+5) c₀ =
        cfg none ⟨desired, signParity word, none⟩ [] [] (word ++ [false]) := by
      rw [show 2*word.length+5 =
        (1+(word.length+1)+1+1)+(word.length+1) by omega,
        run_add, h₀₃]
      simpa [c₄] using h₄
    refine ⟨2*word.length+5, le_refl _, ?_, ?_⟩
    · change (run (2*word.length+5) c₀).l = none
      rw [hrun]
      rfl
    · change (run (2*word.length+5) c₀).stk 2 = parityPad word desired
      rw [hrun]
      simp [cfg, parityPad, h]

def result : List Bool → List Bool
  | [] => []
  | desired :: word => parityPad word desired

noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Fin 3) 2 .read initial program

theorem outputs (input : List Bool) :
    machine.OutputsWithin input (result input) (2*input.length+5) := by
  have hi : rawInit (0 : Fin 3) Label.read initial input =
      cfg (some .read) initial input [] [] := by
    simp only [rawInit, cfg]
    congr 1
    funext k; fin_cases k <;> rfl
  cases input with
  | nil =>
      apply outputsWithin_of_raw_run (0 : Fin 3) 2 .read initial program
        [] [] 1 5 (by omega)
      · rw [hi]
        simpa [run] using congrArg (fun c => c.l) read_bad
      · rw [hi]
        simpa [run, result, cfg] using
          congrArg (fun c => c.stk (2 : Fin 3)) read_bad
  | cons desired word =>
      obtain ⟨t, ht, hh, ho⟩ := valid_run desired word
      apply outputsWithin_of_raw_run (0 : Fin 3) 2 .read initial program
        (desired :: word) (result (desired :: word)) t
        (2*(desired :: word).length+5) (by simp; omega)
      · rw [hi]
        simpa only [run] using hh
      · rw [hi]
        simpa only [run, result] using ho

theorem padded_value (desired : Bool) (word : List Bool) :
    EncodedCommunication.bitsValue (result (desired :: word)) =
      EncodedCommunication.bitsValue word := by
  exact RationalProductSignedPhysical.parityPad_value word desired

theorem padded_parity (desired : Bool) (word : List Bool) :
    RationalProductSignedRepack.signParity (result (desired :: word)) = desired := by
  exact RationalProductSignedPhysical.parityPad_parity word desired

#print axioms outputs
#print axioms padded_value
#print axioms padded_parity

end CurrentAdditive.CodeDParityPadV2
