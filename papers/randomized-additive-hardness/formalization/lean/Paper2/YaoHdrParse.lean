import Paper2.YaoSrcCodecB
import EthInapproximability.CurrentPaper.ExactParameterBranchInstall
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! Unit 5 segment Y2 (lane a-yao-owner-1): the physical header machine.

Consumer: the prelude Y6 (unary `e`, and unary `v`).  Scope per root decision
R-Y2: specified on valid upstream-produced codes `encode x ++ rest` (the pure
`decode` of `YaoSrcCodecB` stays total with rejection; this machine does not
validate).  One fixed program, depending only on the placement
`ι : Fin 5 ↪ J`.  Cells: 0 code (preserved), 1 work, 2 copy scratch,
3 unary `v`, 4 unary `e`.  Stage 1 copies the code (admitted
`ExactParameterBranchInstall.copy_run`); stage 2 is a two-label header reader
that moves the two unary headers into cells 3 and 4, one TM2 step per bit,
leaving exactly the body stream `(bodyCodec t v e).encode (flatten edges) ++ rest`
in the work cell (the stream parsed on all inputs by the admitted
`UnaryFieldListParserScratch.observed_run_eq_piCodec`).  One charged handoff
(`BitMachineRawSequence.runs`).  Exit bank exact on the whole ambient bank. -/

namespace Paper2.YaoHeaderParser

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.YaoSourceCodec

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

/-! ## The local header reader on three stacks (0 input, 1 `v`, 2 `e`) -/

inductive Label where
  | readV | readE
  deriving DecidableEq, Fintype

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label (Option Bool)
  | .readV => pop 0 (fun _ b => b)
      (branch (fun b => b.getD false)
        (push 1 (fun _ => true) (goto (fun _ => .readV)))
        (goto (fun _ => .readE)))
  | .readE => pop 0 (fun _ b => b)
      (branch (fun b => b.getD false)
        (push 2 (fun _ => true) (goto (fun _ => .readE)))
        halt)

abbrev Config := TM2.Cfg (fun _ : Fin 3 => Bool) Label (Option Bool)

def cfg (l : Option Label) (c : Option Bool) (input vs es : List Bool) : Config :=
  ⟨l, c, ![input, vs, es]⟩

def run (n : ℕ) (c : Config) := ((advance program)^[n]) c

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (n : ℕ) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem stepV_true (c : Option Bool) (input vs es : List Bool) :
    TM2.step program (cfg (some .readV) c (true :: input) vs es) =
      some (cfg (some .readV) (some true) input (true :: vs) es) := by
  apply congrArg (fun S => some (⟨some .readV, some true, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem stepV_false (c : Option Bool) (input vs es : List Bool) :
    TM2.step program (cfg (some .readV) c (false :: input) vs es) =
      some (cfg (some .readE) (some false) input vs es) := by
  apply congrArg (fun S => some (⟨some .readE, some false, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem stepE_true (c : Option Bool) (input vs es : List Bool) :
    TM2.step program (cfg (some .readE) c (true :: input) vs es) =
      some (cfg (some .readE) (some true) input vs (true :: es)) := by
  apply congrArg (fun S => some (⟨some .readE, some true, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem stepE_false (c : Option Bool) (input vs es : List Bool) :
    TM2.step program (cfg (some .readE) c (false :: input) vs es) =
      some (cfg none (some false) input vs es) := by
  apply congrArg (fun S => some (⟨none, some false, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem run_halted (c : Option Bool) (input vs es : List Bool) (n : ℕ) :
    run n (cfg none c input vs es) = cfg none c input vs es := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [run, Function.iterate_succ_apply]
      exact ih

private theorem rep_cons (n : ℕ) (l : List Bool) :
    List.replicate n true ++ true :: l = true :: (List.replicate n true ++ l) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem readV_run (n : ℕ) (c : Option Bool) (rest vs es : List Bool) :
    run (n + 1) (cfg (some .readV) c (List.replicate n true ++ false :: rest) vs es) =
      cfg (some .readE) (some false) rest (List.replicate n true ++ vs) es := by
  induction n generalizing c vs with
  | zero => simpa using run_succ (stepV_false c rest vs es) 0
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append, run_succ (stepV_true _ _ _ _), ih, rep_cons]
      rfl

theorem readE_run (n : ℕ) (c : Option Bool) (rest vs es : List Bool) :
    run (n + 1) (cfg (some .readE) c (List.replicate n true ++ false :: rest) vs es) =
      cfg none (some false) rest vs (List.replicate n true ++ es) := by
  induction n generalizing c es with
  | zero => simpa using run_succ (stepE_false c rest vs es) 0
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append, run_succ (stepE_true _ _ _ _), ih, rep_cons]
      rfl

theorem header_run (v e : ℕ) (c : Option Bool) (rest : List Bool) :
    run (v + e + 2) (cfg (some .readV) c (unaryNat v ++ unaryNat e ++ rest) [] []) =
      cfg none (some false) rest (List.replicate v true) (List.replicate e true) := by
  have h1 := readV_run v c (List.replicate e true ++ false :: rest) [] []
  have h2 := readE_run e (some false) rest (List.replicate v true) []
  simp only [List.append_nil] at h1 h2
  have hin : unaryNat v ++ unaryNat e ++ rest =
      List.replicate v true ++ false :: (List.replicate e true ++ false :: rest) := by
    simp [unaryNat, List.append_assoc]
  rw [hin, show v + e + 2 = (e + 1) + (v + 1) by omega]
  unfold run at h1 h2 ⊢
  rw [Function.iterate_add_apply, h1, h2]

/-! ## Ambient placement: copy, then read the header -/

noncomputable def readProgram {K : Type*} [DecidableEq K] (ι : Fin 3 ↪ K) (l : Label) :
    TM2.Stmt (fun _ : K => Bool) Label (Option Bool) :=
  BitMachineStackEmbedding.stmt ι id id id none (program l)

theorem read_run {K : Type*} [DecidableEq K] (ι : Fin 3 ↪ K) (S : K → List Bool)
    (v e : ℕ) (rest : List Bool)
    (h0 : S (ι 0) = unaryNat v ++ unaryNat e ++ rest) (h1 : S (ι 1) = []) (h2 : S (ι 2) = []) :
    ∃ n ≤ v + e + 2,
      ((advance (readProgram ι))^[n])
        (⟨some .readV, none, S⟩ : TM2.Cfg (fun _ : K => Bool) Label (Option Bool)) =
        ⟨none, some false, Function.update (Function.update (Function.update S (ι 0) rest)
          (ι 1) (List.replicate v true)) (ι 2) (List.replicate e true)⟩ := by
  classical
  let c := cfg (some .readV) none (unaryNat v ++ unaryNat e ++ rest) [] []
  have hbank : BitMachineStackEmbedding.bank ι S c.stk = S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    fin_cases k <;> simp [c, cfg, h0, h1, h2]
  have hrun := header_run v e none rest
  have hhalt : (((advance program)^[v + e + 2]) c).l = none := by
    change (run _ c).l = none
    rw [hrun]
    rfl
  obtain ⟨n, hn, he⟩ := BitMachineStackEmbedding.outputs ι S id id id (fun _ => rfl) none
    program (readProgram ι) (by intro l; rfl) c _ hhalt
  have hlocal : ((advance program)^[v + e + 2]) c =
      cfg none (some false) rest (List.replicate v true) (List.replicate e true) := hrun
  rw [hlocal] at he
  change ((advance (readProgram ι))^[n])
      ⟨some .readV, none, BitMachineStackEmbedding.bank ι S c.stk⟩ =
      ⟨none, some false, BitMachineStackEmbedding.bank ι S
        (cfg none (some false) rest (List.replicate v true) (List.replicate e true)).stk⟩ at he
  have hupdate : (cfg none (some false) rest (List.replicate v true)
      (List.replicate e true)).stk =
      Function.update (Function.update (Function.update c.stk 0 rest) 1
        (List.replicate v true)) 2 (List.replicate e true) := by
    funext k
    fin_cases k <;> simp [c, cfg]
  rw [hbank, hupdate, BitMachineStackEmbedding.bank_update,
    BitMachineStackEmbedding.bank_update, BitMachineStackEmbedding.bank_update, hbank] at he
  exact ⟨n, hn, he⟩

def copySel : Fin 3 ↪ Fin 5 := ⟨![0, 1, 2], by decide⟩
def readSel : Fin 3 ↪ Fin 5 := ⟨![1, 3, 4], by decide⟩

variable {J : Type*} [DecidableEq J]

/-- The fixed Y2 program: copy the code, charged handoff, read the header. -/
noncomputable def headerProgram (ι : Fin 5 ↪ J) :=
  BitMachineRawSequence.program
    (ExactParameterBranchInstall.copyProgram (copySel.trans ι)) (readProgram (readSel.trans ι))
    Label.readV none none

def startLabel : BitMachineRawSequence.Label BitMachineCopy.Label Label :=
  BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan

/-- Exact exit bank. -/
def headerOut (ι : Fin 5 ↪ J) (S : J → List Bool) (v e : ℕ) (body : List Bool) :
    J → List Bool :=
  Function.update (Function.update (Function.update S (ι 1) body)
    (ι 3) (List.replicate v true)) (ι 4) (List.replicate e true)

/-- Y2 main theorem: on a valid upstream code `encode x ++ rest` in cell 0,
the fixed program halts with unary `v` in cell 3, unary `e` in cell 4, the
body stream in the work cell 1, the code preserved, the copy scratch empty
and every other ambient cell unchanged. -/
theorem physical_header (ι : Fin 5 ↪ J) (S : J → List Bool) {t : ℕ} (x : YaoSource t)
    (rest : List Bool)
    (h0 : S (ι 0) = encode x ++ rest) (h1 : S (ι 1) = []) (h2 : S (ι 2) = [])
    (h3 : S (ι 3) = []) (h4 : S (ι 4) = []) :
    ∃ total ≤ (2 * (encode x ++ rest).length + 2) + (x.1 + x.2.1 + 2) + 1,
      ((advance (headerProgram ι))^[total])
        (⟨some startLabel, (none, none), S⟩ : TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, (none, some false),
          headerOut ι S x.1 x.2.1
            ((bodyCodec t x.1 x.2.1).encode (flatten x.2.2) ++ rest)⟩ := by
  classical
  have hinj := ι.injective
  obtain ⟨t1, ht1, hr1⟩ := ExactParameterBranchInstall.copy_run (copySel.trans ι) S
    (encode x ++ rest)
    (by simp [copySel, h0]) (by simp [copySel, h1]) (by simp [copySel, h2])
  set S1 := Function.update S ((copySel.trans ι) 1) (encode x ++ rest) with hS1
  have hcode : encode x ++ rest = unaryNat x.1 ++ unaryNat x.2.1 ++
      ((bodyCodec t x.1 x.2.1).encode (flatten x.2.2) ++ rest) := by
    simp [encode, List.append_assoc]
  obtain ⟨t2, ht2, hr2⟩ := read_run (readSel.trans ι) S1 x.1 x.2.1
    ((bodyCodec t x.1 x.2.1).encode (flatten x.2.2) ++ rest)
    (by simp [hS1, copySel, readSel, Function.update_apply, hinj.eq_iff, hcode])
    (by simp [hS1, copySel, readSel, Function.update_apply, hinj.eq_iff, h3])
    (by simp [hS1, copySel, readSel, Function.update_apply, hinj.eq_iff, h4])
  have hfinal : Function.update (Function.update (Function.update S1
      ((readSel.trans ι) 0) ((bodyCodec t x.1 x.2.1).encode (flatten x.2.2) ++ rest))
      ((readSel.trans ι) 1) (List.replicate x.1 true))
      ((readSel.trans ι) 2) (List.replicate x.2.1 true) =
      headerOut ι S x.1 x.2.1 ((bodyCodec t x.1 x.2.1).encode (flatten x.2.2) ++ rest) := by
    funext j
    by_cases hj : ∃ k, ι k = j
    · obtain ⟨k, rfl⟩ := hj
      fin_cases k <;>
        simp [headerOut, hS1, copySel, readSel, Function.update_apply, hinj.eq_iff]
    · have hne : ∀ k, j ≠ ι k := fun k hk => hj ⟨k, hk.symm⟩
      simp [headerOut, hS1, copySel, readSel, Function.update_apply, hne]
  rw [hfinal] at hr2
  obtain ⟨u, hu, hrun⟩ := BitMachineRawSequence.runs
    (ExactParameterBranchInstall.copyProgram (copySel.trans ι)) (readProgram (readSel.trans ι))
    BitMachineCopy.Label.scan Label.readV none none none (some false) S S1 _ t1 t2 hr1 hr2
  exact ⟨u, by omega, hrun⟩

#print axioms header_run
#print axioms read_run
#print axioms physical_header

end Paper2.YaoHeaderParser
