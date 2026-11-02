import EthInapproximability.CurrentPaper.SourceCSPRejectWriterFrame

/-!
# Clear-first writer for the encoded empty ordered three-CNF

The canonical empty formula is the two-bit word `[false,false]`. This
physical routine clears any old unary-count word before writing those bits,
so the zero branch has no hidden empty-output precondition.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPZeroWriter

open Turing TM2.Stmt BitMachineEncoding BitMachineStackEmbedding

inductive Label where
  | clear | write
  deriving DecidableEq, Fintype

abbrev Stack := Fin 1
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool)

def contents (output : List Bool) : Stack → List Bool := fun _ => output

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .clear => .pop 0 (fun _ b => b)
      (.branch Option.isSome (.goto (fun _ => .clear))
        (.goto (fun _ => .write)))
  | .write => .push 0 (fun _ => false)
      (.push 0 (fun _ => false) .halt)

theorem clear_nonempty (v : Option Bool) (b : Bool) (tail : List Bool) :
    advance program
      (⟨some .clear, v, contents (b :: tail)⟩ : Config) =
      ⟨some .clear, some b, contents tail⟩ := by
  simp [advance, TM2.step, TM2.stepAux, program, contents]
  funext k
  fin_cases k
  rfl

theorem clear_empty (v : Option Bool) :
    advance program (⟨some .clear, v, contents []⟩ : Config) =
      ⟨some .write, none, contents []⟩ := by
  simp [advance, TM2.step, TM2.stepAux, program, contents]

theorem write_step :
    advance program (⟨some .write, none, contents []⟩ : Config) =
      ⟨none, none, contents [false, false]⟩ := by
  simp [advance, TM2.step, TM2.stepAux, program, contents]
  funext k
  fin_cases k
  rfl

theorem run_exact_from (v : Option Bool) (output : List Bool) :
    ((advance program)^[output.length + 2])
      (⟨some .clear, v, contents output⟩ : Config) =
      ⟨none, none, contents [false, false]⟩ := by
  induction output generalizing v with
  | nil =>
      simp only [List.length_nil, Nat.zero_add,
        show 2 = 1 + 1 by decide]
      rw [Function.iterate_add_apply]
      simp only [Function.iterate_one, clear_empty, write_step]
  | cons b tail ih =>
      have hlength : (b :: tail).length + 2 =
          tail.length + 2 + 1 := by simp
      rw [hlength, Function.iterate_add_apply]
      simp only [Function.iterate_one, clear_nonempty]
      exact ih (some b)

end EthInapproximability.CurrentPaper.SourceCSPZeroWriter

namespace EthInapproximability.CurrentPaper.SourceCSPZeroWriterFrame

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := SourceCSPInputFrame.Stack
def outputSlot : Stack := SourceCSPRejectWriterFrame.outputSlot

def embedding : SourceCSPZeroWriter.Stack ↪ Stack where
  toFun := fun _ => outputSlot
  inj' := by intro x y _; fin_cases x; fin_cases y; rfl

def program (l : SourceCSPZeroWriter.Label) :
    TM2.Stmt (fun _ : Stack => Bool)
      SourceCSPZeroWriter.Label (Option Bool) :=
  stmt embedding id id id none (SourceCSPZeroWriter.program l)

theorem zero_run (before : Stack → List Bool) :
    ∃ t S, t ≤ (before outputSlot).length + 3 ∧
      ((advance program)^[t])
        (⟨some .clear, none, before⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            SourceCSPZeroWriter.Label (Option Bool)) =
        ⟨none, none, S⟩ ∧
      S outputSlot = [false, false] ∧
      (∀ k : Stack, k ≠ outputSlot → S k = before k) := by
  let localCfg : SourceCSPZeroWriter.Config :=
    ⟨some .clear, none,
      SourceCSPZeroWriter.contents (before outputSlot)⟩
  let n := (before outputSlot).length + 2
  have hr : ((advance SourceCSPZeroWriter.program)^[n]) localCfg =
      ⟨none, none, SourceCSPZeroWriter.contents [false, false]⟩ := by
    simpa only [n, localCfg] using
      SourceCSPZeroWriter.run_exact_from none (before outputSlot)
  have hhalt : (((advance SourceCSPZeroWriter.program)^[n])
      localCfg).l = none := by rw [hr]
  obtain ⟨t, ht, hrun⟩ := outputs embedding before id id id
    (fun _ => rfl) none SourceCSPZeroWriter.program program
    (fun _ => rfl) localCfg n hhalt
  have hstart : cfg embedding before id id none localCfg =
      (⟨some .clear, none, before⟩ :
        TM2.Cfg (fun _ : Stack => Bool)
          SourceCSPZeroWriter.Label (Option Bool)) := by
    simp only [cfg, stackCfg, BitMachineInline.cfg, localCfg, id_eq]
    congr 1
    apply bank_eq_self
    intro k
    fin_cases k
    rfl
  rw [hstart, hr] at hrun
  let S : Stack → List Bool := bank embedding before
    (SourceCSPZeroWriter.contents [false, false])
  refine ⟨t, S, by omega, ?_, ?_, ?_⟩
  · simpa only [program, S, cfg, stackCfg, BitMachineInline.cfg,
      id_eq, Option.map_none] using hrun
  · change bank embedding before _ (embedding 0) = _
    rw [bank_at]
    rfl
  · intro k hk
    apply bank_outside
    rintro ⟨i, hi⟩
    fin_cases i
    exact hk hi.symm

end EthInapproximability.CurrentPaper.SourceCSPZeroWriterFrame
