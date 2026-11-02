import Paper2.SuccessRunMain

/-! Unit 3, segment (5): producers of the parameter part of the writer start bank.

`SuccessRun.success_run` starts from the admitted `SuccessOrient.startBank … word` beside
`SuccessRun.preJH g r k thr output`, whose writer cells carry the master region `restL g r`
(with unary `s+1`, `s` in the fetch cells, unary `q₁, s, Q` in the default-row machine cells,
unary `p, w` in the default-column cells) and unary `k` in the retained cell `cR 4`.

Here those eight parameter cells are PRODUCED from the raw public unary counts that the admitted
start bank already carries (the compiler cells read by the admitted
`SamplerParameterJoin.program`, values by the admitted `SamplerParameterJoin.nrSrc_value`):

* `install = CopyAll.prog cpsI ; pushP` (ONE fixed program; production `BitMachineRawSequence`
  handoff, one charged step): eight source-preserving copies `s → sU`, `s → my`, `q₁ → RM 0`,
  `s → RM 1`, `Q → RM 2`, `p → CR 2`, `w → CR 6`, `k → cR 4`, then one push of a mark on `my`
  (`s ↦ s + 1`);
* `pre0_eq`: the parameter-free bank `preJH0 g r thr output` (NO implicit parameter at all; it
  carries only `SrcU.JJ0 g r` = unary `r`, unary `m` and the literal public graph bytes, the
  unary threshold and the output prefix) is `preJH` with exactly the eight destinations blank;
* `install_run`: `install` turns `startBank … word` beside `preJH0` into `startBank … word`
  (unchanged) beside `preJH g r k thr output`;
* `success_run_installed`: `fullProg = install ; SuccessRun.succProg`, from `startBank … word`
  beside `preJH0 g r thr output`, halts with `EncodedSelectedOutput.outputBits … tp ++ output`
  in the header output cell (all conclusions of `success_run`).

Still supplied (named premises, not produced here): unary `r = rep L m`, unary `m`, the literal
graph bytes `EncodedGraph.encode g` (inside `SrcU.JJ0 g r`), unary `thr = sourceBudget …`, the
output prefix, and — as in the admitted success chain — the raw public unary counts inside
`SuccessOrient.startBank`. -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.SuccessInstall

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource GeneratorFullSample
open RecursiveSamplingProgram RecursiveSamplingLaws RecursiveLabelCodecScratch
open RecursiveEntries RecursiveSampling RecursiveRequestCodeShape
open SourceProfileParameters SourceRecursiveNoSampling TotalFiniteConstructorScratch
open Paper2.HeaderJoin (JH hjIn hjProg wOut thrM scrH)
open Paper2.SuccessXfer (OS JT wAux)
open Paper2.SuccessRun (preJH auxPre hCtl succProg)

/-! ### Cells -/

/-- Master-region cell `z` inside the header-join bank. -/
def mC (z : SrcX.JX) : JH WEntry.Kw := wAux (.inl (RLoop.mX z))

def zMy : SrcX.JX := .inl (.inl (.inl FetchIndexed.myC))
def zSU : SrcX.JX := .inl (.inl (.inr 7))
def zQ1 : SrcX.JX := .inr (.inl 0)
def zS : SrcX.JX := .inr (.inl 1)
def zQ : SrcX.JX := .inr (.inl 2)
def zP : SrcX.JX := .inr (.inr (.inl (.inl 2)))
def zW : SrcX.JX := .inr (.inr (.inl (.inr 1)))

/-- The retained unary-`K` cell `cR 4` of the writer bank. -/
def kC : JH WEntry.Kw := wAux (.inr (.inl 4))

def dstsI : Fin 8 → JH WEntry.Kw := ![mC zSU, mC zMy, mC zQ1, mC zS, mC zQ, mC zP, mC zW, kC]

/-- Sources: the admitted raw public counts (`SamplerParameterJoin.nrSrc`: s, q₁, q₂, w, Q, p,
k, mX, mY) inside the success start bank. -/
def srcC (i : Fin 9) : OS := .inl (.inl (SamplerParameterJoin.nrSrc i))

def srcsI : Fin 8 → OS := ![srcC 0, srcC 0, srcC 1, srcC 0, srcC 4, srcC 5, srcC 3, srcC 6]

theorem dstsI_inj : ∀ i j, dstsI i = dstsI j → i = j := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [dstsI, mC, kC, wAux, RLoop.mX, zMy, zSU, zQ1, zS, zQ, zP, zW, FetchIndexed.myC]

def scrT : JT := .inr (.inr 0)

def cpf (i : Fin 8) : Fin 3 → JT := ![.inl (srcsI i), .inr (.inl (dstsI i)), scrT]

theorem cpf_inj (i : Fin 8) : Function.Injective (cpf i) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [cpf, scrT]

def cpsI (i : Fin 8) : Fin 3 ↪ JT := ⟨cpf i, cpf_inj i⟩

theorem cpsI_src (i : Fin 8) : cpsI i 0 = .inl (srcsI i) := rfl
theorem cpsI_dst (i : Fin 8) : cpsI i 1 = .inr (.inl (dstsI i)) := rfl
theorem cpsI_scr (i : Fin 8) : cpsI i 2 = scrT := rfl

def myT : JT := .inr (.inl (mC zMy))

/-- One charged push of a mark. -/
def pushP : Unit → TM2.Stmt (fun _ : JT => Bool) Unit (Option Bool) :=
  fun _ => TM2.Stmt.push myT (fun _ => true) TM2.Stmt.halt

theorem push_run (S : JT → List Bool) (v : Option Bool) :
    ((advance pushP)^[1]) (⟨some (), v, S⟩ : TM2.Cfg (fun _ : JT => Bool) _ _) =
      ⟨none, v, Function.update S myT (true :: S myT)⟩ := rfl

/-- The install program: eight copies, then the push. ONE fixed program. -/
def install := BitMachineRawSequence.program (CopyAll.prog cpsI) pushP ()
  (none : Option Bool) (none : Option Bool)

/-- The whole success branch: install, then `SuccessRun.succProg`. ONE fixed program. -/
def fullProg := BitMachineRawSequence.program install succProg
  (SamplerFallbackJoin.labelOf succProg
    (BitMachineRawSequence.leftLabel SuccessOrient.startLabel))
  ((none : Option Bool), (none : Option Bool))
  (SuccessOrient.startControl, ((none : Option Bool), hCtl))

/-! ### The parameter-free writer start bank -/

/-- The master region with every parameter cell blank: only `SrcU.JJ0 g r` (unary `r`,
unary `m`, the literal public graph bytes) remains. -/
def master0 (g : EncodedGraph.Graph) (r : ℕ) : SrcX.JX → List Bool :=
  Sum.elim (Sum.elim (fun _ => []) (Sum.elim (SrcU.JJ0 g r) (fun _ => []))) (fun _ => [])

def auxPre0 (g : EncodedGraph.Graph) (r : ℕ) : WEntry.Aux → List Bool :=
  Sum.elim (Sum.elim (fun _ => []) (Sum.elim (master0 g r) (fun _ => []))) (fun _ => [])

/-- The writer/header start bank before the install (no implicit parameter). -/
def preJH0 (g : EncodedGraph.Graph) (r thr : ℕ) (output : List Bool) :
    JH WEntry.Kw → List Bool :=
  hjIn (MatrixTableWriter.ready (fun i => auxPre0 g r (WEntry.eqv.symm i)) 0 0 0 0 0 0 []
    output).contents thr

def blankI (W : JH WEntry.Kw → List Bool) : JH WEntry.Kw → List Bool :=
  fun a => if ∃ i, dstsI i = a then [] else W a

theorem blankI_dst (W : JH WEntry.Kw → List Bool) (i : Fin 8) : blankI W (dstsI i) = [] := by
  unfold blankI
  rw [if_pos ⟨i, rfl⟩]

theorem blankI_off (W : JH WEntry.Kw → List Bool) (a : JH WEntry.Kw)
    (h : ¬ ∃ i, dstsI i = a) : blankI W a = W a := by
  unfold blankI
  rw [if_neg h]

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

theorem pre0_eq (g : EncodedGraph.Graph) (r K thr : ℕ) (output : List Bool) :
    preJH0 g r thr output =
      blankI (preJH (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
        g r K thr output) := by
  funext a
  by_cases ha : ∃ i, dstsI i = a
  · obtain ⟨i, rfl⟩ := ha
    rw [blankI_dst]
    fin_cases i <;>
      (change auxPre0 g r (WEntry.eqv.symm (WEntry.eqv _)) = []
       rw [Equiv.symm_apply_apply]
       rfl)
  · rw [blankI_off _ _ ha]
    rcases a with ((c | e) | h)
    · rcases c with c | c
      · obtain ⟨b, rfl⟩ := WEntry.eqv.surjective c
        change auxPre0 g r (WEntry.eqv.symm (WEntry.eqv b)) =
          auxPre (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r K
            (WEntry.eqv.symm (WEntry.eqv b))
        rw [Equiv.symm_apply_apply]
        rcases b with b | (b | (b | b))
        · rcases b with jt | (z | c2)
          · rcases jt with j | e <;> rfl
          · change master0 g r z = RLoop.master (p := p) (s := s) (q₁ := q₁) (q₂ := q₂)
              (w := w) (Q := Q) g r z
            rcases z with ((bb | (jj | f4)) | lb)
            · rcases bb with ((inner | f5) | f8)
              · rcases inner with ((y | y) | y) <;> fin_cases y <;> rfl
              · fin_cases f5
                · rfl
                · rfl
                · rfl
                · exact absurd ⟨1, rfl⟩ ha
                · rfl
              · fin_cases f8
                · rfl
                · rfl
                · rfl
                · rfl
                · rfl
                · rfl
                · rfl
                · exact absurd ⟨0, rfl⟩ ha
            · rfl
            · fin_cases f4 <;> rfl
            · rcases lb with y | ((y | y) | y)
              · fin_cases y
                · exact absurd ⟨2, rfl⟩ ha
                · exact absurd ⟨3, rfl⟩ ha
                · exact absurd ⟨4, rfl⟩ ha
                all_goals rfl
              · fin_cases y
                · rfl
                · rfl
                · exact absurd ⟨5, rfl⟩ ha
                · rfl
                · rfl
              · fin_cases y
                · rfl
                · exact absurd ⟨6, rfl⟩ ha
                · rfl
              · fin_cases y <;> rfl
          · fin_cases c2 <;> rfl
        · fin_cases b
          · rfl
          · rfl
          · rfl
          · rfl
          · exact absurd ⟨7, rfl⟩ ha
        · rfl
        · fin_cases b <;> rfl
      · fin_cases c <;> rfl
    · cases e <;> rfl
    · rfl

end

#print axioms dstsI_inj
#print axioms push_run
#print axioms pre0_eq

end Paper2.SuccessInstall
