import CurrentAdditive.GaussPivotParser32
import EthInapproximability.CurrentPaper.SourceClausePreservingBroadcast
import EthInapproximability.CurrentPaper.BitMachineClearBank

/-! Physical movement of the parsed Gauss fields into the contextual scanner
layout. The saved original packet is copied from bank 28 to bank 31. -/

namespace CurrentAdditive.GaussPivotFields32

open EthInapproximability.CurrentPaper
open Turing Turing.TM2.Stmt BitMachineEncoding

abbrev Stack := Fin 32
abbrev Control := Unit × Option Bool

inductive Label where
  | copy (p : Fin 4) (l : SourceClausePreservingBroadcast.Label)
  | clear (p : Fin 5)
  | finishClear | done
  deriving DecidableEq, Fintype

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def source : Fin 4 → Stack := ![16, 18, 17, 28]
def dest : Fin 4 → Stack := ![8, 12, 30, 31]
def temp : Stack := 29
def clearBank : Fin 5 → Stack := ![16, 17, 18, 19, 28]

def nextCopy (p : Fin 4) : Label :=
  if h : p.val + 1 < 4 then .copy ⟨p.val + 1, h⟩ .scan
  else .clear 0

def nextClear (p : Fin 5) : Label :=
  if h : p.val + 1 < 5 then .clear ⟨p.val + 1, h⟩
  else .finishClear

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .copy p l =>
      BitMachineInline.stmt (Label.copy p) id id (some (nextCopy p))
        (SourceClausePreservingBroadcast.program (source p) temp [dest p] l)
  | .clear p =>
      BitMachineClearBank.clearStep (clearBank p) (.clear p) (nextClear p)
  | .finishClear => BitMachineClearBank.finishStep id .done
  | .done => .halt

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c c' : Config} {n : Nat} (h : run n c = c') (u : Nat) :
    run (n + u) c = run u c' := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run u) h

def after0 (S : Stack → List Bool) : Stack → List Bool :=
  SourceClausePreservingBroadcast.result (source 0) temp [dest 0]
    (S (source 0)) S
def after1 (S : Stack → List Bool) : Stack → List Bool :=
  SourceClausePreservingBroadcast.result (source 1) temp [dest 1]
    (S (source 1)) (after0 S)
def after2 (S : Stack → List Bool) : Stack → List Bool :=
  SourceClausePreservingBroadcast.result (source 2) temp [dest 2]
    (S (source 2)) (after1 S)
def after3 (S : Stack → List Bool) : Stack → List Bool :=
  SourceClausePreservingBroadcast.result (source 3) temp [dest 3]
    (S (source 3)) (after2 S)

theorem copy_phase (p : Fin 4) (bits : List Bool) (S : Stack → List Bool)
    (hbits : S (source p) = bits) (htemp : S temp = []) :
    ∃ t ≤ 2 * bits.length + 3,
      run t ⟨some (.copy p .scan), ((), none), S⟩ =
        ⟨some (nextCopy p), ((), none),
          SourceClausePreservingBroadcast.result (source p) temp
            [dest p] bits S⟩ := by
  have hst : source p ≠ temp := by
    fin_cases p <;> decide
  have hs : source p ∉ [dest p] := by
    fin_cases p <;> decide
  have ht : temp ∉ [dest p] := by
    fin_cases p <;> decide
  have hcore := SourceClausePreservingBroadcast.run_halt
    (source p) temp [dest p] hst (by simp) hs ht bits S hbits htemp
  obtain ⟨u, hu, hr⟩ := BitMachineInline.outputs
    (Label.copy p) id id (by intro v; rfl) (some (nextCopy p))
    (SourceClausePreservingBroadcast.program (source p) temp [dest p])
    program (by intro l; rfl)
    (⟨some .scan, ((), none), S⟩ :
      TM2.Cfg (fun _ : Stack => Bool)
        SourceClausePreservingBroadcast.Label Control)
    (2 * bits.length + 3) (by rw [hcore])
  refine ⟨u, hu, ?_⟩
  change run u _ = _ at hr
  rw [hcore] at hr
  simpa only [BitMachineInline.cfg] using hr

private theorem after0_source1 (S : Stack → List Bool) :
    after0 S (source 1) = S (source 1) := by
  simp [after0, source, dest, temp,
    SourceClausePreservingBroadcast.result, BitMachineBroadcast.prepend]

private theorem after1_source2 (S : Stack → List Bool) :
    after1 S (source 2) = S (source 2) := by
  simp [after1, after0, source, dest, temp,
    SourceClausePreservingBroadcast.result, BitMachineBroadcast.prepend]

private theorem after2_source3 (S : Stack → List Bool) :
    after2 S (source 3) = S (source 3) := by
  simp [after2, after1, after0, source, dest, temp,
    SourceClausePreservingBroadcast.result, BitMachineBroadcast.prepend]

def copyClock (S : Stack → List Bool) : Nat :=
  (2 * (S (source 0)).length + 3) +
  (2 * (S (source 1)).length + 3) +
  (2 * (S (source 2)).length + 3) +
  (2 * (S (source 3)).length + 3)

theorem copy_fields (S : Stack → List Bool) (htemp : S temp = []) :
    ∃ t ≤ copyClock S,
      run t ⟨some (.copy 0 .scan), ((), none), S⟩ =
        ⟨some (.clear 0), ((), none), after3 S⟩ := by
  obtain ⟨t0, h0, hr0⟩ := copy_phase 0 (S (source 0)) S rfl htemp
  have hs0 : run t0 ⟨some (.copy 0 .scan), ((), none), S⟩ =
      ⟨some (.copy 1 .scan), ((), none), after0 S⟩ := by
    simpa [nextCopy, after0] using hr0
  obtain ⟨t1, h1, hr1⟩ := copy_phase 1 (S (source 1))
    (after0 S) (after0_source1 S)
    (SourceClausePreservingBroadcast.temp_empty _ _ _ _ _)
  have hs1 : run t1 ⟨some (.copy 1 .scan), ((), none), after0 S⟩ =
      ⟨some (.copy 2 .scan), ((), none), after1 S⟩ := by
    simpa [nextCopy, after1] using hr1
  obtain ⟨t2, h2, hr2⟩ := copy_phase 2 (S (source 2))
    (after1 S) (after1_source2 S)
    (SourceClausePreservingBroadcast.temp_empty _ _ _ _ _)
  have hs2 : run t2 ⟨some (.copy 2 .scan), ((), none), after1 S⟩ =
      ⟨some (.copy 3 .scan), ((), none), after2 S⟩ := by
    simpa [nextCopy, after2] using hr2
  obtain ⟨t3, h3, hr3⟩ := copy_phase 3 (S (source 3))
    (after2 S) (after2_source3 S)
    (SourceClausePreservingBroadcast.temp_empty _ _ _ _ _)
  have hs3 : run t3 ⟨some (.copy 3 .scan), ((), none), after2 S⟩ =
      ⟨some (.clear 0), ((), none), after3 S⟩ := by
    simpa [nextCopy, after3] using hr3
  refine ⟨t0 + t1 + t2 + t3, ?_, ?_⟩
  · unfold copyClock; omega
  · rw [show t0 + t1 + t2 + t3 = ((t0 + t1) + t2) + t3 by omega]
    exact (((run_add hs0 t1).trans hs1 |> fun h => run_add h t2).trans hs2
      |> fun h => run_add h t3).trans hs3

theorem copied_field (S : Stack → List Bool) (p : Fin 4)
    (hDest : ∀ q : Fin 4, S (dest q) = []) :
    after3 S (dest p) = S (source p) := by
  have h0 : S 8 = [] := hDest 0
  have h1 : S 12 = [] := hDest 1
  have h2 : S 30 = [] := hDest 2
  have h3 : S 31 = [] := hDest 3
  fin_cases p <;>
    simp [after3, after2, after1, after0, source, dest, temp,
      SourceClausePreservingBroadcast.result,
      BitMachineBroadcast.prepend, h0, h1, h2, h3]

def clearLabel : Fin 6 → Label
  | ⟨n, _hn⟩ => if h : n < 5 then .clear ⟨n, h⟩ else .finishClear

theorem clearBank_injective : Function.Injective clearBank := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [clearBank]

theorem clearLabel_step (i : Fin 5) :
    clearLabel i.castSucc = .clear i ∧
    clearLabel i.succ = nextClear i := by
  fin_cases i <;> simp [clearLabel, nextClear]

theorem clearLabel_finish : clearLabel (Fin.last 5) = .finishClear := by
  simp [clearLabel]

theorem clear_run (S : Stack → List Bool) :
    run ((∑ i : Fin 5, (S (clearBank i)).length) + 6)
      ⟨some (.clear 0), ((), none), S⟩ =
        ⟨some .done, ((), none), BitMachineClearBank.cleared clearBank S⟩ := by
  change ((advance program)^[(∑ i : Fin 5, (S (clearBank i)).length) + 5 + 1])
    ⟨some (clearLabel 0), ((), none), S⟩ = _
  apply BitMachineClearBank.clear_bank_run program id
    Label.done 5 clearBank clearBank_injective clearLabel
  · intro i
    obtain ⟨hi, hn⟩ := clearLabel_step i
    rw [hi, hn]
    rfl
  · rw [clearLabel_finish]
    rfl

theorem fields_and_cleanup (S : Stack → List Bool) (htemp : S temp = []) :
    ∃ t ≤ copyClock S +
        (∑ i : Fin 5, ((after3 S) (clearBank i)).length) + 6,
      run t ⟨some (.copy 0 .scan), ((), none), S⟩ =
        ⟨some .done, ((), none),
          BitMachineClearBank.cleared clearBank (after3 S)⟩ := by
  obtain ⟨t, ht, hr⟩ := copy_fields S htemp
  refine ⟨t + ((∑ i : Fin 5, ((after3 S) (clearBank i)).length) + 6),
    by omega, ?_⟩
  exact (run_add hr _).trans (clear_run (after3 S))

theorem final_field (S : Stack → List Bool) (p : Fin 4)
    (hDest : ∀ q : Fin 4, S (dest q) = []) :
    (BitMachineClearBank.cleared clearBank (after3 S)) (dest p) =
      S (source p) := by
  rw [BitMachineClearBank.cleared_foreign]
  · exact copied_field S p hDest
  · intro i
    fin_cases i <;> fin_cases p <;> decide

theorem final_scratch (S : Stack → List Bool) (i : Fin 5) :
    (BitMachineClearBank.cleared clearBank (after3 S)) (clearBank i) = [] :=
  BitMachineClearBank.cleared_bank _ _ i

#print axioms copy_fields
#print axioms copied_field
#print axioms fields_and_cleanup
#print axioms final_field
#print axioms final_scratch

end CurrentAdditive.GaussPivotFields32
