import EthInapproximability.CurrentPaper.PrimeSamplerEntryMachine
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.BitMachineClearBank
import EthInapproximability.CurrentPaper.MatrixUnaryDivision
import EthInapproximability.CurrentPaper.MatrixStage4FamilyData
import EthInapproximability.CurrentPaper.PrimeSamplerFamilyTableOneHot

/-!
# Exact whole-bank embedded runs for the family-table row body

Lane owner:b-stage4-entry-program, segment 1 (generic part).

Every lemma here embeds an already-checked literal controller
(`MatrixUnaryDivision.program`, the one-hot writer
`PrimeSamplerFamilyTableOneHot.program`, the admitted unary prime-polynomial
accessor `PrimeSamplerEntryMachine.program`) into an arbitrary ambient bank
and states the ENTIRE ambient exit bank as explicit updates of the start
bank. No value is supplied: every output word is computed by the run.
-/

namespace EthInapproximability.CurrentPaper.FamilyRowGeneric

open Turing BitMachineEncoding BitMachineStackEmbedding
open MatrixStage4ScalarPreparationOps

section Generic

variable {K : Type*} [DecidableEq K]

theorem copy_blank (ι : Fin 3 ↪ K) (S : K → List Bool)
    (hscratch : S (ι 2) = []) (htarget : S (ι 1) = []) :
    ((advance (copyProgram ι))^[2 * (S (ι 0)).length + 2])
      (⟨some .scan, none, S⟩ : TM2.Cfg (fun _ : K => Bool)
        BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, Function.update S (ι 1) (S (ι 0))⟩ := by
  have h := copy_run ι S hscratch
  rw [htarget, List.append_nil] at h
  exact h

def divProgram (ι : Fin 6 ↪ K) :
    MatrixUnaryDivision.Label →
      TM2.Stmt (fun _ : K => Bool) MatrixUnaryDivision.Label Bool :=
  fun l => stackStmt ι (MatrixUnaryDivision.program l)

theorem div_run (ι : Fin 6 ↪ K) (S : K → List Bool) (n d : ℕ)
    (h0 : S (ι 0) = List.replicate n true)
    (h1 : S (ι 1) = List.replicate d true)
    (h2 : S (ι 2) = []) (h3 : S (ι 3) = []) (h4 : S (ι 4) = [])
    (h5 : S (ι 5) = []) :
    ((advance (divProgram ι))^[MatrixUnaryDivision.totalTime n d])
      (⟨some .start, false, S⟩ :
        TM2.Cfg (fun _ : K => Bool) MatrixUnaryDivision.Label Bool) =
      ⟨none, false, Function.update (Function.update
        (Function.update S (ι 0) []) (ι 3) (List.replicate (n % d) true))
        (ι 4) (List.replicate (n / d) true)⟩ := by
  let c := MatrixUnaryDivision.cfg (some .start) false (List.replicate n true)
    (List.replicate d true) [] [] [] []
  have hstart : stackCfg ι S c =
      (⟨some .start, false, S⟩ :
        TM2.Cfg (fun _ : K => Bool) MatrixUnaryDivision.Label Bool) := by
    simp only [stackCfg, c, MatrixUnaryDivision.cfg]
    congr 1
    apply bank_eq_self
    intro k
    fin_cases k <;> simp [h0, h1, h2, h3, h4, h5]
  have hrun := BitMachineStackRun.run ι S MatrixUnaryDivision.program c
    (MatrixUnaryDivision.totalTime n d)
  rw [hstart] at hrun
  have he : ((advance MatrixUnaryDivision.program)^[
      MatrixUnaryDivision.totalTime n d]) c =
      MatrixUnaryDivision.cfg none false [] (List.replicate d true) []
        (List.replicate (n % d) true) (List.replicate (n / d) true) [] :=
    MatrixUnaryDivision.division_total_run n d
  unfold divProgram
  rw [hrun, he]
  simp only [stackCfg, MatrixUnaryDivision.cfg]
  congr 1
  have hloc : (![[], List.replicate d true, [], List.replicate (n % d) true,
      List.replicate (n / d) true, []] : Fin 6 → List Bool) =
      Function.update (Function.update (Function.update (fun k => S (ι k)) 0 [])
        3 (List.replicate (n % d) true)) 4 (List.replicate (n / d) true) := by
    funext k
    fin_cases k <;> simp [h1, h2, h5]
  rw [hloc, bank_update, bank_update, bank_update, bank_restrict]

end Generic

/-! ## The one-hot writer: general-step lemmas and its full run -/

section OneHot

open PrimeSamplerFamilyTableOneHot

theorem rep_push (n : ℕ) (b : Bool) (s : List Bool) :
    List.replicate n b ++ b :: s = b :: (List.replicate n b ++ s) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem oh_tail_step (index width saved output : List Bool) (v : Option Bool) :
    advance program (cfg (some .tail) v index (true :: width) saved output) =
    cfg (some .tail) (some true) index width saved (false :: output) := by
  simp [advance, TM2.step, TM2.stepAux, PrimeSamplerFamilyTableOneHot.program, PrimeSamplerFamilyTableOneHot.cfg]
  funext k
  fin_cases k <;> rfl

theorem oh_tail_done (index saved output : List Bool) (v : Option Bool) :
    advance program (cfg (some .tail) v index [] saved output) =
    cfg (some .middle) none index [] saved output := by
  simp [advance, TM2.step, TM2.stepAux, PrimeSamplerFamilyTableOneHot.program, PrimeSamplerFamilyTableOneHot.cfg]

theorem oh_middle_step (index saved output : List Bool) (v : Option Bool) :
    advance program (cfg (some .middle) v index [] saved output) =
    cfg (some .front) v index [] saved (true :: output) := by
  simp [advance, TM2.step, TM2.stepAux, PrimeSamplerFamilyTableOneHot.program, PrimeSamplerFamilyTableOneHot.cfg]
  funext k
  fin_cases k <;> rfl

theorem oh_tail_run (n : Nat) (index saved output : List Bool) (v : Option Bool) :
    run n (cfg (some .tail) v index (List.replicate n true) saved output) =
    cfg (some .tail) (if n = 0 then v else some true)
      index [] saved (List.replicate n false ++ output) := by
  induction n generalizing output v with
  | zero => simp [PrimeSamplerFamilyTableOneHot.run, PrimeSamplerFamilyTableOneHot.cfg]
  | succ n ih =>
      simp only [run, Function.iterate_succ_apply, List.replicate_succ]
      rw [oh_tail_step]
      change run n (cfg (some .tail) (some true) index
        (List.replicate n true) saved (false :: output)) = _
      rw [ih]
      simp only [ite_self, Nat.succ_ne_zero, if_false, rep_push, List.cons_append]

def ohTime (i w : ℕ) : ℕ := 2 * i + (w - 1 - i) + 5

theorem run_one (c : Config) : run 1 c = advance program c := rfl

theorem onehot_local (i w : ℕ) (hi : i < w) (output : List Bool) :
    run (ohTime i w)
      (cfg (some .start) none (List.replicate i true)
        (List.replicate w true) [] output) =
      cfg none none [] [] []
        (MatrixStage4FamilyData.oneHot w ⟨i, hi⟩ ++ output) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = i + 1 + k := ⟨w - 1 - i, by omega⟩
  have ht : ohTime i (i + 1 + k) = 1 + (i + (1 + (k + (1 + (1 + (i + 1)))))) := by
    unfold ohTime; omega
  have hw : List.replicate (i + 1 + k) true = true :: List.replicate (i + k) true := by
    rw [show i + 1 + k = (i + k) + 1 by omega, List.replicate_succ]
  rw [ht, run_after, run_one, hw, start_step, run_after,
    subtract_run i k [] output (some true), run_after, run_one, subtract_done,
    List.append_nil, run_after, oh_tail_run, run_after, run_one, oh_tail_done,
    run_after, run_one, oh_middle_step, run_after, front_run, run_one, front_done]
  simp [MatrixStage4FamilyData.oneHot, List.append_assoc]

end OneHot

section OneHotEmbedded

variable {K : Type*} [DecidableEq K]

def ohProgram (ι : Fin 4 ↪ K) :
    PrimeSamplerFamilyTableOneHot.Label →
      TM2.Stmt (fun _ : K => Bool) PrimeSamplerFamilyTableOneHot.Label (Option Bool) :=
  fun l => stackStmt ι (PrimeSamplerFamilyTableOneHot.program l)

theorem oh_run (ι : Fin 4 ↪ K) (S : K → List Bool) (i w : ℕ) (hi : i < w)
    (h0 : S (ι 0) = List.replicate i true)
    (h1 : S (ι 1) = List.replicate w true) (h2 : S (ι 2) = []) :
    ((advance (ohProgram ι))^[ohTime i w])
      (⟨some .start, none, S⟩ : TM2.Cfg (fun _ : K => Bool)
        PrimeSamplerFamilyTableOneHot.Label (Option Bool)) =
      ⟨none, none, Function.update (Function.update (Function.update S (ι 0) [])
        (ι 1) []) (ι 3) (MatrixStage4FamilyData.oneHot w ⟨i, hi⟩ ++ S (ι 3))⟩ := by
  let c := PrimeSamplerFamilyTableOneHot.cfg (some .start) none
    (List.replicate i true) (List.replicate w true) [] (S (ι 3))
  have hstart : stackCfg ι S c =
      (⟨some .start, none, S⟩ : TM2.Cfg (fun _ : K => Bool)
        PrimeSamplerFamilyTableOneHot.Label (Option Bool)) := by
    simp only [stackCfg, c, PrimeSamplerFamilyTableOneHot.cfg]
    congr 1
    apply bank_eq_self
    intro k
    fin_cases k <;> simp [h0, h1, h2]
  have hrun := BitMachineStackRun.run ι S PrimeSamplerFamilyTableOneHot.program c
    (ohTime i w)
  rw [hstart] at hrun
  have he := onehot_local i w hi (S (ι 3))
  unfold ohProgram
  rw [hrun]
  change stackCfg ι S (PrimeSamplerFamilyTableOneHot.run (ohTime i w) c) = _
  rw [he]
  simp only [stackCfg, PrimeSamplerFamilyTableOneHot.cfg]
  congr 1
  have hloc : (![[], [], [], MatrixStage4FamilyData.oneHot w ⟨i, hi⟩ ++ S (ι 3)] :
      Fin 4 → List Bool) =
      Function.update (Function.update (Function.update (fun k => S (ι k)) 0 [])
        1 []) 3 (MatrixStage4FamilyData.oneHot w ⟨i, hi⟩ ++ S (ι 3)) := by
    funext k
    fin_cases k <;> simp [h2]
  rw [hloc, bank_update, bank_update, bank_update, bank_restrict]

end OneHotEmbedded

/-! ## Exact whole-bank run of the admitted entry accessor -/

section Entry

open PrimeSamplerEntryMachine

theorem entry_exact (p t l j m : ℕ) (hp : 0 < p) (hj : j < p) (hl : l < p ^ t) :
    ∃ n ≤ timeBound p t l j m,
      PrimeSamplerEntryMachine.run n (PrimeSamplerEntryMachine.cfg
        (some (.inl (.inr .loop)))
        ![unary l, unary p, [], [], [], [], unary t, [], unary j, [], unary m]) =
      PrimeSamplerEntryMachine.cfg none
        ![unary j, [], [], [], unary (PrimeSampler.entry p t m l j), [], unary p,
          unary (PrimeSamplerEntryAlgorithm.horner p j t l / m), [], [], unary m] := by
  obtain ⟨a, ha, he⟩ := extract_run p t l j m hl
  have htransfer := transfer_run p j m (PrimeSamplerDigits.digits p t l [])
  obtain ⟨b, hb, hh⟩ := horner_run p t l j m hp hj
  obtain ⟨c, hc, hr⟩ := reduction_run p j (PrimeSamplerEntryAlgorithm.horner p j t l) m
  have hlength := PrimeSamplerEntrySemantics.digit_stream_length p t l hp
  have hvalue := PrimeSamplerEntryAlgorithm.horner_lt p j t l hp
  refine ⟨a + ((j + p + 2 * (PrimeSamplerDigits.digits p t l []).length + 4) + (b + c)),
    ?_, ?_⟩
  · unfold timeBound
    have htwice : 2 * (PrimeSamplerDigits.digits p t l []).length ≤ 2 * t * p := by
      nlinarith [hlength]
    omega
  · rw [run_add he, run_add htransfer, run_add hh, hr, ← PrimeSamplerEntryAlgorithm.entry_eq]
    rfl

end Entry

#print axioms copy_blank
#print axioms div_run
#print axioms onehot_local
#print axioms oh_run
#print axioms entry_exact

end EthInapproximability.CurrentPaper.FamilyRowGeneric
