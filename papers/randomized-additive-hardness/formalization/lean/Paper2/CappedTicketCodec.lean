import Paper2.CappedLoopCleanup
import Paper2.RecursiveLabelCodec
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.BitMachineSubroutine
import Mathlib.Tactic

namespace Paper2.TicketWordScratch

set_option maxRecDepth 16384

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineComposition

abbrev Stack := Fin 10 ⊕ Fin 1
def result : Stack := .inl 9
def accumulator : Stack := .inr 0

inductive Label where
  | first | tally
  deriving DecidableEq, Fintype

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .first =>
      pop result (fun _ b => b)
        (branch Option.isSome
          (push accumulator (fun _ => false) (goto (fun _ => .tally)))
          (load (fun _ => none) halt))
  | .tally =>
      pop result (fun _ b => b)
        (branch Option.isSome
          (push accumulator (fun _ => true) (goto (fun _ => .tally)))
          (load (fun _ => none) halt))

def bank (S : Fin 10 → List Bool) (acc : List Bool) : Stack → List Bool :=
  Sum.elim S (fun _ => acc)

def cfg (l : Option Label) (v : Option Bool) (S : Fin 10 → List Bool)
    (acc : List Bool) : TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool) :=
  ⟨l, v, bank S acc⟩

private theorem first_abort (S : Fin 10 → List Bool) (acc : List Bool)
    (h : S 9 = []) :
    advance program (cfg (some .first) none S acc) = cfg none none S acc := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg, bank, result, h]
  simp only [Sum.elim_inl, h, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => by_cases hk : k = 9 <;> simp [Function.update, hk, h]
  | inr k => fin_cases k <;> simp [Function.update]

private theorem first_success (S : Fin 10 → List Bool) (acc : List Bool)
    (q : List Bool) (h : S 9 = true :: q) :
    advance program (cfg (some .first) none S acc) =
      cfg (some .tally) (some true) (Function.update S 9 q) (false :: acc) := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg, bank,
    result, accumulator, h]
  simp only [Sum.elim_inl, h, List.head?_cons, List.tail_cons,
    Option.isSome_some, Bool.cond_true, Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => simp [bank, Function.update]
  | inr k => fin_cases k <;> rfl

private theorem tally_success (S : Fin 10 → List Bool) (acc : List Bool)
    (q : List Bool) (h : S 9 = true :: q) :
    advance program (cfg (some .tally) (some true) S acc) =
      cfg (some .tally) (some true) (Function.update S 9 q) (true :: acc) := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg, bank,
    result, accumulator, h]
  simp only [Sum.elim_inl, h, List.head?_cons, List.tail_cons,
    Option.isSome_some, Bool.cond_true, Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => simp [bank, Function.update]
  | inr k => fin_cases k <;> rfl

private theorem tally_done (S : Fin 10 → List Bool) (acc : List Bool)
    (h : S 9 = []) :
    advance program (cfg (some .tally) (some true) S acc) = cfg none none S acc := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg, bank, result, h]
  simp only [Sum.elim_inl, h, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => by_cases hk : k = 9 <;> simp [Function.update, hk, h]
  | inr k => fin_cases k <;> simp [Function.update]

theorem abort (S : Fin 10 → List Bool) (acc : List Bool) (h : S 9 = []) :
    ((advance program)^[1]) (cfg (some .first) none S acc) =
      cfg none none S acc := by simpa using first_abort S acc h

theorem tally (q : ℕ) (S : Fin 10 → List Bool) (acc : List Bool)
    (h : S 9 = List.replicate q true) :
    ((advance program)^[q+1]) (cfg (some .tally) (some true) S acc) =
      cfg none none (Function.update S 9 []) (List.replicate q true ++ acc) := by
  induction q generalizing S acc with
  | zero =>
      have hn : S 9 = [] := by simpa using h
      simpa [show Function.update S 9 [] = S by funext k; by_cases hk : k = 9 <;> simp [Function.update, hk, hn]]
        using tally_done S acc hn
  | succ q ih =>
      have hc : S 9 = true :: List.replicate q true := by simpa using h
      have hs := tally_success S acc (List.replicate q true) hc
      rw [show q + 1 + 1 = (q+1)+1 by omega,
        Function.iterate_succ_apply, hs]
      have hh : (Function.update S 9 (List.replicate q true)) 9 =
          List.replicate q true := by simp
      rw [ih _ _ hh]
      simp [Function.update_idem, List.replicate_succ', List.append_assoc]

theorem success (q : ℕ) (S : Fin 10 → List Bool) (acc : List Bool)
    (h : S 9 = true :: List.replicate q true) :
    ((advance program)^[q+2]) (cfg (some .first) none S acc) =
      cfg none none (Function.update S 9 [])
        (List.replicate q true ++ [false] ++ acc) := by
  have hs := first_success S acc (List.replicate q true) h
  have ht := tally q (Function.update S 9 (List.replicate q true)) (false :: acc)
    (by simp)
  rw [show q+2 = (q+1)+1 by omega, Function.iterate_succ_apply, hs, ht]
  simp [Function.update_idem, List.append_assoc]

abbrev DrawLabel :=
  BitMachineRawSequence.Label
    (BitMachineRawSequence.Label (BitMachineRawSequence.Label CappedLoop.WideProjection.Label
      CappedLoop.WideProjection.Prepare.Label)
      (BitMachineRawSequence.Label CappedLoop.Comparator.Label CappedLoop.Drain.Label))
    CappedLoop.Cleanup.Label
abbrev DrawControl :=
  BitMachineRawSequence.Control
    (BitMachineRawSequence.Control (BitMachineRawSequence.Control CappedLoop.WideProjection.Control
      CappedLoop.WideProjection.Control)
      (BitMachineRawSequence.Control CappedLoop.Comparator.Control CappedLoop.Drain.Control))
    CappedLoop.Cleanup.Control

def drawLift : DrawLabel ⊕ Unit →
    TM2.Stmt (fun _ : Stack => Bool) (DrawLabel ⊕ Unit) (DrawControl × Unit)
  | .inl l => liftStmt none (CappedLoop.Cleanup.readyProgram l)
  | .inr _ => halt

def drawStart : DrawLabel :=
  BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel CappedLoop.WideProjection.Label.start))

def drawInitial : DrawControl :=
  ((((none,false),(none,false)),((none,false),(none,false))), ((),none))

def fullProgram := BitMachineRawSequence.program drawLift program Label.first
  (drawInitial, ()) (none : Option Bool)

theorem compose_abort (S T : Fin 10 → List Bool) (acc : List Bool)
    (ta : ℕ)
    (ha : ((advance CappedLoop.Cleanup.readyProgram)^[ta])
      (⟨some drawStart, drawInitial, S⟩ : TM2.Cfg (fun _ : Fin 10 => Bool)
        DrawLabel DrawControl) = ⟨none, drawInitial, T⟩)
    (hout : T 9 = []) :
    ∃ t ≤ ta + 2,
      ((advance fullProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.inl drawStart)),
          ((drawInitial, ()), none), bank S acc⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, ((drawInitial, ()), none), bank T acc⟩ := by
  have hh : (((advance CappedLoop.Cleanup.readyProgram)^[ta])
      (⟨some drawStart, drawInitial, S⟩ : TM2.Cfg (fun _ : Fin 10 => Bool)
        DrawLabel DrawControl)).l = none := by rw [ha]
  obtain ⟨td, htd, hd⟩ := BitMachineSubroutine.lift_outputs
    CappedLoop.Cleanup.readyProgram drawLift none (by intro l; rfl)
    () (fun _ : Fin 1 => acc)
    (⟨some drawStart, drawInitial, S⟩ : TM2.Cfg (fun _ : Fin 10 => Bool)
      DrawLabel DrawControl) ta hh
  have hdraw : ((advance drawLift)^[td])
      (⟨some (.inl drawStart), (drawInitial, ()), bank S acc⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, (drawInitial, ()), bank T acc⟩ := by
    simpa [BitMachineComposition.liftCfg, bank, ha] using hd
  have hemit := abort T acc hout
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs drawLift program (.inl drawStart) Label.first
    (drawInitial, ()) (drawInitial, ()) none none
    (bank S acc) (bank T acc) (bank T acc) td 1 hdraw hemit
  exact ⟨t, by omega, hr⟩

theorem compose_success (q : ℕ) (S T : Fin 10 → List Bool) (acc : List Bool)
    (ta : ℕ)
    (ha : ((advance CappedLoop.Cleanup.readyProgram)^[ta])
      (⟨some drawStart, drawInitial, S⟩ : TM2.Cfg (fun _ : Fin 10 => Bool)
        DrawLabel DrawControl) = ⟨none, drawInitial, T⟩)
    (hout : T 9 = true :: List.replicate q true) :
    ∃ t ≤ ta + q + 3,
      ((advance fullProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.inl drawStart)),
          ((drawInitial, ()), none), bank S acc⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, ((drawInitial, ()), none),
          bank (Function.update T 9 [])
            (List.replicate q true ++ [false] ++ acc)⟩ := by
  have hh : (((advance CappedLoop.Cleanup.readyProgram)^[ta])
      (⟨some drawStart, drawInitial, S⟩ : TM2.Cfg (fun _ : Fin 10 => Bool)
        DrawLabel DrawControl)).l = none := by rw [ha]
  obtain ⟨td, htd, hd⟩ := BitMachineSubroutine.lift_outputs
    CappedLoop.Cleanup.readyProgram drawLift none (by intro l; rfl)
    () (fun _ : Fin 1 => acc)
    (⟨some drawStart, drawInitial, S⟩ : TM2.Cfg (fun _ : Fin 10 => Bool)
      DrawLabel DrawControl) ta hh
  have hdraw : ((advance drawLift)^[td])
      (⟨some (.inl drawStart), (drawInitial, ()), bank S acc⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, (drawInitial, ()), bank T acc⟩ := by
    simpa [BitMachineComposition.liftCfg, bank, ha] using hd
  have hemit := success q T acc hout
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs drawLift program (.inl drawStart) Label.first
    (drawInitial, ()) (drawInitial, ()) none none
    (bank S acc) (bank T acc)
    (bank (Function.update T 9 []) (List.replicate q true ++ [false] ++ acc))
    td (q+2) hdraw hemit
  exact ⟨t, by omega, hr⟩

def drawBound (D B R : ℕ) : ℕ :=
  R * (2 * B + Nat.clog 2 D + 6) + 3 +
    (D - 1 + (B - Nat.clog 2 D) + 2) +
    (R * (CappedLoop.Comparator.attemptBound D + (2 * Nat.clog 2 D + 3)) + 3) + 2 +
    2 * Nat.clog 2 D + 2 * (D-1) + 11

def emptyBank (suffix : List Bool) : Fin 10 → List Bool :=
  CappedLoop.Comparator.bank suffix [] [] [] [] [] [] [] [] []

private theorem erase_result (suffix out : List Bool) :
    Function.update (CappedLoop.Comparator.bank suffix [] [] [] [] [] [] [] [] out)
      9 [] = emptyBank suffix := by
  funext k
  fin_cases k <;> simp [CappedLoop.Comparator.bank, emptyBank, Function.update]

/-- The actual serialized source tape is consumed, not a caller-supplied
terminal result. Stack 0 retains its exact next-draw suffix; the marker and
all tally bits are physically removed from stack 9. -/
theorem source_ticket (D B R N : ℕ) (hD : 0 < D)
    (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1)) (acc : List Bool) :
    ∃ t out,
      t ≤ drawBound D B R + out.length + 2 ∧
      ((advance fullProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.inl drawStart)),
          ((drawInitial, ()), none),
          bank
            (CappedLoop.WideProjection.bank
              (RecursiveSamplingTape.writeTape B R (N+1) tape).val
              (List.replicate (Nat.clog 2 D) true) [] []
              (List.replicate (B - Nat.clog 2 D) true) (List.replicate R true)
              [] [] (List.replicate (D-1) true) []) acc⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, ((drawInitial, ()), none),
          bank (emptyBank (RecursiveSamplingTape.writeTape B R N tape.2).val)
            (match (CappedSampler.runWideBits D B R hB tape.1).map Fin.val with
              | none => acc
              | some q => List.replicate q true ++ [false] ++ acc)⟩ ∧
      out = match (CappedSampler.runWideBits D B R hB tape.1).map Fin.val with
        | none => []
        | some q => true :: List.replicate q true := by
  obtain ⟨ta, out, hta, hra, hout⟩ :=
    CappedLoop.Cleanup.source_draw_ready D B R N hD hB tape
  let S := CappedLoop.WideProjection.bank
    (RecursiveSamplingTape.writeTape B R (N+1) tape).val
    (List.replicate (Nat.clog 2 D) true) [] []
    (List.replicate (B - Nat.clog 2 D) true) (List.replicate R true)
    [] [] (List.replicate (D-1) true) []
  let T := CappedLoop.Comparator.bank
    (RecursiveSamplingTape.writeTape B R N tape.2).val
    [] [] [] [] [] [] [] [] out
  have hr : ((advance CappedLoop.Cleanup.readyProgram)^[ta])
      (⟨some drawStart, drawInitial, S⟩ : TM2.Cfg (fun _ : Fin 10 => Bool)
        DrawLabel DrawControl) = ⟨none, drawInitial, T⟩ := hra
  cases hc : (CappedSampler.runWideBits D B R hB tape.1).map Fin.val with
  | none =>
      rw [hc] at hout
      have ho : out = [] := by simpa [hc] using hout
      have h9 : T 9 = [] := by simp [T, CappedLoop.Comparator.bank, ho]
      obtain ⟨t, ht, hx⟩ := compose_abort S T acc ta hr h9
      refine ⟨t, out, ?_, ?_, hout⟩
      · simp [drawBound, ho] at hta ⊢
        omega
      · simpa [S, T, ho, emptyBank, hc] using hx
  | some q =>
      rw [hc] at hout
      have ho : out = true :: List.replicate q true := by simpa [hc] using hout
      have h9 : T 9 = true :: List.replicate q true := by
        simp [T, CappedLoop.Comparator.bank, ho]
      obtain ⟨t, ht, hx⟩ := compose_success q S T acc ta hr h9
      refine ⟨t, out, ?_, ?_, hout⟩
      · simp [drawBound, ho] at hta ⊢
        omega
      · simpa [S, T, erase_result, hc] using hx

def sourceInitialBank (D B R N : ℕ)
    (tape : CappedSampler.Adaptive.Tape B R (N+1)) : Fin 10 → List Bool :=
  CappedLoop.WideProjection.bank
    (RecursiveSamplingTape.writeTape B R (N+1) tape).val
    (List.replicate (Nat.clog 2 D) true) [] []
    (List.replicate (B - Nat.clog 2 D) true) (List.replicate R true)
    [] [] (List.replicate (D-1) true) []

theorem source_ticket_codec (D B R N : ℕ) (hD : 0 < D)
    (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1)) (acc : List Bool) :
    ∃ t ≤ drawBound D B R + D + 2,
      ((advance fullProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.inl drawStart)),
          ((drawInitial, ()), none), bank (sourceInitialBank D B R N tape) acc⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, ((drawInitial, ()), none),
          bank (emptyBank (RecursiveSamplingTape.writeTape B R N tape.2).val)
            (match CappedSampler.runWideBits D B R hB tape.1 with
              | none => acc
              | some q => (RecursiveLabelCodecScratch.finCodec D).encode q ++ acc)⟩ := by
  obtain ⟨t, out, ht, hr, hout⟩ := source_ticket D B R N hD hB tape acc
  have hlen : out.length ≤ D := by
    cases hc : CappedSampler.runWideBits D B R hB tape.1 with
    | none =>
        simp [hc] at hout
        simp [hout]
    | some q =>
        simp [hc] at hout
        simp [hout]
  refine ⟨t, by omega, ?_⟩
  have hcode :
      (match (CappedSampler.runWideBits D B R hB tape.1).map Fin.val with
        | none => acc
        | some q => List.replicate q true ++ [false] ++ acc) =
      (match CappedSampler.runWideBits D B R hB tape.1 with
        | none => acc
        | some q => (RecursiveLabelCodecScratch.finCodec D).encode q ++ acc) := by
    cases hc : CappedSampler.runWideBits D B R hB tape.1 with
    | none => simp [hc]
    | some q => simp [hc, RecursiveLabelCodecScratch.finCodec, List.append_assoc]
  rw [← hcode]
  simpa only [sourceInitialBank] using hr

end Paper2.TicketWordScratch

#print axioms Paper2.TicketWordScratch.source_ticket_codec
#print axioms Paper2.TicketWordScratch.source_ticket
#print axioms Paper2.TicketWordScratch.success
