import Paper2.CanonicalDefaultWord
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-! Unit 3, segments (3)/(5), a piece of the canonical default tails
(PARTIAL): the COLUMN round of the canonical default-word recursion, which the
production `CanonicalDefaultWordScratch.RowMachine` (row round only) does not
provide. `CanonicalDefaultWordScratch.successor_words`:

  words (k+1) = (repeatWord Q ([F,T,T,F] ++ repeatWord (q₁+s+1) (words k).2),
                 [F] ++ repeatWord w ([T,F,F,F] ++ (words k).1))

ONE fixed program: copy the level-`k` row word `r` (source-preserving),
push the four header bits `[T,F,F,F]` in front, copy the unary `w`, run the
production repeat-stream machine `SourceNormalizationMachineRepeatStream`
(`repeat_run`, reused by name), push the leading `false`. It halts with
exactly `[false] ++ repeatWord w ([true,false,false,false] ++ r)` in its
output cell; with `r = (words k).1` this is `(words (k+1)).2`, the level-`k+1`
canonical default tail word (`canonical_tail_encoded`). Imports production
modules only. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Paper2.DefaultColumnRound

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open BitMachineRawSequence (leftLabel)
open Paper2.CanonicalDefaultWordScratch (repeatWord words successor_words)

abbrev RS := SourceNormalizationMachineRepeatStream.Stack
/-- Repeat-stream cells (source, scratch, counter, output, payload) beside
(row word `r`, unary `w`, copy scratch). -/
abbrev K := RS ⊕ Fin 3

def B (a b c d e r w z : List Bool) : K → List Bool := Sum.elim ![a, b, c, d, e] ![r, w, z]

def iR : RS ↪ K := ⟨Sum.inl, Sum.inl_injective⟩

def slots (a b : K) (h : Function.Injective ![a, b, (.inr 2 : K)]) : Fin 3 ↪ K :=
  ⟨![a, b, .inr 2], h⟩
def rSlots : Fin 3 ↪ K := slots (.inr 0) (.inl 0) (by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all)
def wSlots : Fin 3 ↪ K := slots (.inr 1) (.inl 2) (by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all)

def pushB (k : K) (b : Bool) : Unit → TM2.Stmt (fun _ : K => Bool) Unit Unit :=
  fun _ => push k (fun _ => b) halt

theorem pushB_run (k : K) (b : Bool) (S : K → List Bool) :
    ((advance (pushB k b))^[1]) (⟨some (), (), S⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
      ⟨none, (), Function.update S k (b :: S k)⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, pushB]

def cpR := MatrixStage4ScalarPreparationOps.copyProgram rSlots
def cpW := MatrixStage4ScalarPreparationOps.copyProgram wSlots
def rsP := fun l => stackStmt iR (SourceNormalizationMachineRepeatStream.program l)

abbrev oc := (none : Option Bool)
def d1 := BitMachineRawSequence.program cpR (pushB (.inl 0) false) () oc ()
def d2 := BitMachineRawSequence.program d1 (pushB (.inl 0) false) () (oc, ()) ()
def d3 := BitMachineRawSequence.program d2 (pushB (.inl 0) false) () ((oc, ()), ()) ()
def d4 := BitMachineRawSequence.program d3 (pushB (.inl 0) true) () (((oc, ()), ()), ()) ()
def d5 := BitMachineRawSequence.program d4 cpW .scan ((((oc, ()), ()), ()), ()) oc
def d6 := BitMachineRawSequence.program d5 rsP .next (((((oc, ()), ()), ()), ()), oc) oc
/-- The column round: ONE fixed program. -/
def program := BitMachineRawSequence.program d6 (pushB (.inl 3) false) ()
  ((((((oc, ()), ()), ()), ()), oc), oc) ()

def startCtl := (((((((oc, ()), ()), ()), ()), oc), oc), ())

theorem lift {Kk L V : Type*} [DecidableEq Kk] (ι : Kk ↪ K)
    (P : L → TM2.Stmt (fun _ : Kk => Bool) L V)
    (W : K → List Bool) (S T : Kk → List Bool) (hS : ∀ k, S k = W (ι k)) (l : L) (v v' : V)
    (t : ℕ)
    (hrun : ((advance P)^[t]) (⟨some l, v, S⟩ : TM2.Cfg (fun _ : Kk => Bool) L V) =
      ⟨none, v', T⟩) :
    ((advance (fun l => stackStmt ι (P l)))^[t])
        (⟨some l, v, W⟩ : TM2.Cfg (fun _ : K => Bool) L V) =
      ⟨none, v', bank ι W T⟩ := by
  have hs := BitMachineStackRun.run ι W P (⟨some l, v, S⟩ : TM2.Cfg (fun _ : Kk => Bool) L V) t
  rw [hrun] at hs
  simp only [stackCfg] at hs
  rwa [bank_eq_self ι W S hS] at hs

theorem upd0 (a b c d e r w z x : List Bool) :
    Function.update (B a b c d e r w z) (.inl 0) x = B x b c d e r w z := by
  funext j; rcases j with j | j <;> fin_cases j <;> rfl
theorem upd2 (a b c d e r w z x : List Bool) :
    Function.update (B a b c d e r w z) (.inl 2) x = B a b x d e r w z := by
  funext j; rcases j with j | j <;> fin_cases j <;> rfl
theorem upd3 (a b c d e r w z x : List Bool) :
    Function.update (B a b c d e r w z) (.inl 3) x = B a b c x e r w z := by
  funext j; rcases j with j | j <;> fin_cases j <;> rfl

theorem column_round_run (r : List Bool) (w : ℕ) :
    let hw := [true, false, false, false] ++ r
    ∃ t ≤ (2 * r.length + 2) + 4 + (2 * w + 2) + (w * (2 * hw.length + 3) + 1) + 1 + 7,
      ((advance program)^[t])
        (⟨some (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel
          (leftLabel BitMachineCopy.Label.scan))))))), startCtl,
          B [] [] [] [] [] r (List.replicate w true) []⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, startCtl, B hw [] [] ([false] ++ repeatWord w hw) [] r
          (List.replicate w true) []⟩ := by
  intro hw
  have p1 := MatrixStage4ScalarPreparationOps.copy_run rSlots
    (B [] [] [] [] [] r (List.replicate w true) []) rfl
  rw [show (B [] [] [] [] [] r (List.replicate w true) []) (rSlots 0) = r from rfl,
    show (B [] [] [] [] [] r (List.replicate w true) []) (rSlots 1) = [] from rfl,
    List.append_nil, show rSlots 1 = .inl 0 from rfl, upd0] at p1
  have p2 := pushB_run (.inl 0) false (B r [] [] [] [] r (List.replicate w true) [])
  rw [show (B r [] [] [] [] r (List.replicate w true) []) (.inl 0) = r from rfl, upd0] at p2
  have p3 := pushB_run (.inl 0) false (B (false :: r) [] [] [] [] r (List.replicate w true) [])
  rw [show (B (false :: r) [] [] [] [] r (List.replicate w true) []) (.inl 0) = false :: r
    from rfl, upd0] at p3
  have p4 := pushB_run (.inl 0) false
    (B (false :: false :: r) [] [] [] [] r (List.replicate w true) [])
  rw [show (B (false :: false :: r) [] [] [] [] r (List.replicate w true) []) (.inl 0) =
    false :: false :: r from rfl, upd0] at p4
  have p5 := pushB_run (.inl 0) true
    (B (false :: false :: false :: r) [] [] [] [] r (List.replicate w true) [])
  rw [show (B (false :: false :: false :: r) [] [] [] [] r (List.replicate w true) []) (.inl 0) =
    false :: false :: false :: r from rfl, upd0] at p5
  have p6 := MatrixStage4ScalarPreparationOps.copy_run wSlots
    (B hw [] [] [] [] r (List.replicate w true) []) rfl
  rw [show (B hw [] [] [] [] r (List.replicate w true) []) (wSlots 0) = List.replicate w true
      from rfl,
    show (B hw [] [] [] [] r (List.replicate w true) []) (wSlots 1) = [] from rfl,
    List.append_nil, show wSlots 1 = .inl 2 from rfl, upd2, List.length_replicate] at p6
  have p7raw := SourceNormalizationMachineRepeatStream.repeat_run hw [] [] w none
  simp only [SourceNormalizationMachineRepeatStream.run,
    SourceNormalizationMachineRepeatStream.cfg, List.append_nil] at p7raw
  have p7 := lift iR SourceNormalizationMachineRepeatStream.program
    (B hw [] (List.replicate w true) [] [] r (List.replicate w true) []) _ _
    (fun k => by fin_cases k <;> rfl) _ _ _ _ p7raw
  have hb7 : bank iR (B hw [] (List.replicate w true) [] [] r (List.replicate w true) [])
      ![hw, [], [], SourceNormalizationMachineRepeatStream.repeated hw w, []] =
      B hw [] [] (repeatWord w hw) [] r (List.replicate w true) [] := by
    funext j
    rcases j with j | j
    · rw [show (Sum.inl j : K) = iR j from rfl, bank_at]
      fin_cases j
      · rfl
      · rfl
      · rfl
      · exact Paper2.CanonicalDefaultWordScratch.repeated_eq_repeatWord hw w
      · rfl
    · exact bank_outside iR _ _ _ (by rintro ⟨k, hk⟩; exact Sum.inl_ne_inr hk)
  rw [hb7] at p7
  have p8 := pushB_run (.inl 3) false (B hw [] [] (repeatWord w hw) [] r (List.replicate w true) [])
  rw [show (B hw [] [] (repeatWord w hw) [] r (List.replicate w true) []) (.inl 3) =
    repeatWord w hw from rfl, upd3] at p8
  obtain ⟨u1, hu1, q1⟩ := BitMachineRawSequence.runs cpR (pushB (.inl 0) false) .scan ()
    oc oc () () _ _ _ _ _ p1 p2
  obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs d1 (pushB (.inl 0) false) _ ()
    (oc, ()) _ () () _ _ _ _ _ q1 p3
  obtain ⟨u3, hu3, q3⟩ := BitMachineRawSequence.runs d2 (pushB (.inl 0) false) _ ()
    ((oc, ()), ()) _ () () _ _ _ _ _ q2 p4
  obtain ⟨u4, hu4, q4⟩ := BitMachineRawSequence.runs d3 (pushB (.inl 0) true) _ ()
    (((oc, ()), ()), ()) _ () () _ _ _ _ _ q3 p5
  obtain ⟨u5, hu5, q5⟩ := BitMachineRawSequence.runs d4 cpW _ .scan
    ((((oc, ()), ()), ()), ()) _ oc oc _ _ _ _ _ q4 p6
  obtain ⟨u6, hu6, q6⟩ := BitMachineRawSequence.runs d5 rsP _ .next
    (((((oc, ()), ()), ()), ()), oc) _ oc oc _ _ _ _ _ q5 p7
  obtain ⟨u7, hu7, q7⟩ := BitMachineRawSequence.runs d6 (pushB (.inl 3) false) _ ()
    ((((((oc, ()), ()), ()), ()), oc), oc) _ () () _ _ _ _ _ q6 p8
  refine ⟨u7, ?_, q7⟩
  omega

/-- Same-object identity: started on the level-`k` canonical default row word,
the output cell ends with exactly the level-`k+1` canonical default column
(tail) word. -/
theorem column_round_words (p s q₁ q₂ w Q k : ℕ) :
    [false] ++ repeatWord w ([true, false, false, false] ++ (words p s q₁ q₂ w Q k).1) =
      (words p s q₁ q₂ w Q (k + 1)).2 := by
  rw [successor_words]

end

#print axioms pushB_run
#print axioms lift
#print axioms column_round_run
#print axioms column_round_words

end Paper2.DefaultColumnRound
