import Paper2.DefaultWordLevels

/-! The physical seed of the default-word level loop: from unary `p` (in the
repeat-stream counter cell) ONE fixed program produces `words 0 =
(replicate p false, [false])` in the level cells (production
`physical_seed_row`, reused by name, plus charged pushes, a copy and clears),
then runs `levelLoop`. The composite `default_words_run` therefore starts
from unary `p, q₁, s, Q, w` and `j` counter marks only. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.DefaultWordLoop

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open BitMachineRawSequence (leftLabel)
open Paper2.CanonicalDefaultWordScratch (repeatWord words successor_words)

def pushL (k : LB) (b : Bool) : Unit → TM2.Stmt (fun _ : LB => Bool) Unit Unit :=
  fun _ => push k (fun _ => b) halt

theorem pushL_run (k : LB) (b : Bool) (S : LB → List Bool) :
    ((advance (pushL k b))^[1]) (⟨some (), (), S⟩ : TM2.Cfg (fun _ : LB => Bool) _ _) =
      ⟨none, (), Function.update S k (b :: S k)⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, pushL]

def iRS : SourceNormalizationMachineRepeatStream.Stack ↪ LB :=
  ⟨fun x => .inr (.inl (.inl x)), fun a b h => by simpa using h⟩

def rsL := fun l => stackStmt iRS (SourceNormalizationMachineRepeatStream.program l)

def seedSlots : Fin 3 ↪ LB := ⟨![crOut, crR, scr], by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [crOut, crR, scr]⟩
def cpSeed := MatrixStage4ScalarPreparationOps.copyProgram seedSlots

abbrev ocs := (none : Option Bool)
def f1 := ((), ocs)
def f2 := (f1, ocs)
def f3 := (f2, ocs)
def f4 := (f3, ocs)
def seedCtl := (f4, ())
def e1 := BitMachineRawSequence.program (pushL crJ false) rsL .next () ocs
def e2 := BitMachineRawSequence.program e1 cpSeed .scan f1 ocs
def e3 := BitMachineRawSequence.program e2 (clr crOut) () f2 ocs
def e4 := BitMachineRawSequence.program e3 (clr crJ) () f3 ocs
/-- Seed program: ONE fixed program. -/
def seedP := BitMachineRawSequence.program e4 (pushL (.inl 3) false) () f4 ()

/-- Entry bank: unary `q₁, s, Q` (row machine), unary `p` in the repeat-stream
counter, unary `w`, and `j` counter marks; all words blank. -/
def entry (p q₁ s Q w j : ℕ) : LB → List Bool :=
  bk (CanonicalDefaultWordScratch.RowMachine.B (List.replicate q₁ true) (List.replicate s true)
      (List.replicate Q true) [] [] [] [] [] [] [])
    (DefaultColumnRound.B [] [] (List.replicate p true) [] [] [] (List.replicate w true) [])
    ![List.replicate j true, []]

theorem seed_run (p q₁ s Q w j : ℕ) :
    ∃ t ≤ 1 + (p * 5 + 1) + (2 * p + 2) + (p + 1) + 2 + 1 + 5,
      ((advance seedP)^[t])
        (⟨some (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel ()))))),
          seedCtl, entry p q₁ s Q w j⟩ :
          TM2.Cfg (fun _ : LB => Bool) _ _) =
        ⟨none, seedCtl,
          S q₁ s Q w (List.replicate p false) [false] (List.replicate j true)⟩ := by
  let A0 := CanonicalDefaultWordScratch.RowMachine.B (List.replicate q₁ true)
    (List.replicate s true) (List.replicate Q true) [] [] [] [] [] [] []
  let D0 : Fin 2 → List Bool := ![List.replicate j true, []]
  have p1 := pushL_run crJ false (entry p q₁ s Q w j)
  rw [show crJ = .inr (.inl (.inl 0)) from rfl, show entry p q₁ s Q w j = bk A0
    (DefaultColumnRound.B [] [] (List.replicate p true) [] [] [] (List.replicate w true) []) D0
    from rfl, upd_CR] at p1
  let B1 := Function.update
    (DefaultColumnRound.B [] [] (List.replicate p true) [] [] [] (List.replicate w true) [])
    (.inl 0) [false]
  have h2 := CanonicalDefaultWordScratch.physical_seed_row p [] []
  simp only [SourceNormalizationMachineRepeatStream.run,
    SourceNormalizationMachineRepeatStream.cfg, List.append_nil] at h2
  have l2 := lift iRS SourceNormalizationMachineRepeatStream.program (bk A0 B1 D0) _ _
    (fun k => by fin_cases k <;> rfl) _ _ _ _ h2
  have hb2 : bank iRS (bk A0 B1 D0) ![[false], [], [], List.replicate p false, []] =
      bk A0 (DefaultColumnRound.B [false] [] [] (List.replicate p false) [] []
        (List.replicate w true) []) D0 := by
    funext j'
    rcases j' with j' | (j' | j') | j'
    · exact bank_outside iRS _ _ _ (by rintro ⟨k, hk⟩; exact Sum.inr_ne_inl hk)
    · exact (bank_at iRS _ _ j').trans (by fin_cases j' <;> rfl)
    · exact (bank_outside iRS _ _ _ (by
        rintro ⟨k, hk⟩
        exact Sum.inl_ne_inr (Sum.inl_injective (Sum.inr_injective hk)))).trans
        (by fin_cases j' <;> rfl)
    · exact bank_outside iRS _ _ _ (by
        rintro ⟨k, hk⟩
        exact Sum.inl_ne_inr (Sum.inr_injective hk))
  rw [hb2] at l2
  let B2 := DefaultColumnRound.B [false] [] [] (List.replicate p false) [] []
    (List.replicate w true) []
  have p3 := MatrixStage4ScalarPreparationOps.copy_run seedSlots (bk A0 B2 D0) rfl
  rw [show (bk A0 B2 D0) (seedSlots 0) = List.replicate p false from rfl,
    show (bk A0 B2 D0) (seedSlots 1) = [] from rfl, List.append_nil,
    show seedSlots 1 = .inr (.inl (.inr 0)) from rfl, upd_CR, List.length_replicate] at p3
  let B3 := Function.update B2 (.inr 0) (List.replicate p false)
  have p4 := clr_run crOut (List.replicate p false) (bk A0 B3 D0) ocs rfl
  rw [show crOut = .inr (.inl (.inl 3)) from rfl, upd_CR, List.length_replicate] at p4
  let B4 := Function.update B3 (.inl 3) []
  have p5 := clr_run crJ [false] (bk A0 B4 D0) ocs rfl
  rw [show crJ = .inr (.inl (.inl 0)) from rfl, upd_CR] at p5
  let B5 := Function.update B4 (.inl 0) []
  have p6 := pushL_run (.inl 3) false (bk A0 B5 D0)
  rw [upd_RM] at p6
  obtain ⟨u1, hu1, q1⟩ := BitMachineRawSequence.runs (pushL crJ false) rsL () .next () _
    ocs _ _ _ _ _ _ p1 l2
  obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs e1 cpSeed _ .scan f1 _ ocs _
    _ _ _ _ _ q1 p3
  obtain ⟨u3, hu3, q3⟩ := BitMachineRawSequence.runs e2 (clr crOut) _ () f2 _
    ocs _ _ _ _ _ _ q2 p4
  obtain ⟨u4, hu4, q4⟩ := BitMachineRawSequence.runs e3 (clr crJ) _ ()
    f3 _ ocs _ _ _ _ _ _ q3 p5
  obtain ⟨u5, hu5, q5⟩ := BitMachineRawSequence.runs e4 (pushL (.inl 3) false) _ ()
    f4 _ () () _ _ _ _ _ q4 p6
  have hfinal : bk (Function.update A0 3 (false :: bk A0 B5 D0 (.inl 3))) B5 D0 =
      S q₁ s Q w (List.replicate p false) [false] (List.replicate j true) := by
    unfold S bk
    congr 1
    · funext i; fin_cases i <;> rfl
    · congr 1
      funext i
      rcases i with i | i <;> fin_cases i <;> rfl
  rw [hfinal] at q5
  have hl : ([false] : List Bool).length = 1 := rfl
  refine ⟨u5, by omega, q5⟩

/-- Seed, then the level loop: ONE fixed program from unary parameters. -/
def wordsProgram := BitMachineRawSequence.program seedP levelLoop (.inl ())
  seedCtl ((none : Option Bool), bodyCtl)

theorem default_words_run (p s q₁ q₂ w Q j : ℕ) :
    ∃ t ≤ (1 + (p * 5 + 1) + (2 * p + 2) + (p + 1) + 2 + 1 + 5) +
        (j * (levelBound p s q₁ q₂ w Q j + 2) + 1) + 1, ∃ c',
      ((advance wordsProgram)^[t])
        (⟨some (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel ())))))),
          (seedCtl, ((none : Option Bool), bodyCtl)),
          entry p q₁ s Q w j⟩ : TM2.Cfg (fun _ : LB => Bool) _ _) =
        ⟨none, c', S q₁ s Q w (words p s q₁ q₂ w Q j).1 (words p s q₁ q₂ w Q j).2 []⟩ := by
  obtain ⟨t1, ht1, h1⟩ := seed_run p q₁ s Q w j
  obtain ⟨t2, ht2, c2, h2⟩ := level_loop_run p s q₁ q₂ w Q j ((none : Option Bool), bodyCtl)
  have h2' : ((advance levelLoop)^[t2])
      (⟨some (.inl ()), ((none : Option Bool), bodyCtl),
        S q₁ s Q w (List.replicate p false) [false] (List.replicate j true)⟩ :
        TM2.Cfg (fun _ : LB => Bool) _ _) =
      ⟨none, c2, S q₁ s Q w (words p s q₁ q₂ w Q j).1 (words p s q₁ q₂ w Q j).2 []⟩ := h2
  obtain ⟨u, hu, q⟩ := BitMachineRawSequence.runs seedP levelLoop _ (.inl ())
    seedCtl _ ((none : Option Bool), bodyCtl) c2 _ _ _ _ _ h1 h2'
  exact ⟨u, by omega, _, q⟩

end

#print axioms pushL_run
#print axioms seed_run
#print axioms default_words_run

end Paper2.DefaultWordLoop
