import Paper2.OTLoop

/-! Unit 3, segment (1), outer-token equality, GENERIC in the fetch program:
the body and the loop of `OTBody`/`OTLoop` with the fetch step replaced by an
arbitrary program `F` on the `FetchIndexed` bank, given only its checked run
hypothesis (outer word `i` fetched into the label cell, every other cell of the
`FetchIndexed` bank restored). The fixed-tail tag instantiates `F` with
`FetchIndexed.colProgram`; the unrestricted tag with `FetchIndexed.rowProgram`
(skip the `s+1` tail words with the column code, then the outer words with
the outer code). Everything else (programs, banks, clocks) is exactly as in
`OTBody`/`OTLoop`; the premises are hypotheses on `F`, not on the bank. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.OTGen

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open BitMachineRawSequence (leftLabel)
open Paper2.OTOps (u)
open Paper2.OTBody
open Paper2.OTLoop (accL accL_all accL_length cp2Slots Q2 Q4)

variable {LF VF : Type*} (F : LF → TM2.Stmt (fun _ : FetchIndexed.Stack => Bool) LF VF)
  (f0 : LF) (fc : VF)

/-! ### Programs -/

def G1 := fun l => stackStmt fI (F l)
def g1 := BitMachineRawSequence.program (G1 F) P2 () fc ob
def g2 := BitMachineRawSequence.program (g1 F fc) P3 () (fc, ob) ob
def g3 := BitMachineRawSequence.program (g2 F fc) P4 BitMachineCopy.Label.scan ((fc, ob), ob) ob
def g4 := BitMachineRawSequence.program (g3 F fc) P5 OTOps.CL.cmp (((fc, ob), ob), ob)
  ((ob, ob) : OTOps.CCtl)
/-- The generic loop body. -/
def bodyG := BitMachineRawSequence.program (g4 F fc) P6 () ((((fc, ob), ob), ob),
  ((ob, ob) : OTOps.CCtl)) ob
def bodyGStart := FetchIndexed.labelOf (bodyG F fc)
  (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel f0)))))
def bodyGCtl := (((((fc, ob), ob), ob), ((ob, ob) : OTOps.CCtl)), ob)

def h1 := BitMachineRawSequence.program (G1 F) Q2 () fc ob
def h2 := BitMachineRawSequence.program (h1 F fc) P3 () (fc, ob) ob
def h3 := BitMachineRawSequence.program (h2 F fc) Q4 BitMachineCopy.Label.scan ((fc, ob), ob) ob
def loopG := CountedLoop.loop ctrC (bodyG F fc) (bodyGStart F f0 fc) (bodyGCtl fc)
def h4 := BitMachineRawSequence.program (h3 F fc) (loopG F f0 fc) (.inl ())
  (((fc, ob), ob), ob) (ob, bodyGCtl fc)
/-- The generic outer-token equality machine. -/
def fullG := BitMachineRawSequence.program (h4 F f0 fc) (OTOps.fold accC eqC) ()
  ((((fc, ob), ob), ob), (ob, bodyGCtl fc)) ((true, ob) : OTOps.FCtl)
def fullGStart := FetchIndexed.labelOf (fullG F f0 fc)
  (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel f0)))))
def fullGCtl := (((((fc, ob), ob), ob), (ob, bodyGCtl fc)), ((true, ob) : OTOps.FCtl))

/-- A fetch run: outer word `i` = `unary tok ++ false :: rest` lands in the
label cell of the `FetchIndexed` bank, all other cells restored. -/
def FetchRun (fw c1 c2 c3 : List Bool) (i tok : ℕ) (rest : List Bool) (Tf : ℕ) : Prop :=
  ∃ t ≤ Tf, ∃ v, ((advance F)^[t])
      (⟨some f0, fc, FetchIndexed.FB [] [] [] [] fw c1 c2 c3 (List.replicate i true)⟩ :
        TM2.Cfg (fun _ : FetchIndexed.Stack => Bool) LF VF) =
    ⟨none, v, FetchIndexed.FB [] [] [] (List.replicate tok true ++ false :: rest) fw c1 c2 c3
      (List.replicate i true)⟩

def bodyGBound (Tf tok restLen a : ℕ) : ℕ :=
  ((((Tf + (tok + 1) + 1) + (restLen + 1) + 1) + (2 * a + 2) + 1) + (a + tok + 3) + 1) + 1 + 1

theorem bodyG_run (fw c1 c2 c3 : List Bool) (i tok : ℕ) (rest : List Bool) (Tf : ℕ)
    (hF : FetchRun F f0 fc fw c1 c2 c3 i tok rest Tf) (acc ctr sU : List Bool) (a : ℕ) :
    ∃ t ≤ bodyGBound Tf tok rest.length a, ∃ v,
      ((advance (bodyG F fc))^[t])
        (⟨some (bodyGStart F f0 fc), bodyGCtl fc,
          BB [] fw c1 c2 c3 (u i) (u a) [] [] acc ctr [] sU⟩ :
          TM2.Cfg (fun _ : B => Bool) _ _) =
        ⟨none, v, BB [] fw c1 c2 c3 (u (i + 1)) (u a) [] [] (decide (a = tok) :: acc) ctr [] sU⟩ := by
  obtain ⟨t1, ht1, v1, hh1⟩ := hF
  have l1 := lift fI F (BB [] fw c1 c2 c3 (u i) (u a) [] [] acc ctr [] sU) _ _ (fun _ => rfl)
    _ _ _ _ hh1
  have e1 : bank fI (BB [] fw c1 c2 c3 (u i) (u a) [] [] acc ctr [] sU)
      (FetchIndexed.FB [] [] [] (List.replicate tok true ++ false :: rest) fw c1 c2 c3
        (List.replicate i true)) =
      BB (List.replicate tok true ++ false :: rest) fw c1 c2 c3 (u i) (u a) [] [] acc ctr [] sU :=
    bank_fI _ _ _
  rw [e1] at l1
  have hne2 : lblB ≠ tC := by simp [lblB, tC]
  have l2 := RawRowSplit.readU_run lblB tC hne2 tok rest []
    (BB (List.replicate tok true ++ false :: rest) fw c1 c2 c3 (u i) (u a) [] [] acc ctr [] sU)
    none rfl rfl
  rw [upd_lbl, upd_t, List.append_nil] at l2
  have l3 := OTOps.clr_run lblB rest
    (BB rest fw c1 c2 c3 (u i) (u a) (List.replicate tok true) [] acc ctr [] sU) ob rfl
  rw [upd_lbl] at l3
  have l4 := MatrixStage4ScalarPreparationOps.copy_run cpSlots
    (BB [] fw c1 c2 c3 (u i) (u a) (List.replicate tok true) [] acc ctr [] sU) rfl
  have hc0 : cpSlots 0 = aC := rfl
  have hc1 : cpSlots 1 = xC := rfl
  rw [hc0, hc1, BB_a, BB_x, List.append_nil, upd_x] at l4
  have hxt : xC ≠ tC := by simp [xC, tC]
  have hxa : xC ≠ accC := by simp [xC, accC]
  have hta : tC ≠ accC := by simp [tC, accC]
  obtain ⟨t5, ht5, v5, l5⟩ := OTOps.cmp_run xC tC accC hxt hxa hta a tok
    (BB [] fw c1 c2 c3 (u i) (u a) (List.replicate tok true) (u a) acc ctr [] sU) (ob, ob) rfl rfl
  simp only [OTOps.F] at l5
  rw [upd_x, upd_t, BB_acc, upd_acc] at l5
  have l6 := OTOps.inc_run idxB
    (BB [] fw c1 c2 c3 (u i) (u a) [] [] (decide (a = tok) :: acc) ctr [] sU) ob
  rw [BB_idx, upd_idx] at l6
  obtain ⟨u1, hu1, q1⟩ := BitMachineRawSequence.runs (G1 F) P2 f0 () fc v1 ob (some false)
    _ _ _ _ _ l1 l2
  obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs (g1 F fc) P3 (leftLabel f0) ()
    (fc, ob) (fc, some false) ob ob _ _ _ _ _ q1 l3
  obtain ⟨u3, hu3, q3⟩ := BitMachineRawSequence.runs (g2 F fc) P4
    (leftLabel (leftLabel f0)) BitMachineCopy.Label.scan ((fc, ob), ob) ((fc, ob), ob) ob ob
    _ _ _ _ _ q2 l4
  obtain ⟨u4, hu4, q4⟩ := BitMachineRawSequence.runs (g3 F fc) P5
    (leftLabel (leftLabel (leftLabel f0))) OTOps.CL.cmp (((fc, ob), ob), ob) (((fc, ob), ob), ob)
    ((ob, ob) : OTOps.CCtl) v5 _ _ _ _ _ q3 l5
  obtain ⟨u5, hu5, q5⟩ := BitMachineRawSequence.runs (g4 F fc) P6
    (leftLabel (leftLabel (leftLabel (leftLabel f0)))) ()
    ((((fc, ob), ob), ob), ((ob, ob) : OTOps.CCtl)) ((((fc, ob), ob), ob), v5) ob ob
    _ _ _ _ _ q4 l6
  refine ⟨u5, ?_, _, q5⟩
  have hl : (u a).length = a := by simp [u]
  simp only [bodyGBound]
  rw [hl] at hu3
  omega

def loopGBd (s : ℕ) (Tf tok : ℕ → ℕ) (rest : ℕ → List Bool) (a : ℕ) : ℕ :=
  (Finset.range s).sup (fun i => bodyGBound (Tf i) (tok i) (rest i).length a)

def fullGBound (s : ℕ) (Tf tok : ℕ → ℕ) (rest : ℕ → List Bool) : ℕ :=
  ((((Tf 0 + (tok 0 + 1) + 1) + ((rest 0).length + 1) + 1) + (2 * s + 2) + 1) +
    (s * (loopGBd s Tf tok rest (tok 0) + 2) + 1) + 1) + (s + 1) + 1

/-- The generic outer-token equality run: from the fetch hypotheses for the
outer words `0, …, s-1`, ONE program extracts the token of word 0 into `aC`
and leaves the conjunction of the `s` token comparisons in `eqC`. -/
theorem fullG_run (s : ℕ) (fw c1 c2 c3 : List Bool) (Tf tok : ℕ → ℕ) (rest : ℕ → List Bool)
    (hF : ∀ i < s, FetchRun F f0 fc fw c1 c2 c3 i (tok i) (rest i) (Tf i)) (hs : 0 < s) :
    ∃ t ≤ fullGBound s Tf tok rest, ∃ v,
      ((advance (fullG F f0 fc))^[t])
        (⟨some (fullGStart F f0 fc), fullGCtl fc,
          BB [] fw c1 c2 c3 [] [] [] [] [] [] [] (u s)⟩ :
          TM2.Cfg (fun _ : B => Bool) _ _) =
        ⟨none, v, BB [] fw c1 c2 c3 (u s) (u (tok 0)) [] [] [] []
          [(accL (tok 0) tok s).all id] (u s)⟩ := by
  let a0 := tok 0
  obtain ⟨t1, ht1, v1, hh1⟩ := hF 0 hs
  have l1 := lift fI F (BB [] fw c1 c2 c3 [] [] [] [] [] [] [] (u s)) _ _ (fun _ => rfl)
    _ _ _ _ hh1
  have e1 : bank fI (BB [] fw c1 c2 c3 [] [] [] [] [] [] [] (u s))
      (FetchIndexed.FB [] [] [] (List.replicate a0 true ++ false :: rest 0) fw c1 c2 c3
        (List.replicate 0 true)) =
      BB (List.replicate a0 true ++ false :: rest 0) fw c1 c2 c3 [] [] [] [] [] [] [] (u s) :=
    bank_fI _ _ _
  rw [e1] at l1
  have hne2 : lblB ≠ aC := by simp [lblB, aC]
  have l2 := RawRowSplit.readU_run lblB aC hne2 a0 (rest 0) []
    (BB (List.replicate a0 true ++ false :: rest 0) fw c1 c2 c3 [] [] [] [] [] [] [] (u s))
    none rfl rfl
  rw [upd_lbl, upd_a, List.append_nil] at l2
  have l3 := OTOps.clr_run lblB (rest 0)
    (BB (rest 0) fw c1 c2 c3 [] (List.replicate a0 true) [] [] [] [] [] (u s)) ob rfl
  rw [upd_lbl] at l3
  have l4 := MatrixStage4ScalarPreparationOps.copy_run cp2Slots
    (BB [] fw c1 c2 c3 [] (List.replicate a0 true) [] [] [] [] [] (u s)) rfl
  have hc0 : cp2Slots 0 = sC := rfl
  have hc1 : cp2Slots 1 = ctrC := rfl
  rw [hc0, hc1, BB_s, BB_ctr, List.append_nil, upd_ctr] at l4
  let S : ℕ → B → List Bool := fun i =>
    BB [] fw c1 c2 c3 (u i) (u a0) [] [] (accL a0 tok i) (u (s - i)) [] (u s)
  have hS0 : S 0 = BB [] fw c1 c2 c3 [] (List.replicate a0 true) [] [] [] (u s) [] (u s) := by
    simp only [S, Nat.sub_zero]; rfl
  have hloop := CountedLoop.loop_run ctrC (bodyG F fc) (bodyGStart F f0 fc) (bodyGCtl fc) s
    (loopGBd s Tf tok rest a0) S
    (fun i _ => rfl)
    (by
      intro i hi
      obtain ⟨t, ht, v, hr⟩ := bodyG_run F f0 fc fw c1 c2 c3 i (tok i) (rest i) (Tf i) (hF i hi)
        (accL a0 tok i) (List.replicate (s - i - 1) true) (u s) a0
      refine ⟨t, le_trans ht (Finset.le_sup (f := fun i => bodyGBound (Tf i) (tok i)
        (rest i).length a0) (Finset.mem_range.mpr hi)), v, ?_⟩
      have hU : Function.update (S i) ctrC (List.replicate (s - i - 1) true) =
          BB [] fw c1 c2 c3 (u i) (u a0) [] [] (accL a0 tok i)
            (List.replicate (s - i - 1) true) [] (u s) := upd_ctr _ _ _ _ _ _ _ _ _ _ _ _ _ _
      rw [hU]
      refine hr.trans ?_
      have hsub : s - (i + 1) = s - i - 1 := by omega
      simp only [S, hsub]
      rfl)
    ((ob, bodyGCtl fc))
  rw [hS0] at hloop
  obtain ⟨t5, ht5, c5, l5⟩ := hloop
  have hSs : S s = BB [] fw c1 c2 c3 (u s) (u a0) [] [] (accL a0 tok s) [] [] (u s) := by
    simp only [S, Nat.sub_self]; rfl
  rw [hSs] at l5
  have hae : accC ≠ eqC := by simp [accC, eqC]
  have l6 := OTOps.fold_run accC eqC hae (accL a0 tok s)
    (BB [] fw c1 c2 c3 (u s) (u a0) [] [] (accL a0 tok s) [] [] (u s)) true ob rfl
  rw [upd_acc, BB_eq, upd_eq, accL_length, Bool.true_and] at l6
  obtain ⟨u1, hu1, q1⟩ := BitMachineRawSequence.runs (G1 F) Q2 f0 () fc v1 ob (some false)
    _ _ _ _ _ l1 l2
  obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs (h1 F fc) P3 (leftLabel f0) ()
    (fc, ob) (fc, some false) ob ob _ _ _ _ _ q1 l3
  obtain ⟨u3, hu3, q3⟩ := BitMachineRawSequence.runs (h2 F fc) Q4
    (leftLabel (leftLabel f0)) BitMachineCopy.Label.scan ((fc, ob), ob) ((fc, ob), ob) ob ob
    _ _ _ _ _ q2 l4
  obtain ⟨u4, hu4, q4⟩ := BitMachineRawSequence.runs (h3 F fc) (loopG F f0 fc)
    (leftLabel (leftLabel (leftLabel f0))) (.inl ()) (((fc, ob), ob), ob) (((fc, ob), ob), ob)
    (ob, bodyGCtl fc) c5 _ _ _ _ _ q3 l5
  obtain ⟨u5, hu5, q5⟩ := BitMachineRawSequence.runs (h4 F f0 fc) (OTOps.fold accC eqC)
    (leftLabel (leftLabel (leftLabel (leftLabel f0)))) ()
    ((((fc, ob), ob), ob), (ob, bodyGCtl fc)) ((((fc, ob), ob), ob), c5)
    ((true, ob) : OTOps.FCtl) _ _ _ _ _ _ q4 l6
  refine ⟨u5, ?_, _, q5⟩
  have hl : (u s).length = s := by simp [u]
  simp only [fullGBound]
  rw [hl] at hu3
  have ht5' : t5 ≤ s * (loopGBd s Tf tok rest (tok 0) + 2) + 1 := ht5
  omega

#print axioms bodyG_run
#print axioms fullG_run

end

end Paper2.OTGen
