import Paper2.OTBody

/-! Unit 3, segment (1), outer-token equality, fixed-tail tag: ONE fixed
program `full` on the bank `OTBody.B`, from the fixed-tail tuple word
`(piCodec oc s).encode js ++ O`, the outer code, and unary `s` (cell `sC`):

1. prelude: `FetchIndexed.colProgram` fetches outer word 0; `readU` moves its
   token `(js 0).1` to cell `aC` (the extracted unary `a`); `clr` clears the
   rest; `copyProgram` copies unary `s` to the loop counter `ctrC`;
2. `CountedLoop.loop` on `ctrC` runs `OTBody.body` `s` times (outer index
   `0, …, s-1`), pushing `decide ((js 0).1 = (js p).1)` for every `p`;
3. `OTOps.fold` pops the accumulated bits and pushes their conjunction on
   `eqC`.

Exit bank (exact): unary index `s`, `aC = unary (js 0).1`, `eqC = [eq]` with
`eq = decide (∀ p, (js p).1 = (js 0).1)`, every other lane cell blank, the
retained word/code cells and `sC` unchanged. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.OTLoop

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource RecursiveRequestCodeShape
open RecursiveLabelCodecScratch RecursiveEntries SourceMatrix
open BitMachineRawSequence (leftLabel)
open Paper2.OTOps (u)
open Paper2.OTBody

/-! ### Programs -/

def cp2Fun : Fin 3 → B := ![sC, ctrC, zC]

theorem cp2Fun_injective : Function.Injective cp2Fun := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [cp2Fun, sC, ctrC, zC]

def cp2Slots : Fin 3 ↪ B := ⟨cp2Fun, cp2Fun_injective⟩

def Q2 := RawRowSplit.readU lblB aC
def Q4 := MatrixStage4ScalarPreparationOps.copyProgram cp2Slots
def loopP := CountedLoop.loop ctrC body bodyStart bodyCtl

def e1 := BitMachineRawSequence.program P1 Q2 () FetchIndexed.colControl ob
def e2 := BitMachineRawSequence.program e1 P3 () (FetchIndexed.colControl, ob) ob
def e3 := BitMachineRawSequence.program e2 Q4 BitMachineCopy.Label.scan
  ((FetchIndexed.colControl, ob), ob) ob
def e4 := BitMachineRawSequence.program e3 loopP (.inl ())
  (((FetchIndexed.colControl, ob), ob), ob) (ob, bodyCtl)
/-- The outer-token equality machine (fixed-tail tag): one fixed program. -/
def full := BitMachineRawSequence.program e4 (OTOps.fold accC eqC) ()
  ((((FetchIndexed.colControl, ob), ob), ob), (ob, bodyCtl)) ((true, ob) : OTOps.FCtl)

def fullStart := FetchIndexed.labelOf full
  (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel FetchIndexed.colStart)))))
def fullCtl := (((((FetchIndexed.colControl, ob), ob), ob), (ob, bodyCtl)),
  ((true, ob) : OTOps.FCtl))

/-! ### The accumulated bits -/

def accL (a : ℕ) (tok : ℕ → ℕ) : ℕ → List Bool
  | 0 => []
  | i + 1 => decide (a = tok i) :: accL a tok i

theorem accL_length (a : ℕ) (tok : ℕ → ℕ) : ∀ i, (accL a tok i).length = i
  | 0 => rfl
  | i + 1 => by simp [accL, accL_length a tok i]

theorem accL_all (a : ℕ) (tok : ℕ → ℕ) : ∀ i,
    (accL a tok i).all id = true ↔ ∀ j < i, a = tok j
  | 0 => by simp [accL]
  | i + 1 => by
      rw [show accL a tok (i + 1) = decide (a = tok i) :: accL a tok i from rfl,
        List.all_cons, Bool.and_eq_true, accL_all a tok i]
      constructor
      · rintro ⟨h1, h2⟩ j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
        · exact h2 j h
        · subst h; simpa using h1
      · intro h
        exact ⟨by simpa using h i (by omega), fun j hj => h j (by omega)⟩

variable {n p s q₁ q₂ w Q : ℕ}
  [NeZero n] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

/-- The token of outer word `i` (as a function of `ℕ`, `0` off range). -/
def tokF (k : ℕ)
    (js : Fin s → OuterColumn q₁ q₂ s
      (Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k))
    (i : ℕ) : ℕ :=
  if h : i < s then (js ⟨i, h⟩).1.val else 0

theorem eq_iff (k : ℕ)
    (js : Fin s → OuterColumn q₁ q₂ s
      (Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k)) :
    (accL (js 0).1.val (tokF k js) s).all id = decide (∀ pp, (js pp).1 = (js 0).1) := by
  rw [Bool.eq_iff_iff, accL_all, decide_eq_true_iff]
  constructor
  · intro h pp
    have := h pp.val pp.isLt
    simp only [tokF, dif_pos pp.isLt] at this
    exact Fin.ext this.symm
  · intro h j hj
    simp only [tokF, dif_pos hj]
    exact (congrArg Fin.val (h ⟨j, hj⟩)).symm

/-- The uniform per-iteration clock: the maximum of the exact body clocks. -/
def loopBd (k : ℕ)
    (js : Fin s → OuterColumn q₁ q₂ s
      (Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k))
    (O : List Bool) (a : ℕ) : ℕ :=
  Finset.univ.sup (fun pp : Fin s => bodyBound k js O a pp)

/-- The exact composite clock. -/
def fullBound (k : ℕ)
    (js : Fin s → OuterColumn q₁ q₂ s
      (Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k))
    (O : List Bool) : ℕ :=
  let C := defaultCarrierCodecs n p s q₁ q₂ w Q k
  let oc := outerColumnCodec q₁ q₂ s C.2
  let rc := outerCode q₁ q₂ s (seedRecursiveCodes n p s q₁ q₂ w Q k).2
  let cs := List.ofFn (fun a : Fin s => oc.encode (js a))
  ((((FetchIndexed.colBound rc cs 0 O + ((js 0).1.val + 1) + 1) +
    (((piCodec C.2 (q₁ + s + 1)).encode (js 0).2).length + 1) + 1) + (2 * s + 2) + 1) +
    (s * (loopBd k js O (js 0).1.val + 2) + 1) + 1) + (s + 1) + 1

/-- Segment (1), fixed-tail tag: the outer-token equality bit and the
extracted token `(js 0).1`, by ONE fixed program on ONE bank. -/
theorem fixed_eq_run (hp : 0 < p) (hs : 4 ≤ s) (k : ℕ)
    (js : Fin s → OuterColumn q₁ q₂ s
      (Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k))
    (O r1 r2 : List Bool) :
    let C := defaultCarrierCodecs n p s q₁ q₂ w Q k
    let oc := outerColumnCodec q₁ q₂ s C.2
    let rc := outerCode q₁ q₂ s (seedRecursiveCodes n p s q₁ q₂ w Q k).2
    let fw := (piCodec oc s).encode js ++ O
    ∃ t ≤ fullBound k js O, ∃ v,
      ((advance full)^[t])
        (⟨some fullStart, fullCtl,
          BB [] fw (encodeCode rc) r1 r2 [] [] [] [] [] [] [] (u s)⟩ :
          TM2.Cfg (fun _ : B => Bool) _ _) =
        ⟨none, v, BB [] fw (encodeCode rc) r1 r2 (u s) (u (js 0).1.val) [] [] [] []
          [decide (∀ pp, (js pp).1 = (js 0).1)] (u s)⟩ := by
  intro C oc rc fw
  let a0 := (js 0).1.val
  -- prelude 1: fetch outer word 0
  obtain ⟨t1, ht1, v1, h1⟩ := OuterTokenFetch.fixed_outer_fetch (n := n) (p := p) (s := s)
    (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) hp hs k js 0 O r1 r2
  have l1 := lift fI FetchIndexed.colProgram
    (BB [] fw (encodeCode rc) r1 r2 [] [] [] [] [] [] [] (u s)) _ _ (fun _ => rfl)
    _ _ _ _ h1
  have e1' : bank fI (BB [] fw (encodeCode rc) r1 r2 [] [] [] [] [] [] [] (u s))
      (FetchIndexed.FB [] [] [] (oc.encode (js 0)) fw (encodeCode rc) r1 r2
        (List.replicate (0 : Fin s).val true)) =
      BB (oc.encode (js 0)) fw (encodeCode rc) r1 r2 [] [] [] [] [] [] [] (u s) :=
    bank_fI _ _ _
  rw [e1'] at l1
  -- prelude 2: the token of word 0 into `aC`
  have htok := OuterTokenFetch.outer_word_token (n := n) (p := p) (s := s) (q₁ := q₁)
    (q₂ := q₂) (w := w) (Q := Q) k (js 0)
  let body0 := (piCodec C.2 (q₁ + s + 1)).encode (js 0).2
  have hne2 : lblB ≠ aC := by simp [lblB, aC]
  have l2 := RawRowSplit.readU_run lblB aC hne2 a0 body0 []
    (BB (oc.encode (js 0)) fw (encodeCode rc) r1 r2 [] [] [] [] [] [] [] (u s))
    none (by rw [BB_lbl]; exact htok) rfl
  rw [upd_lbl, upd_a, List.append_nil] at l2
  -- prelude 3: clear the rest of word 0
  have l3 := OTOps.clr_run lblB body0
    (BB body0 fw (encodeCode rc) r1 r2 [] (List.replicate a0 true) [] [] [] [] [] (u s)) ob rfl
  rw [upd_lbl] at l3
  -- prelude 4: the loop counter from unary `s`
  have l4 := MatrixStage4ScalarPreparationOps.copy_run cp2Slots
    (BB [] fw (encodeCode rc) r1 r2 [] (List.replicate a0 true) [] [] [] [] [] (u s)) rfl
  have hc0 : cp2Slots 0 = sC := rfl
  have hc1 : cp2Slots 1 = ctrC := rfl
  rw [hc0, hc1, BB_s, BB_ctr, List.append_nil, upd_ctr] at l4
  -- the loop
  let S : ℕ → B → List Bool := fun i =>
    BB [] fw (encodeCode rc) r1 r2 (u i) (u a0) [] [] (accL a0 (tokF k js) i) (u (s - i)) []
      (u s)
  have hS0 : S 0 = BB [] fw (encodeCode rc) r1 r2 [] (List.replicate a0 true) [] [] [] (u s) []
      (u s) := by
    simp only [S, Nat.sub_zero]; rfl
  have hloop := CountedLoop.loop_run ctrC body bodyStart bodyCtl s (loopBd k js O a0) S
    (fun i _ => rfl)
    (by
      intro i hi
      have hr := body_run (n := n) (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
        hp hs k js ⟨i, hi⟩ O r1 r2 (accL a0 (tokF k js) i) (List.replicate (s - i - 1) true)
        (u s) a0
      obtain ⟨t, ht, v, hr⟩ := hr
      refine ⟨t, le_trans ht (Finset.le_sup (f := fun pp : Fin s => bodyBound k js O a0 pp)
        (Finset.mem_univ (⟨i, hi⟩ : Fin s))), v, ?_⟩
      have hU : Function.update (S i) ctrC (List.replicate (s - i - 1) true) =
          BB [] fw (encodeCode rc) r1 r2 (u i) (u a0) [] [] (accL a0 (tokF k js) i)
            (List.replicate (s - i - 1) true) [] (u s) := upd_ctr _ _ _ _ _ _ _ _ _ _ _ _ _ _
      rw [hU]
      refine hr.trans ?_
      have hT : tokF k js i = (js ⟨i, hi⟩).1.val := by simp [tokF, hi]
      have hA : accL a0 (tokF k js) (i + 1) =
          decide (a0 = (js ⟨i, hi⟩).1.val) :: accL a0 (tokF k js) i := by
        rw [← hT]; rfl
      have hsub : s - (i + 1) = s - i - 1 := by omega
      simp only [S, hA, hsub]
      rfl)
    ((ob, bodyCtl))
  rw [hS0] at hloop
  obtain ⟨t5, ht5, c5, l5⟩ := hloop
  have hSs : S s = BB [] fw (encodeCode rc) r1 r2 (u s) (u a0) [] [] (accL a0 (tokF k js) s) []
      [] (u s) := by
    simp only [S, Nat.sub_self]; rfl
  rw [hSs] at l5
  -- the fold
  have hae : accC ≠ eqC := by simp [accC, eqC]
  have l6 := OTOps.fold_run accC eqC hae (accL a0 (tokF k js) s)
    (BB [] fw (encodeCode rc) r1 r2 (u s) (u a0) [] [] (accL a0 (tokF k js) s) [] [] (u s))
    true ob rfl
  rw [upd_acc, BB_eq, upd_eq, accL_length, Bool.true_and, eq_iff] at l6
  -- sequencing
  obtain ⟨u1, hu1, q1⟩ := BitMachineRawSequence.runs P1 Q2 FetchIndexed.colStart ()
    FetchIndexed.colControl v1 ob (some false) _ _ _ _ _ l1 l2
  obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs e1 P3 (leftLabel FetchIndexed.colStart) ()
    (FetchIndexed.colControl, ob) (FetchIndexed.colControl, some false) ob ob _ _ _ _ _ q1 l3
  obtain ⟨u3, hu3, q3⟩ := BitMachineRawSequence.runs e2 Q4
    (leftLabel (leftLabel FetchIndexed.colStart)) BitMachineCopy.Label.scan
    ((FetchIndexed.colControl, ob), ob) ((FetchIndexed.colControl, ob), ob) ob ob
    _ _ _ _ _ q2 l4
  obtain ⟨u4, hu4, q4⟩ := BitMachineRawSequence.runs e3 loopP
    (leftLabel (leftLabel (leftLabel FetchIndexed.colStart))) (.inl ())
    (((FetchIndexed.colControl, ob), ob), ob) (((FetchIndexed.colControl, ob), ob), ob)
    (ob, bodyCtl) c5 _ _ _ _ _ q3 l5
  obtain ⟨u5, hu5, q5⟩ := BitMachineRawSequence.runs e4 (OTOps.fold accC eqC)
    (leftLabel (leftLabel (leftLabel (leftLabel FetchIndexed.colStart)))) ()
    ((((FetchIndexed.colControl, ob), ob), ob), (ob, bodyCtl))
    ((((FetchIndexed.colControl, ob), ob), ob), c5) ((true, ob) : OTOps.FCtl) _ _ _ _ _ _ q4 l6
  refine ⟨u5, ?_, _, q5⟩
  have ht1' : t1 ≤ FetchIndexed.colBound (outerCode q₁ q₂ s (seedRecursiveCodes n p s q₁ q₂ w Q k).2)
      (List.ofFn fun a =>
        (outerColumnCodec q₁ q₂ s (defaultCarrierCodecs n p s q₁ q₂ w Q k).2).encode (js a))
      0 O := ht1
  have hb : body0.length =
      ((piCodec (defaultCarrierCodecs n p s q₁ q₂ w Q k).2 (q₁ + s + 1)).encode (js 0).2).length :=
    rfl
  have hl : (u s).length = s := by simp [u]
  simp only [fullBound]
  rw [hl] at hu3
  have ht5' : t5 ≤ s * (loopBd k js O (js 0).1.val + 2) + 1 := ht5
  omega

#print axioms cp2Fun_injective
#print axioms accL_all
#print axioms eq_iff
#print axioms fixed_eq_run

end

end Paper2.OTLoop
