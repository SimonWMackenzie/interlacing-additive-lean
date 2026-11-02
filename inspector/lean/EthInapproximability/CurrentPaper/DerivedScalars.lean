import EthInapproximability.CurrentPaper.CopyFill
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps

/-!
# Segment 5 (partial): the derived common words from present level words

Lane owner:b-stage4-entry-program-5 (Paper B, unit 2, map item 3).

ONE fixed six-phase program (five charged handoffs) on an arbitrary bank `K`
with nineteen distinct named cells `ι : Fin 19 ↪ K`. Inputs (restored):
`ι 0 = s`, `ι 1 = cy`, `ι 2 = binBase`, `ι 3 = s*L`, `ι 4 = nv`, `ι 5 = nb`,
`ι 6 = rx` (all unary; at the level-0 prep exit these are writers 28, 27, 29,
16, 18, 15, 17, see `EntryLevelWords.exit_writer_words` for 28/27/29/16/17).
Outputs (blank at the start): `ι 7 = s - 1`, `ι 8 = cy^(s+1)`,
`ι 9 = binBase^s`, `ι 10 = [true]`, `ι 11 = s*L + (nv+nb)*rx` (the raw row
count). Scratch `ι 12 … ι 18` blank at the start and at the exit.

1. owner-4 `CopyFill` copies: `s` into `ι 7`, `ι 12`, `ι 13`; `s*L` into `ι 11`;
2. one straight-line statement: pop `ι 7`; push `true` on `ι 12`, `ι 8`, `ι 9`, `ι 10`;
3. admitted `weighted_power_run`: `ι 8 := cy^(s+1)` (fuel `ι 12` consumed);
4. admitted `weighted_power_run`: `ι 9 := binBase^s` (fuel `ι 13` consumed);
5. admitted `multiply_run`: `ι 11 := nv*rx ++ ι 11`;
6. admitted `multiply_run`: `ι 11 := nb*rx ++ ι 11`.
-/

namespace EthInapproximability.CurrentPaper.DerivedScalars

open Turing BitMachineEncoding MatrixStage4ScalarPreparationOps

variable {K : Type*} [DecidableEq K] (ι : Fin 19 ↪ K)

def rep (n : ℕ) : List Bool := List.replicate n true

def jobs1 : List (K × List K) := [(ι 0, [ι 7, ι 12, ι 13]), (ι 3, [ι 11])]

def P1 := MultiMove.program ((jobs1 ι).map CopyFill.toJob) (ι 14)

def microStmt : TM2.Stmt (fun _ : K => Bool) Unit Unit :=
  TM2.Stmt.pop (ι 7) (fun v _ => v)
    (TM2.Stmt.push (ι 12) (fun _ => true)
      (TM2.Stmt.push (ι 8) (fun _ => true)
        (TM2.Stmt.push (ι 9) (fun _ => true)
          (TM2.Stmt.push (ι 10) (fun _ => true) TM2.Stmt.halt))))

def P2 : Unit → TM2.Stmt (fun _ : K => Bool) Unit Unit := fun _ => microStmt ι

def idxA : Fin 6 ⊕ Fin 1 → Fin 19 := Sum.elim ![8, 1, 15, 16, 17, 18] ![12]
def idxB : Fin 6 ⊕ Fin 1 → Fin 19 := Sum.elim ![9, 2, 15, 16, 17, 18] ![13]
def idxM1 : Fin 6 → Fin 19 := ![4, 6, 15, 16, 17, 11]
def idxM2 : Fin 6 → Fin 19 := ![5, 6, 15, 16, 17, 11]

theorem idxA_inj : Function.Injective idxA := by decide
theorem idxB_inj : Function.Injective idxB := by decide
theorem idxM1_inj : Function.Injective idxM1 := by decide
theorem idxM2_inj : Function.Injective idxM2 := by decide

def eA : MatrixWeightedPower.Stack ↪ K := ⟨fun k => ι (idxA k), ι.injective.comp idxA_inj⟩
def eB : MatrixWeightedPower.Stack ↪ K := ⟨fun k => ι (idxB k), ι.injective.comp idxB_inj⟩
def eM1 : Fin 6 ↪ K := ⟨fun k => ι (idxM1 k), ι.injective.comp idxM1_inj⟩
def eM2 : Fin 6 ↪ K := ⟨fun k => ι (idxM2 k), ι.injective.comp idxM2_inj⟩

def q5 := BitMachineRawSequence.program (multiplyProgram (eM1 ι)) (multiplyProgram (eM2 ι))
  MatrixAddressMachine.Label.outer false false
def q4 := BitMachineRawSequence.program (weightedPowerProgram (eB ι)) (q5 ι)
  (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer) (false, false) (false, false)
def q3 := BitMachineRawSequence.program (weightedPowerProgram (eA ι)) (q4 ι)
  (BitMachineRawSequence.leftLabel (Sum.inr MatrixWeightedPower.Admin.test)) (false, false)
  ((false, false), (false, false))
def q2 := BitMachineRawSequence.program (P2 ι) (q3 ι)
  (BitMachineRawSequence.leftLabel (Sum.inr MatrixWeightedPower.Admin.test)) ()
  ((false, false), ((false, false), (false, false)))
/-- ONE fixed program. -/
def program := BitMachineRawSequence.program (P1 ι) (q2 ι) (BitMachineRawSequence.leftLabel ())
  MultiMove.initial ((), ((false, false), ((false, false), (false, false))))

def initial : MultiMove.Control × (Unit × ((Bool × Bool) × ((Bool × Bool) × (Bool × Bool)))) :=
  (MultiMove.initial, ((), ((false, false), ((false, false), (false, false)))))

/-- The exact exit bank. -/
def outBank (S : K → List Bool) (s cy b sL nv nb rx : ℕ) : K → List Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update S
    (ι 7) (rep (s - 1))) (ι 8) (rep (cy ^ (s + 1)))) (ι 9) (rep (b ^ s))) (ι 10) [true])
    (ι 11) (rep (sL + (nv + nb) * rx))

def bound (s cy b sL nv nb rx : ℕ) : ℕ :=
  ((2 * s + 2) + (2 * sL + 2) + 0 + 1) + MatrixWeightedPower.powerBound cy (s + 1) +
    MatrixWeightedPower.powerBound b s + MatrixAddressMachine.exactTime nv rx 0 +
    MatrixAddressMachine.exactTime nb rx 0 + 6

theorem derived_scalars (S : K → List Bool) (s cy b sL nv nb rx : ℕ)
    (h0 : S (ι 0) = rep s) (h1 : S (ι 1) = rep cy) (h2 : S (ι 2) = rep b)
    (h3 : S (ι 3) = rep sL) (h4 : S (ι 4) = rep nv) (h5 : S (ι 5) = rep nb)
    (h6 : S (ι 6) = rep rx)
    (hb : ∀ k : Fin 19, 7 ≤ k.val → S (ι k) = []) :
    ∃ t ≤ bound s cy b sL nv nb rx,
      ((advance (program ι))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (MultiMove.startLabel ((jobs1 ι).map CopyFill.toJob))), initial, S⟩ :
          TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, initial, outBank ι S s cy b sL nv nb rx⟩ := by
  have ne : ∀ i j : Fin 19, i ≠ j → ι i ≠ ι j := fun i j h => ι.injective.ne h
  have b7 := hb 7 (by decide)
  have b8 := hb 8 (by decide)
  have b9 := hb 9 (by decide)
  have b10 := hb 10 (by decide)
  have b11 := hb 11 (by decide)
  have b12 := hb 12 (by decide)
  have b13 := hb 13 (by decide)
  have b14 := hb 14 (by decide)
  have b15 := hb 15 (by decide)
  have b16 := hb 16 (by decide)
  have b17 := hb 17 (by decide)
  have b18 := hb 18 (by decide)
  -- phase 1
  have good : CopyFill.Good (ι 14) (jobs1 ι) :=
    ⟨by simp [jobs1, EmbeddingLike.apply_eq_iff_eq],
     by simp [jobs1, EmbeddingLike.apply_eq_iff_eq],
     by simp [jobs1, EmbeddingLike.apply_eq_iff_eq],
     by simp [jobs1, EmbeddingLike.apply_eq_iff_eq]⟩
  have hblank1 : ∀ j ∈ jobs1 ι, ∀ d ∈ j.2, S d = [] := by
    simp only [jobs1, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    exact ⟨⟨b7, b12, b13⟩, b11⟩
  have r1 := CopyFill.run (ι 14) (jobs1 ι) good S b14 hblank1
  set B1 := CopyFill.fill (jobs1 ι) S with hB1
  have hc1 : CopyFill.fillCost (jobs1 ι) S = (2 * s + 2) + (2 * sL + 2) + 0 := by
    simp [CopyFill.fillCost, jobs1, h0, h3, rep]
  rw [hc1] at r1
  have e1 : ∀ k : Fin 19, B1 (ι k) =
      if k = 7 ∨ k = 12 ∨ k = 13 then rep s else if k = 11 then rep sL else S (ι k) := by
    intro k
    simp only [hB1, CopyFill.fill, jobs1, List.mem_cons,
      List.not_mem_nil, or_false, EmbeddingLike.apply_eq_iff_eq, h0, h3]
  -- phase 2: one step
  set B2 := Function.update (Function.update (Function.update (Function.update
    (Function.update B1 (ι 7) (B1 (ι 7)).tail) (ι 12) (true :: B1 (ι 12)))
      (ι 8) (true :: B1 (ι 8))) (ι 9) (true :: B1 (ι 9))) (ι 10) (true :: B1 (ι 10)) with hB2
  have r2 : ((advance (P2 ι))^[1]) (⟨some (), (), B1⟩ : TM2.Cfg (fun _ : K => Bool) Unit Unit) =
      ⟨none, (), B2⟩ := by
    simp only [Function.iterate_one, advance, TM2.step, P2, microStmt, TM2.stepAux,
      Option.getD_some]
    congr 1
    simp only [hB2]
    congr 1 <;> simp [EmbeddingLike.apply_eq_iff_eq]
  have ev := fun (k : Fin 19) => e1 k
  -- phase 3: cy^(s+1) into ι 8 (fuel ι 12)
  have a8 : B2 (ι 8) = [true] := by
    simp [hB2, EmbeddingLike.apply_eq_iff_eq, e1, b8]
  have a1 : B2 (ι 1) = rep cy := by
    simp [hB2, EmbeddingLike.apply_eq_iff_eq, e1, h1]
  have a15 : B2 (ι 15) = [] := by
    simp [hB2, EmbeddingLike.apply_eq_iff_eq, e1, b15]
  have a16 : B2 (ι 16) = [] := by
    simp [hB2, EmbeddingLike.apply_eq_iff_eq, e1, b16]
  have a17 : B2 (ι 17) = [] := by
    simp [hB2, EmbeddingLike.apply_eq_iff_eq, e1, b17]
  have a18 : B2 (ι 18) = [] := by
    simp [hB2, EmbeddingLike.apply_eq_iff_eq, e1, b18]
  have a12 : B2 (ι 12) = List.replicate (s + 1) true := by
    simp [hB2, EmbeddingLike.apply_eq_iff_eq, e1, rep,
      List.replicate_succ]
  obtain ⟨t3, ht3, r3⟩ := weighted_power_run (eA ι) B2 cy (s + 1) a8 a1 a15 a16 a17 a18 a12
  set B3 := Function.update (Function.update B2 (ι 8) (List.replicate (cy ^ (s + 1)) true))
    (ι 12) [] with hB3
  have r3' : ((advance (weightedPowerProgram (eA ι)))^[t3])
      (⟨some (.inr .test), (false, false), B2⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
      ⟨none, (false, false), B3⟩ := r3
  -- phase 4: binBase^s into ι 9 (fuel ι 13)
  have c9 : B3 (ι 9) = [true] := by
    simp [hB3, hB2, EmbeddingLike.apply_eq_iff_eq, e1, b9]
  have c2 : B3 (ι 2) = rep b := by
    simp [hB3, hB2, EmbeddingLike.apply_eq_iff_eq, e1, h2]
  have c15 : B3 (ι 15) = [] := by
    simp [hB3, hB2, EmbeddingLike.apply_eq_iff_eq, e1, b15]
  have c16 : B3 (ι 16) = [] := by
    simp [hB3, hB2, EmbeddingLike.apply_eq_iff_eq, e1, b16]
  have c17 : B3 (ι 17) = [] := by
    simp [hB3, hB2, EmbeddingLike.apply_eq_iff_eq, e1, b17]
  have c18 : B3 (ι 18) = [] := by
    simp [hB3, hB2, EmbeddingLike.apply_eq_iff_eq, e1, b18]
  have c13 : B3 (ι 13) = List.replicate s true := by
    simp [hB3, hB2, EmbeddingLike.apply_eq_iff_eq, e1, rep]
  obtain ⟨t4, ht4, r4⟩ := weighted_power_run (eB ι) B3 b s c9 c2 c15 c16 c17 c18 c13
  set B4 := Function.update (Function.update B3 (ι 9) (List.replicate (b ^ s) true))
    (ι 13) [] with hB4
  have r4' : ((advance (weightedPowerProgram (eB ι)))^[t4])
      (⟨some (.inr .test), (false, false), B3⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
      ⟨none, (false, false), B4⟩ := r4
  -- phase 5: nv * rx onto ι 11
  have d4 : B4 (ι 4) = List.replicate nv true := by
    simp [hB4, hB3, hB2, EmbeddingLike.apply_eq_iff_eq, e1, h4, rep]
  have d6 : B4 (ι 6) = List.replicate rx true := by
    simp [hB4, hB3, hB2, EmbeddingLike.apply_eq_iff_eq, e1, h6, rep]
  have d15 : B4 (ι 15) = [] := by
    simp [hB4, hB3, hB2, EmbeddingLike.apply_eq_iff_eq, e1, b15]
  have d16 : B4 (ι 16) = [] := by
    simp [hB4, hB3, hB2, EmbeddingLike.apply_eq_iff_eq, e1, b16]
  have d17 : B4 (ι 17) = [] := by
    simp [hB4, hB3, hB2, EmbeddingLike.apply_eq_iff_eq, e1, b17]
  have r5 := multiply_run (eM1 ι) B4 nv rx d4 d6 d15 d16 d17
  set B5 := Function.update B4 (ι 11) (List.replicate (nv * rx) true ++ B4 (ι 11)) with hB5
  have r5' : ((advance (multiplyProgram (eM1 ι)))^[MatrixAddressMachine.exactTime nv rx 0])
      (⟨some .outer, false, B4⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
      ⟨none, false, B5⟩ := r5
  -- phase 6: nb * rx onto ι 11
  have f5 : B5 (ι 5) = List.replicate nb true := by
    simp [hB5, hB4, hB3, hB2, EmbeddingLike.apply_eq_iff_eq, e1, h5, rep]
  have f6 : B5 (ι 6) = List.replicate rx true := by
    simp [hB5, hB4, hB3, hB2, EmbeddingLike.apply_eq_iff_eq, e1, h6, rep]
  have f15 : B5 (ι 15) = [] := by
    simp [hB5, hB4, hB3, hB2, EmbeddingLike.apply_eq_iff_eq, e1, b15]
  have f16 : B5 (ι 16) = [] := by
    simp [hB5, hB4, hB3, hB2, EmbeddingLike.apply_eq_iff_eq, e1, b16]
  have f17 : B5 (ι 17) = [] := by
    simp [hB5, hB4, hB3, hB2, EmbeddingLike.apply_eq_iff_eq, e1, b17]
  have r6 := multiply_run (eM2 ι) B5 nb rx f5 f6 f15 f16 f17
  set B6 := Function.update B5 (ι 11) (List.replicate (nb * rx) true ++ B5 (ι 11)) with hB6
  have r6' : ((advance (multiplyProgram (eM2 ι)))^[MatrixAddressMachine.exactTime nb rx 0])
      (⟨some .outer, false, B5⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
      ⟨none, false, B6⟩ := r6
  -- the exit bank
  have hfin : B6 = outBank ι S s cy b sL nv nb rx := by
    funext k
    by_cases hk : ∃ i, ι i = k
    · obtain ⟨i, rfl⟩ := hk
      fin_cases i <;>
        simp [hB6, hB5, hB4, hB3, hB2, outBank,
          EmbeddingLike.apply_eq_iff_eq, e1, h0, h1, h2, h3, h4, h5, h6, b8, b9, b10,
          b12, b13, b14, b15, b16, b17, b18, rep, List.tail_replicate]
      all_goals ring_nf
    · have hk' : ∀ i, k ≠ ι i := fun i h => hk ⟨i, h.symm⟩
      have hf : B1 k = S k := by
        rw [hB1]
        apply CopyFill.fill_off
        simp [jobs1, hk']
      simp [hB6, hB5, hB4, hB3, hB2, outBank, hk', hf]
  -- composition
  obtain ⟨u5, hu5, s5⟩ := BitMachineRawSequence.runs (multiplyProgram (eM1 ι))
    (multiplyProgram (eM2 ι)) _ _ _ _ _ _ _ _ _ _ _ r5' r6'
  obtain ⟨u4, hu4, s4⟩ := BitMachineRawSequence.runs (weightedPowerProgram (eB ι)) (q5 ι)
    _ _ _ _ _ _ _ _ _ _ _ r4' s5
  obtain ⟨u3, hu3, s3⟩ := BitMachineRawSequence.runs (weightedPowerProgram (eA ι)) (q4 ι)
    _ _ _ _ _ _ _ _ _ _ _ r3' s4
  obtain ⟨u2, hu2, s2⟩ := BitMachineRawSequence.runs (P2 ι) (q3 ι)
    _ _ _ _ _ _ _ _ _ _ _ r2 s3
  obtain ⟨u1, hu1, s1⟩ := BitMachineRawSequence.runs (P1 ι) (q2 ι)
    _ _ _ _ _ _ _ _ _ _ _ r1 s2
  refine ⟨u1, ?_, ?_⟩
  · unfold bound
    omega
  · rw [← hfin]
    exact s1

#print axioms derived_scalars

end EthInapproximability.CurrentPaper.DerivedScalars
