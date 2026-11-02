import Paper2.ThrJoin
import Paper2.SuccessHeader
import Paper2.SuccessIdent
import Paper2.SuccessOrient
import Paper2.HeaderA
import Paper2.CopyAll

/-!
# Unit 3 endpoint, segment 2: the none outcome of the capped generator as ONE program

Lane `owner:a-h-a3-assembly-2` (private, 26 September 2026). Paper A, lock v12.

ONE fixed program `progN` on the joint bank `JN = OS ⊕ (TK ⊕ HB)`:
* `OS = SuccessOrient.Stack`, which holds the admitted success/fallback start bank
  `SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word`;
* `TK = ThrProducer.TK`, the admitted threshold producer bank;
* `HB = HeaderA.HB`, the admitted header bank.

Stages, each handoff charged by production `BitMachineRawSequence`:
1. `CopyAll` makes six source-preserving copies of the raw public counts p, s, q₂, w, Q, k
   (`SamplerParameterJoin.nrSrc` 5, 0, 2, 3, 4, 6) into the producer start bank `T0 k ![p,s,q₂,w,Q]`;
2. `ThrProducer.thrProg` (admitted, lifted) produces unary `k * Xv v + (clog p + 1)`;
3. `SuccessOrient.program` (admitted, lifted) runs the admitted no-preload producer/fallback program
   (`CodeFallbackFullJoin`), and on the none outcome halts with the zero table printed in the
   fallback writer (`CodeFallbackAllOutcomes.Outcome … none`);
4. `CopyAll` copies unary `mX` (writer rows), unary `mY` (writer cols), the threshold and the writer
   output word into the header cells `fuel 0/1/2` and `outH`;
5. `HeaderA.prog` (admitted, lifted).

Identity (`run_none`, `none_selected`): on `hc` and a physical `none` run on the selected tape, the
consumer word is `encodeInstance ⟨mX, mY, sourceBudget, rowMajor (fun _ _ => false)⟩`.
-/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.A3Assembly.NoneOut

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open BitMachineRawSequence (leftLabel)
open Paper2.ThrProducer (TK thrC ctrC scrC srcI T0 thrProg thrStart thrCtl Xv thrBd)
open GeneratorCode GeneratorSerialization GeneratorSource GeneratorFullSample
open RecursiveSamplingProgram RecursiveSamplingLaws RecursiveLabelCodecScratch
open RecursiveEntries RecursiveSampling
open SourceProfileParameters SourceRecursiveNoSampling TotalFiniteConstructorScratch

/-! ### The identity on the none outcome -/

section Generic

variable {n p s q₁ q₂ w Q : ℕ} [NeZero n] [NeZero s] [NeZero q₁] [NeZero q₂] [NeZero w]
  [NeZero Q]

/-- The semantic capped sampler on a tape where the physical run returns `none` completes to the
all-false table (same route as `SuccessIdent.run_success`, none case). -/
theorem run_none (hp : 0 < p) (hs : 4 ≤ s)
    (activity : SourceConstruction.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q)
    (k mX mY : ℕ)
    (tp : RecursiveSamplingMaterialization.TapeList (Fin n) s q₁ q₂ w Q p k mX mY)
    (hres : GeneratorCode.run (SuccessOrient.Bv n p s q₁ q₂ w Q)
      (SuccessOrient.Rv p s q₁ q₂ w Q k mX mY) (le_refl _)
      (SuccessOrient.Nv p s q₁ q₂ w Q k mX mY)
      (GeneratorStateSize.initialBounded (SuccessOrient.root n p s q₁ q₂ w Q k mX mY)
        (SamplerFallbackJoin.alphabet_bound n p s q₁ q₂ w Q k mX mY
          (NeZero.pos n) hp hs (NeZero.pos q₁) (NeZero.pos q₂) (NeZero.pos w)
          (NeZero.pos Q))) (SuccessIdent.physTape n p s q₁ q₂ w Q k mX mY tp) = none) :
    RecursiveSamplingExecution.run (finCongr (Fintype.card_fin n)) hs p hp activity ξ k mX mY
        (RecursiveSamplingTape.readTape _ _ _ tp) = fun _ _ => false := by
  rw [← codedCompleted_eq_sourceRun hp hs activity ξ k mX mY]
  let P := samples (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
    (finCongr (Fintype.card_fin n)) hs
    (RecursiveSamplingSeed.seedRow p) (RecursiveSamplingSeed.seedColumn p hp) k mX mY
  let M := RecursiveSamplingExecution.alphabetCap s q₁ q₂ w Q (Fintype.card (Fin n)) p
  have hM : P.maxAlphabet ≤ M := by
    simpa only [P, M, Fintype.card_fin] using
      seed_samples_alphabetBound (n := n) (p := p) (s := s)
        (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) hp hs activity ξ k mX mY
  have hsem : GeneratorCode.run (Nat.clog 2 M)
      (rejectionAttemptCap (RecursiveSamplingExecution.drawCap s q₁ q₂ w Q p k mX mY)) le_rfl
      (RecursiveSamplingExecution.drawCap s q₁ q₂ w Q p k mX mY)
      (encodedState (seedSampleCode n p s q₁ q₂ w Q k mX mY)
        (sampleCodec n s q₁ q₂ w Q k mX mY (piCodec boolCodec p) (finCodec p)) P
        (seedSampleCode_exact hp hs k mX mY) hM)
      (RecursiveSamplingTape.readTape _ _ _ tp) = none := by
    refine Eq.trans ?_ hres
    exact SuccessIdent.run_transport M (SamplerParameterJoin.M n p s q₁ q₂ w Q) _ _
      (by simp only [M, SamplerParameterJoin.M, Fintype.card_fin]) _ _ rfl tp.val tp.property
      (SuccessIdent.tape_length n p s q₁ q₂ w Q k mX mY tp)
  unfold codedCompleted
  simp only []
  rw [hsem]
  rfl

end Generic

/-- **None-outcome identity** at the canonical schedule: the consumer word is the encoded
instance with rows `sourceRows`, cols `sourceCols`, threshold `sourceBudget` and the all-false
table. -/
theorem none_selected {n m : ℕ} [NeZero n] (hn : 0 < n) (edge : Fin m → Bool → Fin n)
    (Δ : ℕ) (γ : ℚ) (k : ℕ)
    [NeZero (width (Nat.clog 2 n))] [NeZero (width (Nat.clog 2 n) - 2)]
    [NeZero (outerWidth (Nat.clog 2 n))]
    [NeZero (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 n))]
    [NeZero (ParameterizedCanonicalSource.coverWidth n m (Nat.clog 2 n) Δ γ)]
    (hc : CompletePublicScheduleScratch.Checks (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ)
    (tp : (select hn edge Δ γ k).Tape) :
    let L := Nat.clog 2 n
    let p := LookupSeed.width L
    let s := width L
    let q₁ := width L - 2
    let q₂ := outerWidth L
    let w := ParameterizedCanonicalSource.restorationWidth L
    let Q := ParameterizedCanonicalSource.coverWidth n m L Δ γ
    let mX := sourceRows L (ParameterizedCanonicalSource.restorationDepth L)
      (ParameterizedCanonicalSource.coverDepth n m L Δ γ) k
    let mY := sourceCols L (ParameterizedCanonicalSource.restorationDepth L)
      (ParameterizedCanonicalSource.coverDepth n m L Δ γ) k
    let thr := sourceBudget L (ParameterizedCanonicalSource.restorationDepth L)
      (ParameterizedCanonicalSource.coverDepth n m L Δ γ) k
    GeneratorCode.run (SuccessOrient.Bv n p s q₁ q₂ w Q)
        (SuccessOrient.Rv p s q₁ q₂ w Q k mX mY) (le_refl _)
        (SuccessOrient.Nv p s q₁ q₂ w Q k mX mY)
        (GeneratorStateSize.initialBounded (SuccessOrient.root n p s q₁ q₂ w Q k mX mY)
          (SamplerFallbackJoin.alphabet_bound n p s q₁ q₂ w Q k mX mY
            (NeZero.pos n) (by show 0 < LookupSeed.width L; unfold LookupSeed.width; positivity)
            (SourceProfiles.width_ge_four L) (NeZero.pos q₁) (NeZero.pos q₂) (NeZero.pos w)
            (NeZero.pos Q)))
        (SuccessIdent.physTape n p s q₁ q₂ w Q k mX mY (SuccessIdent.selTape hn edge Δ γ k hc tp))
        = none →
      EncodedSelectedOutput.selectedInstance hn edge Δ γ k tp =
          ⟨mX, mY, thr, MatrixMaterialization.rowMajor (fun (_ : Fin mX) (_ : Fin mY) => false)⟩ ∧
        EncodedSelectedOutput.outputBits hn edge Δ γ k tp =
          EncodedCommunication.encodeInstance
            ⟨mX, mY, thr, MatrixMaterialization.rowMajor (fun (_ : Fin mX) (_ : Fin mY) => false)⟩ := by
  intro L p s q₁ q₂ w Q mX mY thr hres
  have hp : 0 < p := by show 0 < LookupSeed.width L; unfold LookupSeed.width; positivity
  let activity := SourceActiveRank.scanAtCanonical edge
    (by have := SourceProfiles.width_ge_four L; omega)
    (SourceRepetitionScratch.outerWidth_eq_sourceQ0_mul_rep L (Fin m) hc.1)
  let ξ := CanonicalDefaultSource.canonicalDefaultTails L n w Q hn (NeZero.pos w) (NeZero.pos Q)
  have h := run_none (n := n) (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
    hp (SourceProfiles.width_ge_four L) activity ξ k mX mY
    (SuccessIdent.selTape hn edge Δ γ k hc tp) hres
  have hsel : EncodedSelectedOutput.selectedInstance hn edge Δ γ k tp =
      ⟨mX, mY, thr, MatrixMaterialization.rowMajor (fun (_ : Fin mX) (_ : Fin mY) => false)⟩ := by
    rw [SuccessIdent.selected_eq_scheduled hn edge Δ γ k hc tp]
    show EncodedSelectedOutput.instanceOf (YaoMaterialization.tabulate
      (RecursiveSamplingExecution.run (finCongr (Fintype.card_fin n))
        (SourceProfiles.width_ge_four L) p hp activity ξ k mX mY
        (RecursiveSamplingTape.readTape _ _ _ (SuccessIdent.selTape hn edge Δ γ k hc tp)))) thr = _
    rw [h]
    rfl
  refine ⟨hsel, ?_⟩
  unfold EncodedSelectedOutput.outputBits
  rw [hsel]

/-! ### The joint bank -/

abbrev OS := SuccessOrient.Stack
abbrev HB := HeaderA.HB
abbrev JN := OS ⊕ (TK ⊕ HB)

instance instDecOS : DecidableEq OS := inferInstance
instance instDecTK : DecidableEq TK := inferInstance
instance instDecHB : DecidableEq HB := inferInstance
instance instDecJN : DecidableEq JN := instDecidableEqSum

def ιO : OS ↪ JN := ⟨Sum.inl, Sum.inl_injective⟩
def ιT : TK ↪ JN := ⟨fun j => .inr (.inl j), by intro a b h; simpa using h⟩
def ιH : HB ↪ JN := ⟨fun j => .inr (.inr j), by intro a b h; simpa using h⟩

theorem bank_O (X Z : OS → List Bool) (Y : TK ⊕ HB → List Bool) :
    bank ιO (Sum.elim X Y) Z = Sum.elim Z Y := by
  funext c
  rcases c with c | c
  · exact bank_at ιO _ Z c
  · exact bank_outside ιO _ Z (.inr c) (by rintro ⟨k, hk⟩; cases hk)

theorem bank_T (X : OS → List Bool) (Y Z : TK → List Bool) (H : HB → List Bool) :
    bank ιT (Sum.elim X (Sum.elim Y H)) Z = Sum.elim X (Sum.elim Z H) := by
  funext c
  rcases c with c | c | c
  · exact bank_outside ιT _ Z (.inl c) (by rintro ⟨k, hk⟩; cases hk)
  · exact bank_at ιT _ Z c
  · exact bank_outside ιT _ Z (.inr (.inr c)) (by rintro ⟨k, hk⟩; cases hk)

theorem bank_H (X : OS → List Bool) (Y : TK → List Bool) (H Z : HB → List Bool) :
    bank ιH (Sum.elim X (Sum.elim Y H)) Z = Sum.elim X (Sum.elim Y Z) := by
  funext c
  rcases c with c | c | c
  · exact bank_outside ιH _ Z (.inl c) (by rintro ⟨k, hk⟩; cases hk)
  · exact bank_outside ιH _ Z (.inr (.inl c)) (by rintro ⟨k, hk⟩; cases hk)
  · exact bank_at ιH _ Z c

/-! ### Cells and copies -/

def oSrc (j : Fin 9) : JN := .inl (.inl (.inl (SamplerParameterJoin.nrSrc j)))
def tC (x : TK) : JN := .inr (.inl x)
def hC (x : HB) : JN := .inr (.inr x)
/-- Fallback writer cells inside `OS` (through the admitted `fallbackSlots`). -/
def wCell (e : MatrixTableWriter.Extra) : JN :=
  .inl (.inl (.inl (CodeFallbackEntryBank.fallbackSlots (.inr (.inr e)))))

def cpT (i : Fin 6) : Fin 3 ↪ JN :=
  ⟨![oSrc (ThrJoin.sT i), tC (ThrJoin.dT i), tC scrC], by
    intro a b h
    fin_cases i <;> fin_cases a <;> fin_cases b <;>
      simp_all [oSrc, tC, ThrJoin.dT, ThrJoin.sT, srcI, ctrC, scrC]⟩

def srcD : Fin 4 → JN := ![wCell .rows, wCell .cols, tC thrC, wCell .output]
def dstD : Fin 4 → JN := ![hC (HeaderA.fuel 0), hC (HeaderA.fuel 1), hC (HeaderA.fuel 2),
  hC HeaderA.outH]
def cpD (i : Fin 4) : Fin 3 ↪ JN :=
  ⟨![srcD i, dstD i, tC scrC], by
    intro a b h
    fin_cases i <;> fin_cases a <;> fin_cases b <;>
      simp_all [srcD, dstD, wCell, tC, hC, HeaderA.fuel, HeaderA.outH, thrC, scrC]⟩

/-! ### Banks -/

def vv (p s q₂ w Q : ℕ) : Fin 5 → ℕ := ![p, s, q₂, w, Q]
def valT (p s q₂ w Q k : ℕ) : Fin 6 → ℕ := ![p, s, q₂, w, Q, k]
def thrV (p s q₂ w Q k : ℕ) : ℕ := k * Xv (vv p s q₂ w Q) + (Nat.clog 2 p + 1)

def entryN (n p s q₁ q₂ w Q k mX mY : ℕ) (word : List Bool) : JN → List Bool :=
  Sum.elim (SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word)
    (Sum.elim (fun _ => []) (fun _ => []))

def zeroTable (mX mY : ℕ) : List Bool :=
  MatrixMaterialization.rowMajor (fun (_ : Fin mX) (_ : Fin mY) => false)

/-! ### Program -/

def tProg := fun l => stackStmt ιT (thrProg l)
def oProg := fun l => stackStmt ιO (SuccessOrient.program l)
def hProg := fun l => stackStmt ιH (HeaderA.prog l)

def q1 := BitMachineRawSequence.program (CopyAll.prog cpT) tProg thrStart (none : Option Bool)
  thrCtl
def q2 := BitMachineRawSequence.program q1 oProg SuccessOrient.startLabel
  ((none : Option Bool), thrCtl) SuccessOrient.startControl
def q3 := BitMachineRawSequence.program q2 (CopyAll.prog cpD) (.inl ⟨0, by omega⟩)
  (((none : Option Bool), thrCtl), SuccessOrient.startControl) (none : Option Bool)
/-- ONE fixed program for the none outcome (with its own generator run). -/
def progN := BitMachineRawSequence.program q3 hProg HeaderA.progStart
  ((((none : Option Bool), thrCtl), SuccessOrient.startControl), (none : Option Bool))
  HeaderA.progCtl

def ctlN := ((((((none : Option Bool), thrCtl), SuccessOrient.startControl),
  (none : Option Bool)), HeaderA.progCtl))

/-! ### Clock -/

def LN (p s q₂ w Q k mX mY : ℕ) : ℕ := mX + mY + thrV p s q₂ w Q k + (zeroTable mX mY).length

def headerClockN (p s q₂ w Q k mX mY : ℕ) : ℕ :=
  UnaryBinaryEncoding.coefficient * (mX + 1) ^ 2 +
    UnaryBinaryEncoding.coefficient * (mY + 1) ^ 2 +
    UnaryBinaryEncoding.coefficient * (thrV p s q₂ w Q k + 1) ^ 2 +
    (2 * (EncodedCommunication.natField mX ++ EncodedCommunication.natField mY ++
      EncodedCommunication.natField (thrV p s q₂ w Q k)).length + 2) + 3

def clockN (n p s q₁ q₂ w Q k mX mY : ℕ) : ℕ :=
  (6 * (2 * (p + s + q₂ + w + Q + k) + 3) + 1) + thrBd k (vv p s q₂ w Q) +
    (SamplerFallbackJoin.clock n p s q₁ q₂ w Q k mX mY + 1) +
    (4 * (2 * LN p s q₂ w Q k mX mY + 3) + 1) + headerClockN p s q₂ w Q k mX mY + 4

/-! ### Stage 1: the six count copies -/

theorem stage1 (n p s q₁ q₂ w Q k mX mY : ℕ) (word : List Bool) :
    ∃ t ≤ 6 * (2 * (p + s + q₂ + w + Q + k) + 3) + 1, ∃ v',
      ((advance (CopyAll.prog cpT))^[t])
          (⟨some (.inl ⟨0, by omega⟩), (none : Option Bool),
            entryN n p s q₁ q₂ w Q k mX mY word⟩ :
            TM2.Cfg (fun _ : JN => Bool) (CopyAll.Lab 6) (Option Bool)) =
        ⟨none, v', Sum.elim (SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word)
          (Sum.elim (T0 k (vv p s q₂ w Q)) (fun _ => []))⟩ := by
  let T := entryN n p s q₁ q₂ w Q k mX mY word
  have hval : ∀ i : Fin 6, T (cpT i 0) = List.replicate (valT p s q₂ w Q k i) true := by
    intro i
    refine (SamplerParameterJoin.nrSrc_value n p s q₁ q₂ w Q k mX mY word (ThrJoin.sT i)).trans ?_
    fin_cases i <;> rfl
  have hsd : ∀ i j, cpT i 0 ≠ cpT j 1 := by
    intro i j h
    change oSrc (ThrJoin.sT i) = tC (ThrJoin.dT j) at h
    simp [oSrc, tC] at h
  have hzd : ∀ i j, cpT i 2 ≠ cpT j 1 := by
    intro i j h
    change tC scrC = tC (ThrJoin.dT j) at h
    simp only [tC, Sum.inr.injEq, Sum.inl.injEq] at h
    fin_cases j <;> simp [ThrJoin.dT, srcI, ctrC, scrC] at h
  have hdd : ∀ i j, cpT i 1 = cpT j 1 → i = j := by
    intro i j h
    change tC (ThrJoin.dT i) = tC (ThrJoin.dT j) at h
    simp only [tC, Sum.inr.injEq, Sum.inl.injEq] at h
    exact ThrJoin.dT_inj i j h
  obtain ⟨tA, htA, vA, rA⟩ := CopyAll.all_run cpT hsd hzd hdd T (fun i => rfl)
    (p + s + q₂ + w + Q + k)
    (by
      intro i
      rw [hval, List.length_replicate]
      fin_cases i <;> simp [valT] <;> omega) none
  have hA : CopyAll.done cpT 6 T =
      Sum.elim (SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word)
        (Sum.elim (T0 k (vv p s q₂ w Q)) (fun _ => [])) := by
    funext z
    by_cases hz' : ∃ j, cpT j 1 = z
    · obtain ⟨j, rfl⟩ := hz'
      rw [CopyAll.done_dst cpT hdd T j, hval j]
      change _ ++ [] = T0 k (vv p s q₂ w Q) (ThrJoin.dT j)
      rw [List.append_nil]
      fin_cases j <;> rfl
    · rw [CopyAll.done_off cpT T z (fun j h => hz' ⟨j, h⟩)]
      rcases z with z | y | y
      · rfl
      · change [] = T0 k (vv p s q₂ w Q) y
        rcases y with a | ⟨i, x⟩
        · fin_cases a
          · rfl
          · rfl
          · exact absurd ⟨5, rfl⟩ hz'
          · rfl
        · by_cases hx : x = .inl 0
          · subst hx
            fin_cases i
            · exact absurd ⟨0, rfl⟩ hz'
            · exact absurd ⟨1, rfl⟩ hz'
            · exact absurd ⟨2, rfl⟩ hz'
            · exact absurd ⟨3, rfl⟩ hz'
            · exact absurd ⟨4, rfl⟩ hz'
          · show [] = (if x = .inl 0 then _ else [])
            rw [if_neg hx]
      · rfl
  rw [hA] at rA
  exact ⟨tA, htA, vA, rA⟩

/-! ### Stage 2: the threshold producer -/

theorem stage2 (n p s q₁ q₂ w Q k mX mY : ℕ) (word : List Bool) :
    ∃ t ≤ thrBd k (vv p s q₂ w Q), ∃ vc, ∃ F : TK → List Bool,
      ((advance tProg)^[t]) (⟨some thrStart, thrCtl,
          Sum.elim (SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word)
            (Sum.elim (T0 k (vv p s q₂ w Q)) (fun _ => []))⟩ :
          TM2.Cfg (fun _ : JN => Bool) _ _) =
        ⟨none, vc, Sum.elim (SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word)
          (Sum.elim F (fun _ => []))⟩ ∧
      F thrC = List.replicate (thrV p s q₂ w Q k) true ∧ F scrC = [] := by
  obtain ⟨tB, htB, vc, F, rB, hFt, -, -, hFz, -, -⟩ := ThrProducer.thr_run k (vv p s q₂ w Q)
  have rB' := BitMachineStackRun.run ιT
    (Sum.elim (SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word)
      (Sum.elim (T0 k (vv p s q₂ w Q)) (fun _ => []))) thrProg
    (⟨some thrStart, thrCtl, T0 k (vv p s q₂ w Q)⟩ : TM2.Cfg (fun _ : TK => Bool) _ _) tB
  rw [rB] at rB'
  simp only [stackCfg] at rB'
  rw [bank_T, bank_T] at rB'
  refine ⟨tB, htB, vc, F, rB', ?_, hFz⟩
  rw [hFt]
  rfl

/-! ### Stage 3: the admitted producer/fallback run, none outcome -/

theorem stage3 (n p s q₁ q₂ w Q k mX mY : ℕ)
    (hn : 0 < n) (hp : 0 < p) (hs : 4 ≤ s) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hw : 0 < w) (hQ : 0 < Q)
    (tape : CappedSampler.Adaptive.Tape (SuccessOrient.Bv n p s q₁ q₂ w Q)
      (SuccessOrient.Rv p s q₁ q₂ w Q k mX mY) (SuccessOrient.Nv p s q₁ q₂ w Q k mX mY))
    (hres : GeneratorCode.run (SuccessOrient.Bv n p s q₁ q₂ w Q) (SuccessOrient.Rv p s q₁ q₂ w Q k mX mY)
      (le_refl _) (SuccessOrient.Nv p s q₁ q₂ w Q k mX mY)
      (GeneratorStateSize.initialBounded (SuccessOrient.root n p s q₁ q₂ w Q k mX mY)
        (SamplerFallbackJoin.alphabet_bound n p s q₁ q₂ w Q k mX mY
          hn hp hs hq₁ hq₂ hw hQ)) tape = none)
    (F : TK → List Bool) :
    let word := (RecursiveSamplingTape.writeTape (SuccessOrient.Bv n p s q₁ q₂ w Q)
      (SuccessOrient.Rv p s q₁ q₂ w Q k mX mY) (SuccessOrient.Nv p s q₁ q₂ w Q k mX mY) tape).val
    ∃ t ≤ SamplerFallbackJoin.clock n p s q₁ q₂ w Q k mX mY + 1,
      ∃ (d : CodeTableFallback.Config) (G : SamplerParameterBank.Private → List Bool),
        CodeFallbackAllOutcomes.Outcome mX mY none d ∧
        ((advance oProg)^[t]) (⟨some SuccessOrient.startLabel, SuccessOrient.startControl,
            Sum.elim (SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word)
              (Sum.elim F (fun _ => []))⟩ : TM2.Cfg (fun _ : JN => Bool) _ _) =
          ⟨none, ((SamplerParameterJoin.startControl,
              (CodeFallbackFullJoin.prepControl, d.var)), none),
            Sum.elim (SuccessOrient.fallbackBank n p s q₁ q₂ w Q k mX mY word
              (SuccessOrient.Bv n p s q₁ q₂ w Q) (SuccessOrient.Rv p s q₁ q₂ w Q k mX mY) d G)
              (Sum.elim F (fun _ => []))⟩ := by
  intro word
  obtain ⟨t, d, G, ht, -, -, hout, hresult⟩ :=
    SuccessOrient.run n p s q₁ q₂ w Q k mX mY hn hp hs hq₁ hq₂ hw hQ tape
  rw [hres] at ht hout hresult
  refine ⟨t, by simpa [SuccessOrient.outputTime] using ht, d, G, hout, ?_⟩
  simp only [SuccessOrient.Result] at hresult
  have h := BitMachineStackRun.run ιO
    (Sum.elim (SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word) (Sum.elim F (fun _ => [])))
    SuccessOrient.program
    (⟨some SuccessOrient.startLabel, SuccessOrient.startControl,
      SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word⟩ :
      TM2.Cfg (fun _ : OS => Bool) _ _) t
  rw [hresult] at h
  simp only [stackCfg] at h
  rw [bank_O, bank_O] at h
  exact h

/-! ### Stage 4: copies into the header -/

theorem fallback_writer (n p s q₁ q₂ w Q k mX mY : ℕ) (word : List Bool) (B R : ℕ)
    (d : CodeTableFallback.Config) (G : SamplerParameterBank.Private → List Bool)
    (e : MatrixTableWriter.Extra) :
    SuccessOrient.fallbackBank n p s q₁ q₂ w Q k mX mY word B R d G
      (.inl (.inl (CodeFallbackEntryBank.fallbackSlots (.inr (.inr e))))) =
      d.stk (.inr (.inr e)) := by
  show bank CodeFallbackEntryBank.fallbackSlots _ d.stk
    (CodeFallbackEntryBank.fallbackSlots (.inr (.inr e))) = _
  exact bank_at _ _ _ _

theorem stage4 (n p s q₁ q₂ w Q k mX mY : ℕ) (word : List Bool) (B R : ℕ)
    (a : CodeFullPadding.Config) (wc : CodeTableFallback.WriterControl)
    (G : SamplerParameterBank.Private → List Bool) (F : TK → List Bool)
    (hFt : F thrC = List.replicate (thrV p s q₂ w Q k) true) (hFz : F scrC = []) :
    let d : CodeTableFallback.Config := ⟨none, CodeTableFallback.embedWriter wc,
        Sum.elim (Function.update a.stk CodeHeaderDraw.output [])
          (MatrixTableWriter.ready CodeTableFallback.emptyBank mX mY
            0 0 0 0 [] (zeroTable mX mY)).contents⟩
    ∃ t ≤ 4 * (2 * LN p s q₂ w Q k mX mY + 3) + 1, ∃ v',
      ((advance (CopyAll.prog cpD))^[t])
          (⟨some (.inl ⟨0, by omega⟩), (none : Option Bool),
            Sum.elim (SuccessOrient.fallbackBank n p s q₁ q₂ w Q k mX mY word B R d G)
              (Sum.elim F (fun _ => []))⟩ :
            TM2.Cfg (fun _ : JN => Bool) (CopyAll.Lab 4) (Option Bool)) =
        ⟨none, v', Sum.elim (SuccessOrient.fallbackBank n p s q₁ q₂ w Q k mX mY word B R d G)
          (Sum.elim F (HeaderA.Hin mX mY (thrV p s q₂ w Q k) (zeroTable mX mY) []))⟩ := by
  intro d
  let T : JN → List Bool :=
    Sum.elim (SuccessOrient.fallbackBank n p s q₁ q₂ w Q k mX mY word B R d G)
      (Sum.elim F (fun _ => []))
  have hrows : T (wCell .rows) = List.replicate mX true :=
    fallback_writer n p s q₁ q₂ w Q k mX mY word B R d G .rows
  have hcols : T (wCell .cols) = List.replicate mY true :=
    fallback_writer n p s q₁ q₂ w Q k mX mY word B R d G .cols
  have hout : T (wCell .output) = zeroTable mX mY :=
    fallback_writer n p s q₁ q₂ w Q k mX mY word B R d G .output
  have hthr : T (tC thrC) = List.replicate (thrV p s q₂ w Q k) true := hFt
  have hsd : ∀ i j, cpD i 0 ≠ cpD j 1 := by
    intro i j h
    change srcD i = dstD j at h
    fin_cases i <;> fin_cases j <;> simp [srcD, dstD, wCell, tC, hC] at h
  have hzd : ∀ i j, cpD i 2 ≠ cpD j 1 := by
    intro i j h
    change tC scrC = dstD j at h
    fin_cases j <;> simp [dstD, tC, hC] at h
  have hdd : ∀ i j, cpD i 1 = cpD j 1 → i = j := by
    intro i j h
    change dstD i = dstD j at h
    fin_cases i <;> fin_cases j <;> simp_all [dstD, hC, HeaderA.fuel, HeaderA.outH]
  obtain ⟨tA, htA, vA, rA⟩ := CopyAll.all_run cpD hsd hzd hdd T (fun i => hFz)
    (LN p s q₂ w Q k mX mY)
    (by
      intro i
      fin_cases i
      · change (T (wCell .rows)).length ≤ _
        rw [hrows, List.length_replicate]; unfold LN; omega
      · change (T (wCell .cols)).length ≤ _
        rw [hcols, List.length_replicate]; unfold LN; omega
      · change (T (tC thrC)).length ≤ _
        rw [hthr, List.length_replicate]; unfold LN; omega
      · change (T (wCell .output)).length ≤ _
        rw [hout]; unfold LN; omega) none
  have hA : CopyAll.done cpD 4 T =
      Sum.elim (SuccessOrient.fallbackBank n p s q₁ q₂ w Q k mX mY word B R d G)
        (Sum.elim F (HeaderA.Hin mX mY (thrV p s q₂ w Q k) (zeroTable mX mY) [])) := by
    funext z
    by_cases hz' : ∃ j, cpD j 1 = z
    · obtain ⟨j, rfl⟩ := hz'
      rw [CopyAll.done_dst cpD hdd T j]
      fin_cases j
      · change T (wCell .rows) ++ [] = _
        rw [hrows, List.append_nil]; rfl
      · change T (wCell .cols) ++ [] = _
        rw [hcols, List.append_nil]; rfl
      · change T (tC thrC) ++ [] = _
        rw [hthr, List.append_nil]; rfl
      · change T (wCell .output) ++ [] = _
        rw [hout]; rfl
    · rw [CopyAll.done_off cpD T z (fun j h => hz' ⟨j, h⟩)]
      rcases z with z | y | y
      · rfl
      · rfl
      · change [] = HeaderA.Hin mX mY (thrV p s q₂ w Q k) (zeroTable mX mY) [] y
        rcases y with x | j
        · rfl
        · fin_cases j
          · exact absurd ⟨0, rfl⟩ hz'
          · exact absurd ⟨1, rfl⟩ hz'
          · exact absurd ⟨2, rfl⟩ hz'
          · rfl
          · rfl
          · exact absurd ⟨3, rfl⟩ hz'
  rw [hA] at rA
  exact ⟨tA, htA, vA, rA⟩

/-! ### Stage 5: the header -/

theorem stage5 (X : OS → List Bool) (F : TK → List Bool) (mX mY thr : ℕ) (table : List Bool) :
    ∃ t ≤ UnaryBinaryEncoding.coefficient * (mX + 1) ^ 2 +
        UnaryBinaryEncoding.coefficient * (mY + 1) ^ 2 +
        UnaryBinaryEncoding.coefficient * (thr + 1) ^ 2 +
        (2 * (EncodedCommunication.natField mX ++ EncodedCommunication.natField mY ++
          EncodedCommunication.natField thr).length + 2) + 3,
      ∃ v, ∃ H : HB → List Bool,
        ((advance hProg)^[t]) (⟨some HeaderA.progStart, HeaderA.progCtl,
            Sum.elim X (Sum.elim F (HeaderA.Hin mX mY thr table []))⟩ :
            TM2.Cfg (fun _ : JN => Bool) _ _) = ⟨none, v, Sum.elim X (Sum.elim F H)⟩ ∧
        H HeaderA.outH = EncodedCommunication.encodeInstance ⟨mX, mY, thr, table⟩ := by
  obtain ⟨t, ht, v, H, hr, hH⟩ := HeaderA.header_instance ⟨mX, mY, thr, table⟩ []
  refine ⟨t, ht, v, H, ?_, by rw [hH, List.append_nil]⟩
  have h := BitMachineStackRun.run ιH (Sum.elim X (Sum.elim F (HeaderA.Hin mX mY thr table [])))
    HeaderA.prog ⟨some HeaderA.progStart, HeaderA.progCtl, HeaderA.Hin mX mY thr table []⟩ t
  rw [hr] at h
  simp only [stackCfg] at h
  rw [bank_H, bank_H] at h
  exact h

/-! ### Segment 2 main theorem (generic parameters) -/

/-- **Segment 2 (generic).** For every physical capped tape on which the admitted generator run
returns `none`, the ONE fixed program `progN`, started on the admitted start bank (raw public
counts and the literal tape word) with everything else blank, halts within `clockN` in the exact
exit bank: the admitted fallback exit bank (`Outcome … none`), the producer region `F` (threshold
and scratch cells stated) and the header region `H`, whose output cell holds
`encodeInstance ⟨mX, mY, thrV, rowMajor (all false)⟩`. -/
theorem none_run (n p s q₁ q₂ w Q k mX mY : ℕ)
    (hn : 0 < n) (hp : 0 < p) (hs : 4 ≤ s) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hw : 0 < w) (hQ : 0 < Q)
    (tape : CappedSampler.Adaptive.Tape (SuccessOrient.Bv n p s q₁ q₂ w Q)
      (SuccessOrient.Rv p s q₁ q₂ w Q k mX mY) (SuccessOrient.Nv p s q₁ q₂ w Q k mX mY))
    (hres : GeneratorCode.run (SuccessOrient.Bv n p s q₁ q₂ w Q) (SuccessOrient.Rv p s q₁ q₂ w Q k mX mY)
      (le_refl _) (SuccessOrient.Nv p s q₁ q₂ w Q k mX mY)
      (GeneratorStateSize.initialBounded (SuccessOrient.root n p s q₁ q₂ w Q k mX mY)
        (SamplerFallbackJoin.alphabet_bound n p s q₁ q₂ w Q k mX mY
          hn hp hs hq₁ hq₂ hw hQ)) tape = none) :
    let word := (RecursiveSamplingTape.writeTape (SuccessOrient.Bv n p s q₁ q₂ w Q)
      (SuccessOrient.Rv p s q₁ q₂ w Q k mX mY) (SuccessOrient.Nv p s q₁ q₂ w Q k mX mY) tape).val
    ∃ T ≤ clockN n p s q₁ q₂ w Q k mX mY, ∃ ctl,
      ∃ (d : CodeTableFallback.Config) (G : SamplerParameterBank.Private → List Bool)
        (F : TK → List Bool) (H : HB → List Bool),
        CodeFallbackAllOutcomes.Outcome mX mY none d ∧
        ((advance progN)^[T]) (⟨some (leftLabel (leftLabel (leftLabel (leftLabel
            (.inl ⟨0, by omega⟩))))), ctlN, entryN n p s q₁ q₂ w Q k mX mY word⟩ :
            TM2.Cfg (fun _ : JN => Bool) _ _) =
          ⟨none, ctl, Sum.elim (SuccessOrient.fallbackBank n p s q₁ q₂ w Q k mX mY word
              (SuccessOrient.Bv n p s q₁ q₂ w Q) (SuccessOrient.Rv p s q₁ q₂ w Q k mX mY) d G)
            (Sum.elim F H)⟩ ∧
        F thrC = List.replicate (thrV p s q₂ w Q k) true ∧ F scrC = [] ∧
        H HeaderA.outH = EncodedCommunication.encodeInstance
          ⟨mX, mY, thrV p s q₂ w Q k, zeroTable mX mY⟩ := by
  intro word
  obtain ⟨t1, ht1, v1, r1⟩ := stage1 n p s q₁ q₂ w Q k mX mY word
  obtain ⟨t2, ht2, vc, F, r2, hFt, hFz⟩ := stage2 n p s q₁ q₂ w Q k mX mY word
  obtain ⟨t3, ht3, d, G, hout, r3⟩ :=
    stage3 n p s q₁ q₂ w Q k mX mY hn hp hs hq₁ hq₂ hw hQ tape hres F
  have hout' := hout
  simp only [CodeFallbackAllOutcomes.Outcome] at hout'
  obtain ⟨a, wc, hd⟩ := hout'
  subst hd
  obtain ⟨t4, ht4, v4, r4⟩ := stage4 n p s q₁ q₂ w Q k mX mY word
    (SuccessOrient.Bv n p s q₁ q₂ w Q) (SuccessOrient.Rv p s q₁ q₂ w Q k mX mY) a wc G F hFt hFz
  obtain ⟨t5, ht5, v5, H, r5, hH⟩ := stage5
    (SuccessOrient.fallbackBank n p s q₁ q₂ w Q k mX mY word
      (SuccessOrient.Bv n p s q₁ q₂ w Q) (SuccessOrient.Rv p s q₁ q₂ w Q k mX mY) _ G)
    F mX mY (thrV p s q₂ w Q k) (zeroTable mX mY)
  obtain ⟨u1, hu1, s1⟩ := BitMachineRawSequence.runs (CopyAll.prog cpT) tProg _ _ _ _ _ _ _ _ _
    t1 t2 r1 r2
  obtain ⟨u2, hu2, s2⟩ := BitMachineRawSequence.runs q1 oProg _ _ _ _ _ _ _ _ _
    u1 t3 s1 r3
  obtain ⟨u3, hu3, s3⟩ := BitMachineRawSequence.runs q2 (CopyAll.prog cpD) _ _ _ _ _ _ _ _ _
    u2 t4 s2 r4
  obtain ⟨u4, hu4, s4⟩ := BitMachineRawSequence.runs q3 hProg _ _ _ _ _ _ _ _ _
    u3 t5 s3 r5
  refine ⟨u4, ?_, _, _, G, F, H, hout, s4, hFt, hFz, hH⟩
  unfold clockN headerClockN
  omega

end

#print axioms run_none
#print axioms none_selected
#print axioms stage1
#print axioms stage2
#print axioms stage3
#print axioms stage4
#print axioms stage5
#print axioms none_run

end Paper2.A3Assembly.NoneOut
