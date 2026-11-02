import Paper2.SuccessFetchJoin
import Paper2.EncodedSelectedOutput

/-! Unit 3, segment (6), semantic core (production imports only; no private module).

On the scheduled branch of `TotalFiniteConstructorScratch.select` (public checks pass), a
selected tape `tp` is a fair-bit list of the scheduled length. `physTape` is the physical
capped tape carrying EXACTLY the same bits (the literal word written on the machine tape is
`tp.val`, `physTape_word`); only the vertex-count term `Fintype.card (Fin n)` is rewritten
to `n` in its type. If the physical generator run of the admitted success chain
(`SuccessFetchJoin.success_fetch`'s hypothesis `hres`) returns `some bytes` on that tape and
`bytes` is the columns-first codec word of label tuples `(ys, xs)` (the equation that
`success_fetch` / `SuccessCodec.success_codec` provide), then:

* `run_success`: the semantic capped sampler on the same tape returns exactly the table
  `fun i j => RecursiveEntries.matrix (LookupSeed.matrix p) activity ξ k (xs i) (ys j)`
  (via the production `GeneratorFullSample.codedCompleted_eq_sourceRun`);
* `success_selected`: `EncodedSelectedOutput.selectedInstance hn edge Δ γ k tp` is the
  instance with rows `sourceRows`, cols `sourceCols`, threshold `sourceBudget` and table
  `MatrixMaterialization.rowMajor f` for that `f` at the canonical schedule;
* `success_outputBits`: hence `outputBits … tp = natField mX ++ natField mY ++ natField thr
  ++ rowMajor f`.

No colouring, success event, or table value is supplied: the only hypotheses are the public
checks, the physical run result and the byte equation. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.SuccessIdent

noncomputable section

open EthInapproximability.CurrentPaper
open GeneratorCode GeneratorSerialization GeneratorSource GeneratorFullSample
open RecursiveSamplingProgram RecursiveSamplingLaws RecursiveLabelCodecScratch
open RecursiveEntries RecursiveSampling
open SourceProfileParameters SourceRecursiveNoSampling TotalFiniteConstructorScratch

/-- Paper B's row-major list is Paper A's serialized `tabulate` list (same function). -/
theorem rowMajor_eq_tabulate {r c : ℕ} (F : Fin r → Fin c → Bool) :
    MatrixMaterialization.rowMajor F = (YaoMaterialization.tabulate F).bits := rfl

/-- Changing only the alphabet-cap term (propositionally equal) does not change the run. -/
theorem run_transport (M₁ M₂ R N : ℕ) (h : M₁ = M₂)
    (st₁ : GeneratorCode.BoundedState M₁) (st₂ : GeneratorCode.BoundedState M₂)
    (hst : st₁.val = st₂.val) (bits : List Bool)
    (h₁ : bits.length = RecursiveSamplingTape.bitCount (Nat.clog 2 M₁) R N)
    (h₂ : bits.length = RecursiveSamplingTape.bitCount (Nat.clog 2 M₂) R N) :
    GeneratorCode.run (Nat.clog 2 M₁) R le_rfl N st₁
        (RecursiveSamplingTape.readTape _ R N ⟨bits, h₁⟩) =
      GeneratorCode.run (Nat.clog 2 M₂) R le_rfl N st₂
        (RecursiveSamplingTape.readTape _ R N ⟨bits, h₂⟩) := by
  subst h
  obtain rfl : st₁ = st₂ := Subtype.ext hst
  rfl

theorem tape_length (n p s q₁ q₂ w Q k mX mY : ℕ)
    (tp : RecursiveSamplingMaterialization.TapeList (Fin n) s q₁ q₂ w Q p k mX mY) :
    tp.val.length = RecursiveSamplingTape.bitCount (SuccessOrient.Bv n p s q₁ q₂ w Q)
      (SuccessOrient.Rv p s q₁ q₂ w Q k mX mY) (SuccessOrient.Nv p s q₁ q₂ w Q k mX mY) := by
  rw [tp.property, Fintype.card_fin]
  rfl

/-- The physical capped tape of the admitted success chain carrying the bits of `tp`. -/
def physTape (n p s q₁ q₂ w Q k mX mY : ℕ)
    (tp : RecursiveSamplingMaterialization.TapeList (Fin n) s q₁ q₂ w Q p k mX mY) :
    CappedSampler.Adaptive.Tape (SuccessOrient.Bv n p s q₁ q₂ w Q)
      (SuccessOrient.Rv p s q₁ q₂ w Q k mX mY) (SuccessOrient.Nv p s q₁ q₂ w Q k mX mY) :=
  RecursiveSamplingTape.readTape _ _ _ ⟨tp.val, tape_length n p s q₁ q₂ w Q k mX mY tp⟩

/-- The word the physical machine starts on is literally the selected tape list. -/
theorem physTape_word (n p s q₁ q₂ w Q k mX mY : ℕ)
    (tp : RecursiveSamplingMaterialization.TapeList (Fin n) s q₁ q₂ w Q p k mX mY) :
    (RecursiveSamplingTape.writeTape (SuccessOrient.Bv n p s q₁ q₂ w Q)
      (SuccessOrient.Rv p s q₁ q₂ w Q k mX mY) (SuccessOrient.Nv p s q₁ q₂ w Q k mX mY)
      (physTape n p s q₁ q₂ w Q k mX mY tp)).val = tp.val := by
  simp only [physTape, RecursiveSamplingTape.writeTape_readTape]

section Generic

variable {n p s q₁ q₂ w Q : ℕ} [NeZero n] [NeZero s] [NeZero q₁] [NeZero q₂] [NeZero w]
  [NeZero Q]

theorem decode_success (hp : 0 < p) (hs : 4 ≤ s) (k mX mY : ℕ) (bytes : List Bool)
    (ys : Fin mY → Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n))
      s q₁ q₂ w Q k)
    (xs : Fin mX → Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n))
      s q₁ q₂ w Q k)
    (hbytes : bytes =
      (List.ofFn (fun j => (defaultCarrierCodecs n p s q₁ q₂ w Q k).2.encode (ys j))).flatten ++
        (List.ofFn (fun i => (defaultCarrierCodecs n p s q₁ q₂ w Q k).1.encode (xs i))).flatten) :
    (sampleCodec n s q₁ q₂ w Q k mX mY (piCodec boolCodec p) (finCodec p)).decode bytes =
      some ((ys, xs), []) := by
  have henc : bytes =
      (sampleCodec n s q₁ q₂ w Q k mX mY (piCodec boolCodec p) (finCodec p)).encode
        (ys, xs) ++ [] := by
    rw [List.append_nil, hbytes]
    change _ = (piCodec _ mY).encode ys ++ (piCodec _ mX).encode xs
    rw [CodeSampleOutputDecoder.piCodec_encode_tupleWord,
      CodeSampleOutputDecoder.piCodec_encode_tupleWord,
      SuccessCodec.tupleWord_eq_flatten, SuccessCodec.tupleWord_eq_flatten]
    rfl
  rw [henc, PrefixCodec.roundtrip]

/-- The semantic capped sampler on a tape where the physical success chain succeeds with the
codec word of `(ys, xs)` returns exactly the recursive matrix restricted to `(xs, ys)`. -/
theorem run_success (hp : 0 < p) (hs : 4 ≤ s)
    (activity : SourceConstruction.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q)
    (k mX mY : ℕ)
    (tp : RecursiveSamplingMaterialization.TapeList (Fin n) s q₁ q₂ w Q p k mX mY)
    (bytes : List Bool)
    (hres : GeneratorCode.run (SuccessOrient.Bv n p s q₁ q₂ w Q)
      (SuccessOrient.Rv p s q₁ q₂ w Q k mX mY) (le_refl _)
      (SuccessOrient.Nv p s q₁ q₂ w Q k mX mY)
      (GeneratorStateSize.initialBounded (SuccessOrient.root n p s q₁ q₂ w Q k mX mY)
        (SamplerFallbackJoin.alphabet_bound n p s q₁ q₂ w Q k mX mY
          (NeZero.pos n) hp hs (NeZero.pos q₁) (NeZero.pos q₂) (NeZero.pos w)
          (NeZero.pos Q))) (physTape n p s q₁ q₂ w Q k mX mY tp) = some bytes)
    (ys : Fin mY → Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n))
      s q₁ q₂ w Q k)
    (xs : Fin mX → Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n))
      s q₁ q₂ w Q k)
    (hbytes : bytes =
      (List.ofFn (fun j => (defaultCarrierCodecs n p s q₁ q₂ w Q k).2.encode (ys j))).flatten ++
        (List.ofFn (fun i => (defaultCarrierCodecs n p s q₁ q₂ w Q k).1.encode (xs i))).flatten) :
    RecursiveSamplingExecution.run (finCongr (Fintype.card_fin n)) hs p hp activity ξ k mX mY
        (RecursiveSamplingTape.readTape _ _ _ tp) =
      fun i j => RecursiveEntries.matrix (LookupSeed.matrix p) activity ξ k (xs i) (ys j) := by
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
      (RecursiveSamplingTape.readTape _ _ _ tp) = some bytes := by
    refine Eq.trans ?_ hres
    exact run_transport M (SamplerParameterJoin.M n p s q₁ q₂ w Q) _ _
      (by simp only [M, SamplerParameterJoin.M, Fintype.card_fin]) _ _ rfl tp.val tp.property
      (tape_length n p s q₁ q₂ w Q k mX mY tp)
  have hdec := decode_success hp hs k mX mY bytes ys xs hbytes
  unfold codedCompleted
  simp only []
  rw [hsem]
  simp only [Option.bind_some, hdec, Option.map_some, CappedSampler.completed,
    Option.getD_some]
  funext i j
  exact evaluate_eq_matrix _ _ _ _ _ _

end Generic

/-- Transport of a selected tape along `select_good` (pure `Eq.rec`). -/
theorem instance_transport (o o' : SelectedOutput) (e : o = o') (t : o.Tape) :
    EncodedSelectedOutput.instanceOf (o.table t) o.budget =
      EncodedSelectedOutput.instanceOf (o'.table (cast (congrArg SelectedOutput.Tape e) t))
        o'.budget := by
  subst e
  rfl

/-- The scheduled tape list underlying a selected tape when the public checks pass. -/
def selTape {n m : ℕ} (hn : 0 < n) (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CompletePublicScheduleScratch.Checks (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ)
    (tp : (select hn edge Δ γ k).Tape) : (scheduledOutput hn edge Δ γ k hc).Tape :=
  cast (congrArg SelectedOutput.Tape (select_good hn edge Δ γ k hc)) tp

theorem selected_eq_scheduled {n m : ℕ} (hn : 0 < n) (edge : Fin m → Bool → Fin n) (Δ : ℕ)
    (γ : ℚ) (k : ℕ)
    (hc : CompletePublicScheduleScratch.Checks (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ)
    (tp : (select hn edge Δ γ k).Tape) :
    EncodedSelectedOutput.selectedInstance hn edge Δ γ k tp =
      EncodedSelectedOutput.instanceOf
        ((scheduledOutput hn edge Δ γ k hc).table (selTape hn edge Δ γ k hc tp))
        (scheduledOutput hn edge Δ γ k hc).budget :=
  instance_transport _ _ (select_good hn edge Δ γ k hc) tp

/-- Success-branch identification of the selected instance and of its output bits at the
canonical schedule `L = Nat.clog 2 n` (the scheduled branch of `select`). -/
theorem success_selected {n m : ℕ} [NeZero n] (hn : 0 < n) (edge : Fin m → Bool → Fin n)
    (Δ : ℕ) (γ : ℚ) (k : ℕ)
    [NeZero (width (Nat.clog 2 n))] [NeZero (width (Nat.clog 2 n) - 2)]
    [NeZero (outerWidth (Nat.clog 2 n))]
    [NeZero (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 n))]
    [NeZero (ParameterizedCanonicalSource.coverWidth n m (Nat.clog 2 n) Δ γ)]
    (hc : CompletePublicScheduleScratch.Checks (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ)
    (tp : (select hn edge Δ γ k).Tape) (bytes : List Bool) :
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
    let activity := SourceActiveRank.scanAtCanonical edge
      (by have := SourceProfiles.width_ge_four L; omega)
      (SourceRepetitionScratch.outerWidth_eq_sourceQ0_mul_rep L (Fin m) hc.1)
    let ξ := CanonicalDefaultSource.canonicalDefaultTails L n w Q hn (NeZero.pos w)
      (NeZero.pos Q)
    ∀ (_hres : GeneratorCode.run (SuccessOrient.Bv n p s q₁ q₂ w Q)
        (SuccessOrient.Rv p s q₁ q₂ w Q k mX mY) (le_refl _)
        (SuccessOrient.Nv p s q₁ q₂ w Q k mX mY)
        (GeneratorStateSize.initialBounded (SuccessOrient.root n p s q₁ q₂ w Q k mX mY)
          (SamplerFallbackJoin.alphabet_bound n p s q₁ q₂ w Q k mX mY
            (NeZero.pos n) (by show 0 < LookupSeed.width L; unfold LookupSeed.width; positivity)
            (SourceProfiles.width_ge_four L) (NeZero.pos q₁) (NeZero.pos q₂) (NeZero.pos w)
            (NeZero.pos Q)))
        (physTape n p s q₁ q₂ w Q k mX mY (selTape hn edge Δ γ k hc tp)) = some bytes)
      (ys : Fin mY → Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n))
        s q₁ q₂ w Q k)
      (xs : Fin mX → Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n))
        s q₁ q₂ w Q k),
      bytes =
        (List.ofFn (fun j => (defaultCarrierCodecs n p s q₁ q₂ w Q k).2.encode (ys j))).flatten ++
          (List.ofFn (fun i => (defaultCarrierCodecs n p s q₁ q₂ w Q k).1.encode (xs i))).flatten →
      let f : Fin mX → Fin mY → Bool := fun i j =>
        RecursiveEntries.matrix (LookupSeed.matrix p) activity ξ k (xs i) (ys j)
      EncodedSelectedOutput.selectedInstance hn edge Δ γ k tp =
          ⟨mX, mY, thr, MatrixMaterialization.rowMajor f⟩ ∧
        EncodedSelectedOutput.outputBits hn edge Δ γ k tp =
          EncodedCommunication.natField mX ++ EncodedCommunication.natField mY ++
            EncodedCommunication.natField thr ++ MatrixMaterialization.rowMajor f := by
  intro L p s q₁ q₂ w Q mX mY thr activity ξ hres ys xs hbytes f
  have hp : 0 < p := by show 0 < LookupSeed.width L; unfold LookupSeed.width; positivity
  have h := run_success (n := n) (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
    hp (SourceProfiles.width_ge_four L) activity ξ k mX mY
    (selTape hn edge Δ γ k hc tp) bytes hres ys xs hbytes
  have hsel : EncodedSelectedOutput.selectedInstance hn edge Δ γ k tp =
      ⟨mX, mY, thr, MatrixMaterialization.rowMajor f⟩ := by
    rw [selected_eq_scheduled hn edge Δ γ k hc tp]
    show EncodedSelectedOutput.instanceOf (YaoMaterialization.tabulate
      (RecursiveSamplingExecution.run (finCongr (Fintype.card_fin n))
        (SourceProfiles.width_ge_four L) p hp activity ξ k mX mY
        (RecursiveSamplingTape.readTape _ _ _ (selTape hn edge Δ γ k hc tp)))) thr = _
    rw [h]
    rfl
  refine ⟨hsel, ?_⟩
  unfold EncodedSelectedOutput.outputBits
  rw [hsel]
  rfl

end

#print axioms rowMajor_eq_tabulate
#print axioms run_transport
#print axioms physTape_word
#print axioms decode_success
#print axioms run_success
#print axioms instance_transport
#print axioms selected_eq_scheduled
#print axioms success_selected

end Paper2.SuccessIdent
