import Paper2.WHeader
import Paper2.SuccessIdent

/-! Unit 3, segments (5) and (6): the success-branch half of endpoint H-A3.

On the scheduled branch of `TotalFiniteConstructorScratch.select` (public checks pass), for a
selected tape `tp` on which the physical capped generator of the admitted success chain
returns `some bytes`:

* the admitted `SuccessFetchJoin.success_fetch` runs `SuccessOrient.program` from
  `SuccessOrient.startBank … word` (raw public unary counts and the written tape word only),
  where `word` is LITERALLY `(select …).tapeBits tp`, to the success bank `post … bytes`, and
  binds the sample `(ys, xs)` to the tape (`Produces samples … (ys, xs)`);
* the success bank holds, at `fwCell`, `colCodeCell`, `rowCodeCell`, exactly the words that the
  owner-8 writer bank `bankW g r k mX mY xs ys` holds in its sample-word and level-`k` code
  cells (same objects, `rfl`-level equalities stated below);
* the owner-8 writer-then-header program `WEntry.tableHeader`, started on that writer bank with
  the scheduled dimensions `mX = sourceRows`, `mY = sourceCols` and threshold
  `thr = sourceBudget`, halts with output cell
  `EncodedSelectedOutput.outputBits hn edge Δ γ k tp ++ output`
  (same consumer object as `TotalFiniteConstructor.select` / `outputBits`).

The fixed-tail premise is discharged by `StepXCanon.canonical_hfix`. The charged transfer of
the success-bank cells into the writer bank, and the producers of the master region, unary
`k`, the writer's `rows`/`cols` cells and the unary threshold, are NOT built here (named
remaining premises in CHECKPOINT.md). -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.SuccessHeader

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open GeneratorCode GeneratorSerialization GeneratorSource GeneratorFullSample
open RecursiveSamplingProgram RecursiveSamplingLaws RecursiveLabelCodecScratch
open RecursiveEntries RecursiveSampling RecursiveRequestCodeShape
open SourceProfileParameters SourceRecursiveNoSampling TotalFiniteConstructorScratch
open Paper2.HeaderJoin (JH hjIn hjProg wOut thrM scrH)

theorem tapeBits_transport (o o' : SelectedOutput) (e : o = o') (t : o.Tape) :
    o.tapeBits t = o'.tapeBits (cast (congrArg SelectedOutput.Tape e) t) := by
  subst e
  rfl

/-- The bits of a selected tape on the scheduled branch are the scheduled tape list. -/
theorem selTape_bits {n m : ℕ} (hn : 0 < n) (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ)
    (k : ℕ)
    (hc : CompletePublicScheduleScratch.Checks (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ)
    (tp : (select hn edge Δ γ k).Tape) :
    (select hn edge Δ γ k).tapeBits tp =
      Subtype.val (SuccessIdent.selTape hn edge Δ γ k hc tp) :=
  tapeBits_transport _ _ (select_good hn edge Δ γ k hc) tp

theorem success_header (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hn : 0 < g.vertices) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    [NeZero (width (Nat.clog 2 g.vertices))] [NeZero (width (Nat.clog 2 g.vertices) - 2)]
    [NeZero (outerWidth (Nat.clog 2 g.vertices))]
    [NeZero (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 g.vertices))]
    [NeZero (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length
      (Nat.clog 2 g.vertices) Δ γ)]
    (hc : CompletePublicScheduleScratch.Checks (V := Fin g.vertices) (E := Fin g.edges.length)
      (Nat.clog 2 g.vertices) Δ γ)
    (tp : (select hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape)
    (bytes output : List Bool) :
    let n := g.vertices
    let m := g.edges.length
    let edge := CanonicalEdgeTape.graphEdge g hg
    let L := Nat.clog 2 n
    let p := LookupSeed.width L
    let s := width L
    let q₁ := width L - 2
    let q₂ := outerWidth L
    let w := ParameterizedCanonicalSource.restorationWidth L
    let Q := ParameterizedCanonicalSource.coverWidth n m L Δ γ
    let r := ParameterizedCanonicalSource.rep L m
    let mX := sourceRows L (ParameterizedCanonicalSource.restorationDepth L)
      (ParameterizedCanonicalSource.coverDepth n m L Δ γ) k
    let mY := sourceCols L (ParameterizedCanonicalSource.restorationDepth L)
      (ParameterizedCanonicalSource.coverDepth n m L Δ γ) k
    let thr := sourceBudget L (ParameterizedCanonicalSource.restorationDepth L)
      (ParameterizedCanonicalSource.coverDepth n m L Δ γ) k
    let hq := SourceRepetitionScratch.outerWidth_eq_sourceQ0_mul_rep L (Fin m) hc.1
    let ξ := CanonicalDefaultSource.canonicalDefaultTails L n w Q hn (NeZero.pos w)
      (NeZero.pos Q)
    let word := (select hn edge Δ γ k).tapeBits tp
    GeneratorCode.run (SuccessOrient.Bv n p s q₁ q₂ w Q)
        (SuccessOrient.Rv p s q₁ q₂ w Q k mX mY) (le_refl _)
        (SuccessOrient.Nv p s q₁ q₂ w Q k mX mY)
        (GeneratorStateSize.initialBounded (SuccessOrient.root n p s q₁ q₂ w Q k mX mY)
          (SamplerFallbackJoin.alphabet_bound n p s q₁ q₂ w Q k mX mY
            (NeZero.pos n) (by show 0 < LookupSeed.width L; unfold LookupSeed.width; positivity)
            (SourceProfiles.width_ge_four L) (NeZero.pos q₁) (NeZero.pos q₂) (NeZero.pos w)
            (NeZero.pos Q)))
        (SuccessIdent.physTape n p s q₁ q₂ w Q k mX mY
          (SuccessIdent.selTape hn edge Δ γ k hc tp)) = some bytes →
    ∃ (t₀ : ℕ) (d : CodeTableFallback.Config) (G : SamplerParameterBank.Private → List Bool)
      (ys : Fin mY → Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n))
        s q₁ q₂ w Q k)
      (xs : Fin mX → Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n))
        s q₁ q₂ w Q k),
      t₀ ≤ SamplerFallbackJoin.clock n p s q₁ q₂ w Q k mX mY + (3 * bytes.length + 4) ∧
      ((advance SuccessOrient.program)^[t₀])
          ⟨some SuccessOrient.startLabel, SuccessOrient.startControl,
            SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word⟩ =
        ⟨none, (SamplerFallbackJoin.startControl, none),
          SuccessFetchJoin.post n p s q₁ q₂ w Q k mX mY word d G bytes⟩ ∧
      Produces (samples (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
          (finCongr (Fintype.card_fin n)) (SourceProfiles.width_ge_four L)
          (RecursiveSamplingSeed.seedRow p)
          (RecursiveSamplingSeed.seedColumn p
            (by show 0 < LookupSeed.width L; unfold LookupSeed.width; positivity))
          k mX mY) (ys, xs) ∧
      SuccessFetchJoin.post n p s q₁ q₂ w Q k mX mY word d G bytes SuccessFetchJoin.fwCell =
        (WEntry.colWords g k mY ys).flatten ++ (WEntry.rowWords g k mX xs).flatten ∧
      SuccessFetchJoin.post n p s q₁ q₂ w Q k mX mY word d G bytes
          SuccessFetchJoin.colCodeCell =
        encodeCode (seedRecursiveCodes n p s q₁ q₂ w Q k).2 ∧
      SuccessFetchJoin.post n p s q₁ q₂ w Q k mX mY word d G bytes
          SuccessFetchJoin.rowCodeCell =
        encodeCode (seedRecursiveCodes n p s q₁ q₂ w Q k).1 ∧
      EncodedSelectedOutput.selectedInstance hn edge Δ γ k tp =
        ⟨mX, mY, thr, MatrixMaterialization.rowMajor (fun i j =>
          RecursiveEntries.matrix (LookupSeed.matrix p)
            (SourceActiveRank.scanAtCanonical edge
              (by have := SourceProfiles.width_ge_four L; omega) hq) ξ k (xs i) (ys j))⟩ ∧
      ∃ t ≤ MatrixTableWriter.writerBound mX mY
          (WEntry.Tent g hg (SourceProfiles.width_ge_four L) r hq ξ k mX mY xs ys) +
          WEntry.hdrBd mX mY thr + 1,
        ∃ v, ∃ F : JH WEntry.Kw → List Bool,
        ((advance WEntry.tableHeader)^[t])
          (⟨some (BitMachineRawSequence.leftLabel (.inr (.copy .rows))),
            ((WEntry.wCtl, (none : Option Bool)), ((none : Option Bool), HeaderA.progCtl)),
            hjIn (MatrixTableWriter.ready (WEntry.bankW g r k mX mY xs ys) mX mY 0 0 0 0 []
              output).contents thr⟩ : TM2.Cfg (fun _ : JH WEntry.Kw => Bool) _ _) =
            ⟨none, v, F⟩ ∧
        F wOut = EncodedSelectedOutput.outputBits hn edge Δ γ k tp ++ output ∧
        (∀ a : MatrixTableWriter.Stack WEntry.Kw, a ≠ .inr .output →
          F (.inl a) = (MatrixTableWriter.ready (WEntry.bankW g r k mX mY xs ys) mX mY 0 0 0 0 []
            ((EncodedSelectedOutput.selectedInstance hn edge Δ γ k tp).table ++
              output)).contents a) ∧
        F thrM = List.replicate thr true ∧ F scrH = [] := by
  intro n m edge L p s q₁ q₂ w Q r mX mY thr hq ξ word hres
  have hp : 0 < p := by show 0 < LookupSeed.width L; unfold LookupSeed.width; positivity
  have hs : 4 ≤ s := SourceProfiles.width_ge_four L
  obtain ⟨t₀, d, G, ys, xs, ht₀, hrun, hsam, hbytes, -, -⟩ :=
    SuccessFetchJoin.success_fetch n p s q₁ q₂ w Q k mX mY hp hs
      (SuccessIdent.physTape n p s q₁ q₂ w Q k mX mY (SuccessIdent.selTape hn edge Δ γ k hc tp))
      bytes hres
  have hword : (RecursiveSamplingTape.writeTape (SuccessOrient.Bv n p s q₁ q₂ w Q)
      (SuccessOrient.Rv p s q₁ q₂ w Q k mX mY) (SuccessOrient.Nv p s q₁ q₂ w Q k mX mY)
      (SuccessIdent.physTape n p s q₁ q₂ w Q k mX mY
        (SuccessIdent.selTape hn edge Δ γ k hc tp))).val = word := by
    rw [SuccessIdent.physTape_word]
    exact (selTape_bits hn edge Δ γ k hc tp).symm
  rw [hword] at hrun
  have hsel := SuccessIdent.success_selected hn edge Δ γ k hc tp bytes hres ys xs hbytes
  obtain ⟨t, ht, v, F, r2, hF, hfr, hthr, hscr⟩ := WEntry.table_header g hg hp hs r hq ξ
    (fun k' i => StepXCanon.canonical_hfix L w Q r g hg hn (NeZero.pos w) (NeZero.pos Q) hq k' i)
    k mX mY xs ys thr output
  refine ⟨t₀, d, G, ys, xs, ht₀, hrun, hsam, ?_, ?_, ?_, hsel.1, t, ht, v, F, r2, ?_, ?_,
    hthr, hscr⟩
  · simp only [SuccessFetchJoin.post, SuccessFetchJoin.fwCell, Function.update_self]
    exact hbytes
  · simp only [SuccessFetchJoin.post]
    rw [Function.update_of_ne (by simp [SuccessFetchJoin.colCodeCell,
      SuccessFetchJoin.sampleCell]), SuccessFetchJoin.fallbackBank_colCode]
  · simp only [SuccessFetchJoin.post]
    rw [Function.update_of_ne (by simp [SuccessFetchJoin.rowCodeCell,
      SuccessFetchJoin.sampleCell]), SuccessFetchJoin.fallbackBank_rowCode]
  · rw [hF, hsel.2]
    simp only [List.append_assoc]
    rfl
  · intro a ha
    rw [hfr a ha, hsel.1]
    rfl

end

#print axioms tapeBits_transport
#print axioms selTape_bits
#print axioms success_header

end Paper2.SuccessHeader
