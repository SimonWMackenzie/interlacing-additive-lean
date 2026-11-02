import Paper2.SuccessInstallRun

/-! Unit 3, segments (5) and (6): the whole success branch as ONE fixed program
`SuccessInstall.fullProg = install ; SuccessRun.succProg` (production `BitMachineRawSequence`,
one charged handoff), from the admitted success start bank `SuccessOrient.startBank … word`
(`word = (select …).tapeBits tp`) beside the parameter-free writer bank
`SuccessInstall.preJH0 g r thr output`, to `EncodedSelectedOutput.outputBits hn edge Δ γ k tp ++
output` in the header output cell. Compared with `SuccessRun.success_run`, the master-region
parameter cells (unary `s+1`, `s`, `q₁`, `s`, `Q`, `p`, `w`) and unary `k` are now produced from
the raw public counts of the admitted start bank. -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.SuccessInstall

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource GeneratorFullSample
open RecursiveSamplingProgram RecursiveSamplingLaws RecursiveLabelCodecScratch
open RecursiveEntries RecursiveSampling RecursiveRequestCodeShape
open SourceProfileParameters SourceRecursiveNoSampling TotalFiniteConstructorScratch
open Paper2.HeaderJoin (JH hjIn hjProg wOut thrM scrH)
open Paper2.SuccessXfer (OS JT dsts blank finJH xfer xLmax rowsCell)
open Paper2.SuccessRun (preJH auxPre hCtl succProg)

theorem success_run_installed (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
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
    ∃ (ys : Fin mY → Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n))
        s q₁ q₂ w Q k)
      (xs : Fin mX → Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n))
        s q₁ q₂ w Q k),
      Produces (samples (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
          (finCongr (Fintype.card_fin n)) (SourceProfiles.width_ge_four L)
          (RecursiveSamplingSeed.seedRow p)
          (RecursiveSamplingSeed.seedColumn p
            (by show 0 < LookupSeed.width L; unfold LookupSeed.width; positivity))
          k mX mY) (ys, xs) ∧
      bytes = (WEntry.colWords g k mY ys).flatten ++ (WEntry.rowWords g k mX xs).flatten ∧
      EncodedSelectedOutput.selectedInstance hn edge Δ γ k tp =
        ⟨mX, mY, thr, MatrixMaterialization.rowMajor (fun i j =>
          RecursiveEntries.matrix (LookupSeed.matrix p)
            (SourceActiveRank.scanAtCanonical edge
              (by have := SourceProfiles.width_ge_four L; omega) hq) ξ k (xs i) (ys j))⟩ ∧
      ∃ t ≤ instBd s q₁ Q p w k + (SamplerFallbackJoin.clock n p s q₁ q₂ w Q k mX mY + (3 * bytes.length + 4) +
          (6 * (2 * xLmax g k mX mY xs ys + 3) + 1 +
            (MatrixTableWriter.writerBound mX mY
              (WEntry.Tent g hg (SourceProfiles.width_ge_four L) r hq ξ k mX mY xs ys) +
              WEntry.hdrBd mX mY thr + 1) + 1) + 1) + 1,
        ∃ v, ∃ (d : CodeTableFallback.Config) (G : SamplerParameterBank.Private → List Bool)
          (F : JH WEntry.Kw → List Bool),
        ((advance fullProg)^[t])
          (⟨some (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩))),
            (((none : Option Bool), (none : Option Bool)),
              (SuccessOrient.startControl, ((none : Option Bool), hCtl))),
            Sum.elim (SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word)
              (Sum.elim (preJH0 g r thr output) (fun _ => []))⟩ :
            TM2.Cfg (fun _ : JT => Bool) _ _) =
          ⟨none, v, Sum.elim (SuccessFetchJoin.post n p s q₁ q₂ w Q k mX mY word d G bytes)
            (Sum.elim F (fun _ => []))⟩ ∧
        F wOut = EncodedSelectedOutput.outputBits hn edge Δ γ k tp ++ output ∧
        (∀ a : MatrixTableWriter.Stack WEntry.Kw, a ≠ .inr .output →
          F (.inl a) = (MatrixTableWriter.ready (WEntry.bankW g r k mX mY xs ys) mX mY 0 0 0 0 []
            ((EncodedSelectedOutput.selectedInstance hn edge Δ γ k tp).table ++
              output)).contents a) ∧
        F thrM = List.replicate thr true ∧ F scrH = [] := by
  intro n m edge L p s q₁ q₂ w Q r mX mY thr hq ξ word hres
  obtain ⟨ys, xs, hsam, hbytes, hsel, t, ht, v, d, G, F, hrun, hF, hfr, hthr, hscr⟩ :=
    SuccessRun.success_run g hg hn Δ γ k hc tp bytes output hres
  obtain ⟨ti, hti, hri⟩ := install_run (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w)
    (Q := Q) n k mX mY word g r thr output
  obtain ⟨u, hu, ru⟩ := BitMachineRawSequence.runs install succProg
    (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩))
    (BitMachineRawSequence.leftLabel SuccessOrient.startLabel)
    ((none : Option Bool), (none : Option Bool)) ((none : Option Bool), (none : Option Bool))
    (SuccessOrient.startControl, ((none : Option Bool), hCtl)) v _ _ _ ti t hri hrun
  refine ⟨ys, xs, hsam, hbytes, hsel, u, ?_, _, d, G, F, ru, hF, hfr, hthr, hscr⟩
  exact le_trans hu (Nat.add_le_add_right (Nat.add_le_add hti ht) 1)

end

#print axioms success_run_installed

end Paper2.SuccessInstall
