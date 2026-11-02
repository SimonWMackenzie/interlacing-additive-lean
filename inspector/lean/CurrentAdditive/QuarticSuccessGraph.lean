import CurrentAdditive.QuarticSuccessInstall
import Paper2.SuccessGraphMain

/-! Unit 3, segments (5) and (6): the whole success branch as ONE fixed program
`SuccessGraph.fullProg2 = graphProg ; (install ; SuccessRun.succProg)`, from the admitted success
start bank beside the writer bank `preJHm g r thr output` (parameter-free and without unary `m`)
and a blank side region, to `outputBits27 hn edge Δ γ k tp ++ output`. -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.CurrentAdditive.QuarticSuccessGraph

noncomputable section

open Paper2.SuccessGraph Paper2.CurrentAdditive.QuarticConstructor

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource GeneratorFullSample
open RecursiveSamplingProgram RecursiveSamplingLaws RecursiveLabelCodecScratch
open RecursiveEntries RecursiveSampling RecursiveRequestCodeShape
open SourceProfileParameters SourceRecursiveNoSampling TotalFiniteConstructorScratch
open Paper2.HeaderJoin (JH hjIn hjProg wOut thrM scrH)
open Paper2.SuccessXfer (OS JT xLmax)
open Paper2.SuccessRun (preJH hCtl succProg)
open Paper2.SuccessInstall (mC preJH0 instBd install fullProg)

theorem success_run_graph27 (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hn : 0 < g.vertices) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    [NeZero (width (Nat.clog 2 g.vertices))] [NeZero (width (Nat.clog 2 g.vertices) - 2)]
    [NeZero (outerWidth (Nat.clog 2 g.vertices))]
    [NeZero (CurrentAdditive.RandomizedSchedule.width27 (Nat.clog 2 g.vertices))]
    [NeZero (CurrentAdditive.RandomizedSchedule.Q27 (V := Fin g.vertices) (E := Fin g.edges.length)
      (Nat.clog 2 g.vertices) γ Δ)]
    (hc : CurrentAdditive.QuarticSchedule.Checks27 (V := Fin g.vertices) (Edges := Fin g.edges.length)
      (Nat.clog 2 g.vertices) Δ γ)
    (tp : (select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape)
    (bytes output : List Bool) :
    let n := g.vertices
    let m := g.edges.length
    let edge := CanonicalEdgeTape.graphEdge g hg
    let L := Nat.clog 2 n
    let p := LookupSeed.width L
    let s := width L
    let q₁ := width L - 2
    let q₂ := outerWidth L
    let w := CurrentAdditive.RandomizedSchedule.width27 L
    let Q := CurrentAdditive.RandomizedSchedule.Q27 (V := Fin n) (E := Fin m) L γ Δ
    let r := ParameterizedCanonicalSource.rep L m
    let mX := sourceRows L (4 * RestorationWidthScheduleScratch.ell L)
      (CurrentAdditive.RandomizedSchedule.q27 (V := Fin n) (E := Fin m) L γ Δ) k
    let mY := sourceCols L (4 * RestorationWidthScheduleScratch.ell L)
      (CurrentAdditive.RandomizedSchedule.q27 (V := Fin n) (E := Fin m) L γ Δ) k
    let thr := sourceBudget L (4 * RestorationWidthScheduleScratch.ell L)
      (CurrentAdditive.RandomizedSchedule.q27 (V := Fin n) (E := Fin m) L γ Δ) k
    let hq := SourceRepetitionScratch.outerWidth_eq_sourceQ0_mul_rep L (Fin m) hc.1
    let ξ := CanonicalDefaultSource.canonicalDefaultTails L n w Q hn (NeZero.pos w)
      (NeZero.pos Q)
    let word := (select27 hn edge Δ γ k).tapeBits tp
    GeneratorCode.run (SuccessOrient.Bv n p s q₁ q₂ w Q)
        (SuccessOrient.Rv p s q₁ q₂ w Q k mX mY) (le_refl _)
        (SuccessOrient.Nv p s q₁ q₂ w Q k mX mY)
        (GeneratorStateSize.initialBounded (SuccessOrient.root n p s q₁ q₂ w Q k mX mY)
          (SamplerFallbackJoin.alphabet_bound n p s q₁ q₂ w Q k mX mY
            (NeZero.pos n) (by show 0 < LookupSeed.width L; unfold LookupSeed.width; positivity)
            (SourceProfiles.width_ge_four L) (NeZero.pos q₁) (NeZero.pos q₂) (NeZero.pos w)
            (NeZero.pos Q)))
        (SuccessIdent.physTape n p s q₁ q₂ w Q k mX mY
          (selTape27 hn edge Δ γ k hc tp)) = some bytes →
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
      selectedInstance27 hn edge Δ γ k tp =
        ⟨mX, mY, thr, MatrixMaterialization.rowMajor (fun i j =>
          RecursiveEntries.matrix (LookupSeed.matrix p)
            (SourceActiveRank.scanAtCanonical edge
              (by have := SourceProfiles.width_ge_four L; omega) hq) ξ k (xs i) (ys j))⟩ ∧
      ∃ t ≤ ((1 * (2 * (EncodedGraph.encode g).length + 3) + 1) +
          103 * ((EncodedGraph.encode g).length + 1) ^ 3 + 1 +
          (1 * (2 * g.edges.length + 3) + 1) + 1) + (instBd s q₁ Q p w k + (SamplerFallbackJoin.clock n p s q₁ q₂ w Q k mX mY + (3 * bytes.length + 4) +
          (6 * (2 * xLmax g k mX mY xs ys + 3) + 1 +
            (MatrixTableWriter.writerBound mX mY
              (WEntry.Tent g hg (SourceProfiles.width_ge_four L) r hq ξ k mX mY xs ys) +
              WEntry.hdrBd mX mY thr + 1) + 1) + 1) + 1) + 1,
        ∃ v, ∃ (d : CodeTableFallback.Config) (G : SamplerParameterBank.Private → List Bool)
          (F : JH WEntry.Kw → List Bool),
        ((advance fullProg2)^[t])
          (⟨some (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩)))),
            ((((none : Option Bool), gCtl), (none : Option Bool)), fCtl),
            Sum.elim (Sum.elim (SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word)
              (Sum.elim (preJHm g r thr output) (fun _ => []))) (fun _ => [])⟩ :
            TM2.Cfg (fun _ : JT2 => Bool) _ _) =
          ⟨none, v, Sum.elim (Sum.elim
            (SuccessFetchJoin.post n p s q₁ q₂ w Q k mX mY word d G bytes)
            (Sum.elim F (fun _ => []))) (PublicGraphEndpointMachine.resultBank g hg)⟩ ∧
        F wOut = outputBits27 hn edge Δ γ k tp ++ output ∧
        (∀ a : MatrixTableWriter.Stack WEntry.Kw, a ≠ .inr .output →
          F (.inl a) = (MatrixTableWriter.ready (WEntry.bankW g r k mX mY xs ys) mX mY 0 0 0 0 []
            ((selectedInstance27 hn edge Δ γ k tp).table ++
              output)).contents a) ∧
        F thrM = List.replicate thr true ∧ F scrH = [] := by
  intro n m edge L p s q₁ q₂ w Q r mX mY thr hq ξ word hres
  obtain ⟨ys, xs, hsam, hbytes, hsel, t, ht, v, d, G, F, hrun, hF, hfr, hthr, hscr⟩ :=
    QuarticSuccessInstall.success_run_installed27 g hg hn Δ γ k hc tp bytes output hres
  obtain ⟨tg, htg, vg, hrg⟩ := graph_run g hg
    (SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word) r thr output
  have rL := BitMachineStackRun.run ιL
    (Sum.elim (Sum.elim (SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word)
      (Sum.elim (preJH0 g r thr output) (fun _ => [])))
      (PublicGraphEndpointMachine.resultBank g hg))
    fullProg
    (⟨some (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩))),
      (((none : Option Bool), (none : Option Bool)),
        (SuccessOrient.startControl, ((none : Option Bool), hCtl))),
      Sum.elim (SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word)
        (Sum.elim (preJH0 g r thr output) (fun _ => []))⟩ :
      TM2.Cfg (fun _ : JT => Bool) _ _) t
  rw [hrun] at rL
  simp only [stackCfg] at rL
  rw [bank_L, bank_L] at rL
  obtain ⟨u, hu, ru⟩ := BitMachineRawSequence.runs graphProg fullL
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩)))
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩)))
    (((none : Option Bool), gCtl), (none : Option Bool))
    (((none : Option Bool), gCtl), vg) fCtl v _ _ _ tg t hrg rL
  refine ⟨ys, xs, hsam, hbytes, hsel, u, ?_, _, d, G, F, ru, hF, hfr, hthr, hscr⟩
  exact le_trans hu (Nat.add_le_add_right (Nat.add_le_add htg ht) 1)

end

#print axioms success_run_graph27

end Paper2.CurrentAdditive.QuarticSuccessGraph
