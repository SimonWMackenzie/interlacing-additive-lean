import Paper2.ThrJoinRun

/-! Unit 3, segments (5) and (6): the whole success branch as ONE fixed program
`ThrJoin.fullProg3 = thrJoin ; (graphProg ; (install ; SuccessRun.succProg))`, from the admitted
success start bank (raw public counts and the selected tape word) beside the writer bank
`preJHm g r 0 output` (no parameter cell, no unary `m`, blank threshold), a blank graph side region
and a blank threshold-producer region, to `EncodedSelectedOutput.outputBits hn edge Δ γ k tp ++
output` in the header output cell. -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.ThrJoin

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
open Paper2.SuccessXfer (OS JT xLmax)
open Paper2.SuccessRun (preJH hCtl succProg)
open Paper2.SuccessInstall (mC preJH0 instBd install fullProg)
open Paper2.SuccessGraph (JT2 preJHm fullProg2 gCtl fCtl)
open Paper2.ThrProducer (Xv)

theorem success_run_full (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
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
      ∃ t ≤ joinBd p s q₂ w Q k + (((1 * (2 * (EncodedGraph.encode g).length + 3) + 1) +
          103 * ((EncodedGraph.encode g).length + 1) ^ 3 + 1 +
          (1 * (2 * g.edges.length + 3) + 1) + 1) + (instBd s q₁ Q p w k + (SamplerFallbackJoin.clock n p s q₁ q₂ w Q k mX mY + (3 * bytes.length + 4) +
          (6 * (2 * xLmax g k mX mY xs ys + 3) + 1 +
            (MatrixTableWriter.writerBound mX mY
              (WEntry.Tent g hg (SourceProfiles.width_ge_four L) r hq ξ k mX mY xs ys) +
              WEntry.hdrBd mX mY thr + 1) + 1) + 1) + 1) + 1) + 1,
        ∃ v, ∃ (d : CodeTableFallback.Config) (G : SamplerParameterBank.Private → List Bool)
          (F : JH WEntry.Kw → List Bool) (Fk : ThrProducer.TK → List Bool),
        ((advance fullProg3)^[t])
          (⟨some (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩)))),
            ((((none : Option Bool), ThrProducer.thrCtl), (none : Option Bool)), jCtl),
            Sum.elim (Sum.elim (Sum.elim (SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word)
              (Sum.elim (preJHm g r 0 output) (fun _ => []))) (fun _ => [])) (fun _ => [])⟩ :
            TM2.Cfg (fun _ : JT3 => Bool) _ _) =
          ⟨none, v, Sum.elim (Sum.elim (Sum.elim
            (SuccessFetchJoin.post n p s q₁ q₂ w Q k mX mY word d G bytes)
            (Sum.elim F (fun _ => []))) (PublicGraphEndpointMachine.resultBank g hg)) Fk⟩ ∧
        F wOut = EncodedSelectedOutput.outputBits hn edge Δ γ k tp ++ output ∧
        (∀ a : MatrixTableWriter.Stack WEntry.Kw, a ≠ .inr .output →
          F (.inl a) = (MatrixTableWriter.ready (WEntry.bankW g r k mX mY xs ys) mX mY 0 0 0 0 []
            ((EncodedSelectedOutput.selectedInstance hn edge Δ γ k tp).table ++
              output)).contents a) ∧
        F thrM = List.replicate thr true ∧ F scrH = [] ∧
        Fk ThrProducer.thrC = List.replicate thr true ∧ Fk ThrProducer.ctrC = [] ∧
        Fk ThrProducer.scrC = [] := by
  intro n m edge L p s q₁ q₂ w Q r mX mY thr hq ξ word hres
  obtain ⟨ys, xs, hsam, hbytes, hsel, t, ht, v, d, G, F, hrun, hF, hfr, hthr, hscr⟩ :=
    SuccessGraph.success_run_graph g hg hn Δ γ k hc tp bytes output hres
  obtain ⟨tj, htj, vj, Fk, rj, hFt, hFc, hFz⟩ :=
    thr_join_run n p s q₁ q₂ w Q k mX mY word g r output
  have hthrv : k * Xv (vv p s q₂ w Q) + (Nat.clog 2 p + 1) = thr := budget_eq n m Δ γ k
  have hX1 : X1 n p s q₁ q₂ w Q k mX mY word g r output
      (k * Xv (vv p s q₂ w Q) + (Nat.clog 2 p + 1)) =
      Sum.elim (Sum.elim (SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word)
        (Sum.elim (preJHm g r thr output) (fun _ => []))) (fun _ => []) := by
    rw [hthrv]
    unfold X1
    rw [thr_fill]
  rw [hX1] at rj
  have rL := BitMachineStackRun.run ιL
    (Sum.elim (Sum.elim (Sum.elim (SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word)
      (Sum.elim (preJHm g r thr output) (fun _ => []))) (fun _ => [])) Fk)
    SuccessGraph.fullProg2
    (⟨some (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩)))),
      ((((none : Option Bool), SuccessGraph.gCtl), (none : Option Bool)), SuccessGraph.fCtl),
      Sum.elim (Sum.elim (SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word)
        (Sum.elim (preJHm g r thr output) (fun _ => []))) (fun _ => [])⟩ :
      TM2.Cfg (fun _ : JT2 => Bool) _ _) t
  rw [hrun] at rL
  simp only [stackCfg] at rL
  rw [bank_L, bank_L] at rL
  obtain ⟨u, hu, ru⟩ := BitMachineRawSequence.runs thrJoin fullL
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩)))
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩))))
    (((none : Option Bool), ThrProducer.thrCtl), (none : Option Bool))
    (((none : Option Bool), ThrProducer.thrCtl), vj) jCtl v _ _ _ tj t rj rL
  refine ⟨ys, xs, hsam, hbytes, hsel, u, ?_, _, d, G, F, Fk, ru, hF, hfr, hthr, hscr, ?_, hFc,
    hFz⟩
  · exact le_trans hu (Nat.add_le_add_right (Nat.add_le_add htj ht) 1)
  · rw [hFt, hthrv]

end

#print axioms success_run_full

end Paper2.ThrJoin
