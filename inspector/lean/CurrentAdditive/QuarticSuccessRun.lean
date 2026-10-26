import CurrentAdditive.QuarticMachineIdent
import Paper2.SuccessRunMain

/-! Unit 3, segments (5) and (6): the success-branch run of ONE fixed program
`succProg = SuccessOrient.program ; SuccessXfer.xfer ; WEntry.tableHeader` (see `SuccessRun`),
ending with `outputBits27 hn edge Δ γ k tp ++ output` in the header output
cell. Supplied at the start (NOT produced here): the raw public unary counts inside the
admitted `SuccessOrient.startBank` (as in the admitted success chain), the master region
`restL g r`, unary `k`, the output prefix and the unary threshold `thr` (inside `preJH`). -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.CurrentAdditive.QuarticSuccessRun

noncomputable section

open Paper2.SuccessRun Paper2.CurrentAdditive.QuarticConstructor

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

/-- Orientation, then transfer and writer/header: ONE fixed program. -/
def succProg := BitMachineRawSequence.program orientL tailProg
  (SamplerFallbackJoin.labelOf tailProg (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩)))
  SuccessOrient.startControl ((none : Option Bool), hCtl)

theorem success_run27 (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
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
      ∃ t ≤ SamplerFallbackJoin.clock n p s q₁ q₂ w Q k mX mY + (3 * bytes.length + 4) +
          (6 * (2 * xLmax g k mX mY xs ys + 3) + 1 +
            (MatrixTableWriter.writerBound mX mY
              (WEntry.Tent g hg (SourceProfiles.width_ge_four L) r hq ξ k mX mY xs ys) +
              WEntry.hdrBd mX mY thr + 1) + 1) + 1,
        ∃ v, ∃ (d : CodeTableFallback.Config) (G : SamplerParameterBank.Private → List Bool)
          (F : JH WEntry.Kw → List Bool),
        ((advance succProg)^[t])
          (⟨some (BitMachineRawSequence.leftLabel SuccessOrient.startLabel),
            (SuccessOrient.startControl, ((none : Option Bool), hCtl)),
            Sum.elim (SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word)
              (Sum.elim (preJH (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
                g r k thr output) (fun _ => []))⟩ :
            TM2.Cfg (fun _ : JT => Bool) _ _) =
          ⟨none, v, Sum.elim (SuccessFetchJoin.post n p s q₁ q₂ w Q k mX mY word d G bytes)
            (Sum.elim F (fun _ => []))⟩ ∧
        F wOut = outputBits27 hn edge Δ γ k tp ++ output ∧
        (∀ a : MatrixTableWriter.Stack WEntry.Kw, a ≠ .inr .output →
          F (.inl a) = (MatrixTableWriter.ready (WEntry.bankW g r k mX mY xs ys) mX mY 0 0 0 0 []
            ((selectedInstance27 hn edge Δ γ k tp).table ++
              output)).contents a) ∧
        F thrM = List.replicate thr true ∧ F scrH = [] := by
  intro n m edge L p s q₁ q₂ w Q r mX mY thr hq ξ word hres
  have hp : 0 < p := by show 0 < LookupSeed.width L; unfold LookupSeed.width; positivity
  have hs : 4 ≤ s := SourceProfiles.width_ge_four L
  obtain ⟨t₀, d, G, ht₀, -, -, hout, hresult⟩ := SuccessOrient.run n p s q₁ q₂ w Q k mX mY
    (NeZero.pos n) hp hs (NeZero.pos q₁) (NeZero.pos q₂) (NeZero.pos w) (NeZero.pos Q)
    (SuccessIdent.physTape n p s q₁ q₂ w Q k mX mY (selTape27 hn edge Δ γ k hc tp))
  rw [hres] at ht₀ hout hresult
  obtain ⟨hc0, -⟩ := hresult
  obtain ⟨a, hd, -, -⟩ := hout
  have hprod := OutputSkipper.run_produces _ _ (le_refl _) _ _ _
    (SuccessIdent.physTape n p s q₁ q₂ w Q k mX mY (selTape27 hn edge Δ γ k hc tp))
    bytes hres
  obtain ⟨ys, xs, hsam, hbytes, -, -⟩ := SuccessCodec.success_codec hp hs k mX mY bytes hprod
  have hword : (RecursiveSamplingTape.writeTape (SuccessOrient.Bv n p s q₁ q₂ w Q)
      (SuccessOrient.Rv p s q₁ q₂ w Q k mX mY) (SuccessOrient.Nv p s q₁ q₂ w Q k mX mY)
      (SuccessIdent.physTape n p s q₁ q₂ w Q k mX mY
        (selTape27 hn edge Δ γ k hc tp))).val = word := by
    rw [SuccessIdent.physTape_word]
    exact selTape27_bits hn edge Δ γ k hc tp
  rw [hword] at hc0
  have hsel := success_selected27 hn edge Δ γ k hc tp bytes hres ys xs hbytes
  have hd' : d.stk = Sum.elim a.stk (CodeTableFallback.writerData mX mY).contents := by
    rw [hd]
  -- the success-bank cells read by the transfer
  have hPfw : SuccessFetchJoin.post n p s q₁ q₂ w Q k mX mY word d G bytes
      SuccessFetchJoin.fwCell =
      (WEntry.colWords g k mY ys).flatten ++ (WEntry.rowWords g k mX xs).flatten := by
    simp only [SuccessFetchJoin.post, SuccessFetchJoin.fwCell, Function.update_self]
    exact hbytes
  have hPcc : SuccessFetchJoin.post n p s q₁ q₂ w Q k mX mY word d G bytes
      SuccessFetchJoin.colCodeCell = encodeCode (seedRecursiveCodes n p s q₁ q₂ w Q k).2 := by
    simp only [SuccessFetchJoin.post]
    rw [Function.update_of_ne (by simp [SuccessFetchJoin.colCodeCell,
      SuccessFetchJoin.sampleCell]), SuccessFetchJoin.fallbackBank_colCode]
  have hPrc : SuccessFetchJoin.post n p s q₁ q₂ w Q k mX mY word d G bytes
      SuccessFetchJoin.rowCodeCell = encodeCode (seedRecursiveCodes n p s q₁ q₂ w Q k).1 := by
    simp only [SuccessFetchJoin.post]
    rw [Function.update_of_ne (by simp [SuccessFetchJoin.rowCodeCell,
      SuccessFetchJoin.sampleCell]), SuccessFetchJoin.fallbackBank_rowCode]
  have hPmy : SuccessFetchJoin.post n p s q₁ q₂ w Q k mX mY word d G bytes
      SuccessFetchJoin.colsCell = List.replicate mY true := by
    simp only [SuccessFetchJoin.post]
    rw [Function.update_of_ne (by simp [SuccessFetchJoin.colsCell]),
      SuccessFetchJoin.fallbackBank_cols _ _ _ _ _ _ _ _ _ _ _ _ _ d G a hd']
  have hPmx : SuccessFetchJoin.post n p s q₁ q₂ w Q k mX mY word d G bytes
      rowsCell = List.replicate mX true := by
    simp only [SuccessFetchJoin.post]
    rw [Function.update_of_ne (by simp [rowsCell]),
      SuccessXfer.fallbackBank_rows _ _ _ _ _ _ _ _ _ _ _ _ _ d G a hd']
  -- (1) orientation, lifted beside the header bank
  have r1 := BitMachineStackRun.run oE
    (Sum.elim (fun _ => []) (Sum.elim (preJH (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w)
      (Q := Q) g r k thr output) (fun _ : Fin 1 => [])))
    SuccessOrient.program
    ⟨some SuccessOrient.startLabel, SuccessOrient.startControl,
      SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word⟩ t₀
  rw [hc0] at r1
  simp only [stackCfg] at r1
  rw [bank_oE, bank_oE] at r1
  -- (2) transfer
  obtain ⟨tx, htx, vx, rx⟩ := SuccessXfer.xfer_run g r k mX mY xs ys thr output
    (SuccessFetchJoin.post n p s q₁ q₂ w Q k mX mY word d G bytes) hPfw hPcc hPrc hPmy hPmx
  rw [← preJH_eq_blank g r k mX mY xs ys thr output] at rx
  -- (3) writer then header
  obtain ⟨th, hth, vh, F, rh, hF, hfr, hthr, hscr⟩ := WEntry.table_header g hg hp hs r hq ξ
    (fun k' i => StepXCanon.canonical_hfix L w Q r g hg hn (NeZero.pos w) (NeZero.pos Q) hq k' i)
    k mX mY xs ys thr output
  have rhL := HeaderJoin.liftG hE WEntry.tableHeader
    (Sum.elim (SuccessFetchJoin.post n p s q₁ q₂ w Q k mX mY word d G bytes)
      (Sum.elim (finJH g r k mX mY xs ys thr output) (fun _ : Fin 1 => [])))
    (finJH g r k mX mY xs ys thr output) F (fun _ => rfl) _ _ _ th rh
  rw [bank_hE] at rhL
  -- (4) compose
  obtain ⟨u1, hu1, ru1⟩ := BitMachineRawSequence.runs xfer headerL
    (.inl ⟨0, by omega⟩) (BitMachineRawSequence.leftLabel (.inr (.copy .rows)))
    (none : Option Bool) vx hCtl vh _ _ _ tx th rx rhL
  obtain ⟨u, hu, ru⟩ := BitMachineRawSequence.runs orientL tailProg
    SuccessOrient.startLabel (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩))
    SuccessOrient.startControl (SamplerFallbackJoin.startControl, none)
    ((none : Option Bool), hCtl) ((none : Option Bool), vh) _ _ _ t₀ u1 r1 ru1
  refine ⟨ys, xs, hsam, hbytes, hsel.1, u, ?_, _, d, G, F, ru, ?_, ?_, hthr, hscr⟩
  · simp only [SuccessOrient.outputTime] at ht₀
    have : th ≤ MatrixTableWriter.writerBound mX mY
        (WEntry.Tent g hg (SourceProfiles.width_ge_four L) r hq ξ k mX mY xs ys) +
        WEntry.hdrBd mX mY thr + 1 := hth
    omega
  · rw [hF, hsel.2]
    simp only [List.append_assoc]
    rfl
  · intro a' ha
    rw [hfr a' ha, hsel.1]
    rfl

end

#print axioms success_run27

end Paper2.CurrentAdditive.QuarticSuccessRun
