import CurrentAdditive.CanonicalAmbientSource

/-! The source-stage exit bank is physically copied into the three public
input cells of the forthcoming exact degree compiler. The copy programs
preserve the source cells and reuse one empty scratch cell. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.FiniteFieldConstructor.CanonicalSourcePrelude
open Paper2.YaoMachine Paper2.YaoLookup
open Paper2.YaoSourceCodec

def sourceBank {t N : ℕ} (x : Paper2.YaoSourceCodec.YaoSource t) :
    Cell t N → List Bool :=
  bank (sourceEmbed t N) (blank t N) (sourceReady x)

theorem sourceBank_source {t N : ℕ} (x : Paper2.YaoSourceCodec.YaoSource t)
    (k : WStack t 0) : sourceBank (N := N) x (.source k) = sourceReady x k := by
  simpa [sourceBank, sourceEmbed] using
    bank_at (sourceEmbed t N) (blank t N) (sourceReady x) k

theorem sourceBank_degree {t N : ℕ} (x : Paper2.YaoSourceCodec.YaoSource t)
    (k : Fin N) : sourceBank x (.degree k) = [] := by
  apply bank_outside (sourceEmbed t N) (blank t N) (sourceReady x)
  intro ⟨j, hj⟩
  cases hj

theorem sourceBank_copyScratch {t N : ℕ} (x : Paper2.YaoSourceCodec.YaoSource t)
    (k : Fin 3) : sourceBank (N := N) x (.copyScratch k) = [] := by
  apply bank_outside (sourceEmbed t N) (blank t N) (sourceReady x)
  intro ⟨j, hj⟩
  cases hj

def bPlace (t : ℕ) (N : ℕ) (hN : 2 < N) : Fin 3 ↪ Cell t N :=
  ⟨![.source (sN 5), .degree ⟨0, by omega⟩, .copyScratch 0], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all⟩
def HPlace (t : ℕ) (N : ℕ) (hN : 2 < N) : Fin 3 ↪ Cell t N :=
  ⟨![.source (sN 6), .degree ⟨1, by omega⟩, .copyScratch 0], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all⟩
def KPlace (t : ℕ) (N : ℕ) (hN : 2 < N) : Fin 3 ↪ Cell t N :=
  ⟨![.source (sN 9), .degree ⟨2, hN⟩, .copyScratch 0], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all⟩

def copies2 (t N : ℕ) (hN : 2 < N) :=
  BitMachineRawSequence.program
    (MatrixStage4ScalarPreparationOps.copyProgram (HPlace t N hN))
    (MatrixStage4ScalarPreparationOps.copyProgram (KPlace t N hN))
    BitMachineCopy.Label.scan none none
def copies3 (t N : ℕ) (hN : 2 < N) :=
  BitMachineRawSequence.program
    (MatrixStage4ScalarPreparationOps.copyProgram (bPlace t N hN))
    (copies2 t N hN)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none (none, none)

theorem physical_degree_inputs (t N : ℕ) (hN : 2 < N)
    (x : Paper2.YaoSourceCodec.YaoSource t) :
    let b := paddedEdgeBits x.2.1
    let H := paddedEdgeCount x.2.1
    let K := arity t
    ∃ steps ≤ (2*b+2) + (2*H+2) + (2*K+2) + 2,
      ((advance (copies3 t N hN))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none, (none, none)), sourceBank x⟩ :
          TM2.Cfg (fun _ : Cell t N => Bool) _ _) =
        ⟨none, (none, (none, none)),
          Function.update
            (Function.update
              (Function.update (sourceBank x) (.degree ⟨0, by omega⟩)
                (List.replicate b true)) (.degree ⟨1, by omega⟩)
              (List.replicate H true)) (.degree ⟨2, hN⟩)
            (List.replicate K true)⟩ := by
  dsimp only
  let b := paddedEdgeBits x.2.1
  let H := paddedEdgeCount x.2.1
  let K := arity t
  let S := sourceBank (N := N) x
  let S1 := Function.update S (.degree ⟨0, by omega⟩) (List.replicate b true)
  let S2 := Function.update S1 (.degree ⟨1, by omega⟩) (List.replicate H true)
  let S3 := Function.update S2 (.degree ⟨2, hN⟩) (List.replicate K true)
  have hsource := sourceReady_public_cells x
  obtain ⟨_, _, _, hb, hH, hK⟩ := hsource
  have hr1 := MatrixStage4ScalarPreparationOps.copy_run (bPlace t N hN) S
    (by simpa [bPlace, S] using sourceBank_copyScratch (N := N) x 0)
  have hr1' : ((advance (MatrixStage4ScalarPreparationOps.copyProgram (bPlace t N hN)))^[2*b+2])
      (⟨some BitMachineCopy.Label.scan, none, S⟩ :
        TM2.Cfg (fun _ : Cell t N => Bool) _ _) = ⟨none, none, S1⟩ := by
    simpa [bPlace, S1, S, sourceBank_source, sourceBank_degree, hb] using hr1
  have hr2 := MatrixStage4ScalarPreparationOps.copy_run (HPlace t N hN) S1
    (by simp [HPlace, S1, S, sourceBank_copyScratch])
  have hr2' : ((advance (MatrixStage4ScalarPreparationOps.copyProgram (HPlace t N hN)))^[2*H+2])
      (⟨some BitMachineCopy.Label.scan, none, S1⟩ :
        TM2.Cfg (fun _ : Cell t N => Bool) _ _) = ⟨none, none, S2⟩ := by
    simpa [HPlace, S2, S1, S, sourceBank_source, sourceBank_degree, hH] using hr2
  have hr3 := MatrixStage4ScalarPreparationOps.copy_run (KPlace t N hN) S2
    (by simp [KPlace, S2, S1, S, sourceBank_copyScratch])
  have hr3' : ((advance (MatrixStage4ScalarPreparationOps.copyProgram (KPlace t N hN)))^[2*K+2])
      (⟨some BitMachineCopy.Label.scan, none, S2⟩ :
        TM2.Cfg (fun _ : Cell t N => Bool) _ _) = ⟨none, none, S3⟩ := by
    simpa [KPlace, S3, S2, S1, S, sourceBank_source, sourceBank_degree, hK] using hr3
  obtain ⟨u, hu, hrun2⟩ := BitMachineRawSequence.runs
    (MatrixStage4ScalarPreparationOps.copyProgram (HPlace t N hN))
    (MatrixStage4ScalarPreparationOps.copyProgram (KPlace t N hN))
    BitMachineCopy.Label.scan BitMachineCopy.Label.scan
    none none none none S1 S2 S3 (2*H+2) (2*K+2) hr2' hr3'
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    (MatrixStage4ScalarPreparationOps.copyProgram (bPlace t N hN))
    (copies2 t N hN)
    BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none none (none, none) (none, none) S S1 S3 (2*b+2) u hr1' hrun2
  exact ⟨steps, by omega, by simpa [copies3, S3, S2, S1, S] using hrun⟩

def sourceToDegreeInputs (t N : ℕ) (hN : 2 < N) :=
  BitMachineRawSequence.program (sourceStage t N) (copies3 t N hN)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (CanonicalSourcePrelude.initialControl t) (none, (none, none))

/-- The valid-source parser/prelude and all three source-to-degree copies are
one literal program on the common ambient stack namespace. -/
theorem physical_source_to_degree_inputs (t N : ℕ) (ht : 1 ≤ t) (hN : 2 < N)
    (x : Paper2.YaoSourceCodec.YaoSource t) :
    let b := paddedEdgeBits x.2.1
    let H := paddedEdgeCount x.2.1
    let K := arity t
    ∃ steps ≤ CanonicalSourcePrelude.sourceClock x +
        ((2*b+2) + (2*H+2) + (2*K+2) + 2) + 1,
      ((advance (sourceToDegreeInputs t N hN))^[steps])
          (⟨some (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                Paper2.YaoHeaderParser.startLabel)),
            (CanonicalSourcePrelude.initialControl t, (none, (none, none))),
            bank (sourceEmbed t N) (blank t N)
              (Paper2.YaoMachine.initBank 0 x [])⟩ :
                TM2.Cfg (fun _ : Cell t N => Bool) _ _) =
          ⟨none, (CanonicalSourcePrelude.initialControl t, (none, (none, none))),
            Function.update
              (Function.update
                (Function.update (sourceBank x) (.degree ⟨0, by omega⟩)
                  (List.replicate b true)) (.degree ⟨1, by omega⟩)
                (List.replicate H true)) (.degree ⟨2, hN⟩)
              (List.replicate K true)⟩ := by
  dsimp only
  obtain ⟨s, hs, cs, hsource⟩ := physical_ambient_source t N ht x
  obtain ⟨u, hu, hdegree⟩ := physical_degree_inputs t N hN x
  have hsource' : ((advance (sourceStage t N))^[s])
      (stackCfg (sourceEmbed t N) (blank t N)
        (⟨some (BitMachineRawSequence.leftLabel
            Paper2.YaoHeaderParser.startLabel),
          CanonicalSourcePrelude.initialControl t,
          Paper2.YaoMachine.initBank 0 x []⟩ :
            TM2.Cfg (fun _ : WStack t 0 => Bool) _ _)) =
      ⟨none, cs, sourceBank x⟩ := by
    simpa [stackCfg, sourceBank] using hsource
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    (sourceStage t N) (copies3 t N hN)
    (BitMachineRawSequence.leftLabel Paper2.YaoHeaderParser.startLabel)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (CanonicalSourcePrelude.initialControl t) cs
    (none, (none, none)) (none, (none, none))
    (bank (sourceEmbed t N) (blank t N) (Paper2.YaoMachine.initBank 0 x []))
    (sourceBank x) _ s u
    hsource' hdegree
  refine ⟨steps, by omega, ?_⟩
  simpa [sourceToDegreeInputs] using hrun

#print axioms physical_degree_inputs
#print axioms physical_source_to_degree_inputs

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
