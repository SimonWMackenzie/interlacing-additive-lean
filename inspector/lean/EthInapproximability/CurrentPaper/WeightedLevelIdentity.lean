import EthInapproximability.CurrentPaper.WeightedLevelPublicClock
import EthInapproximability.CurrentPaper.MatrixWeightedFullBankBridge

/-! Unit 2, segment 5 (partial): same-constructor identity of the physically
produced words for ONE weighted level, with one public clock.

Instantiate the checked segment-2/4 controller at the actual level-`lvl`
parameters `i := Iteration.stepParameters G c b y lvl M` of the SAME
constructor `Iteration.step G c b y lvl M` and the SAME graph `G` (whose
literal guarded code `EncodedETHSource.serializeGraph G` is the graph operand).
Then every word the controller physically produced equals the corresponding
field of the admitted physical step's persistent entry bank
`MatrixWeightedEntryController.persistentBank (actualD G c b y lvl M)`:
writer 17 (`rx = M.rows`), 27 (`cy = M.columns`), 28 (`s`), 21 (`rawWidth`),
26 (`wordBase`), 29 (`binBase`), and the retained `s*L` equals the
`stagePrefixRows` field. The retained `a`, `q`, `L` are `Iteration.a`,
`Iteration.q₂`, `Iteration.labels` of the same step.

Scope: of the 22 persistent fields (1, 3, 4, 6, 15, 16, 17, 18, 21, 22, 26,
27, 28, 29, 47..53, 60) this identifies the six writer cells 17, 21, 26, 27,
28, 29, plus the value of field 16 held in the retained region (moved into
writer 16 by `WeightedLevelStagePrefix`). Writer 22 (`rawBits`, the raw
Stage--4 table) and the remaining fields are not produced here. The six raw
words `i` are still a typed input of the scalar controller. -/

namespace EthInapproximability.CurrentPaper.WeightedLevelIdentity

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph

noncomputable section

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

variable {VG EG : Type} [Fintype VG] [DecidableEq VG]
  [Fintype EG] [DecidableEq EG]

theorem bank17 (d : MatrixWeightedEntryController.Input) :
    MatrixWeightedEntryController.persistentBank d 17 =
      List.replicate d.rx true := by
  simp [MatrixWeightedEntryController.persistentBank]

theorem bank27 (d : MatrixWeightedEntryController.Input) :
    MatrixWeightedEntryController.persistentBank d 27 =
      List.replicate d.cy true := by
  simp [MatrixWeightedEntryController.persistentBank]

theorem bank28 (d : MatrixWeightedEntryController.Input) :
    MatrixWeightedEntryController.persistentBank d 28 =
      List.replicate d.s true := by
  simp [MatrixWeightedEntryController.persistentBank]

theorem bank21 (d : MatrixWeightedEntryController.Input) :
    MatrixWeightedEntryController.persistentBank d 21 =
      List.replicate d.rawWidth true := by
  simp [MatrixWeightedEntryController.persistentBank]

theorem bank26 (d : MatrixWeightedEntryController.Input) :
    MatrixWeightedEntryController.persistentBank d 26 =
      List.replicate d.wordBase true := by
  simp [MatrixWeightedEntryController.persistentBank]

theorem bank29 (d : MatrixWeightedEntryController.Input) :
    MatrixWeightedEntryController.persistentBank d 29 =
      List.replicate d.binBase true := by
  simp [MatrixWeightedEntryController.persistentBank]

theorem persistent_fields (G : EndpointGraph VG EG) (c b y lvl : ℕ)
    (M : Iteration.Matrix) :
    let d := ProtectedFullBankBridgeScratch.actualD G c b y lvl M
    let i := Iteration.stepParameters G c b y lvl M
    let s := Parameters.bins i
    let q := ParameterizedNP.GuardedSourceSlab.q2 G s
    let a := Parameters.firstExponent i
    MatrixWeightedEntryController.persistentBank d 17 =
        List.replicate i.rows true ∧
      MatrixWeightedEntryController.persistentBank d 27 =
        List.replicate i.columns true ∧
      MatrixWeightedEntryController.persistentBank d 28 =
        List.replicate s true ∧
      MatrixWeightedEntryController.persistentBank d 21 =
        List.replicate (MatrixStage4Codes.cols a s q i.columns) true ∧
      MatrixWeightedEntryController.persistentBank d 26 =
        List.replicate (MatrixStage4Digits.wordBase a s i.columns) true ∧
      MatrixWeightedEntryController.persistentBank d 29 =
        List.replicate (MatrixStage4Digits.binBase a s q i.columns) true ∧
      d.stagePrefixRows = s *
        PrimeSampler.size q (Parameters.balanceOrder i)
          (Construction.qOne a * i.rows) := by
  intro d i s q a
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · rw [bank17]; rfl
  · rw [bank27]; rfl
  · rw [bank28]; rfl
  · rw [bank21]; rfl
  · rw [bank26]; rfl
  · rw [bank29]; rfl

/-- One level, same constructor: the checked scalar/retention/column controller
at the actual step parameters, with its one public clock, produces exactly the
persistent-bank fields listed above and the retained `a, q, L, s*L` of the same
`Iteration.step`. -/
theorem level_scalar_identity (G : EndpointGraph VG EG) (c b y lvl : ℕ)
    (M : Iteration.Matrix) (W : Fin 64 → List Bool)
    (h17 : W 17 = []) (h62 : W 62 = [])
    (h27 : W 27 = []) (h63 : W 63 = [])
    (h28 : W 28 = []) (h61 : W 61 = [])
    (h7 : W 7 = []) (h8 : W 8 = []) (h9 : W 9 = [])
    (h10 : W 10 = []) (h11 : W 11 = []) (h12 : W 12 = [])
    (h13 : W 13 = []) (h14 : W 14 = [])
    (h15 : W 15 = []) (h18 : W 18 = [])
    (h54 : W 54 = []) (h55 : W 55 = []) (h56 : W 56 = [])
    (h57 : W 57 = []) (h58 : W 58 = []) (h60 : W 60 = []) :
    let d := ProtectedFullBankBridgeScratch.actualD G c b y lvl M
    let i := Iteration.stepParameters G c b y lvl M
    let g := EncodedETHSource.serializeGraph G
    let s := Parameters.bins i
    let q := ParameterizedNP.GuardedSourceSlab.q2 G s
    let a := Parameters.firstExponent i
    let L := PrimeSampler.size q (Parameters.balanceOrder i)
      (Construction.qOne a * i.rows)
    let W'' := Function.update
      (Function.update W 27 (List.replicate i.columns true))
      17 (List.replicate i.rows true)
    ∃ F : ETHBinsJoinedScratch.Stack → List Bool,
    ∃ Q : WeightedGraphQJoined.Stack → List Bool,
    ∃ P : ChosenPrimeRaw.Stack → List Bool,
      let T := WeightedScalarComplete.finalBank i g W'' F Q P i.rows q
      let X := WeightedLevelColumnSave.exitBank T a s q L i.rows i.columns
      ∃ u ≤ WeightedLevelPublicClock.publicBound i g (Fintype.card EG) W a s q L,
        ((advance WeightedLevelColumnSave.program)^[u])
          (⟨some (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
            WeightedLevelColumnSave.initialControl,
            WeightedLevelColumnSave.initialBank i g W⟩ :
            TM2.Cfg (fun _ : WeightedLevelColumnSave.Stack => Bool) _ _) =
          ⟨none, WeightedLevelColumnSave.initialControl, X⟩ ∧
        X (WeightedLevelColumnSave.wcell 17) =
          MatrixWeightedEntryController.persistentBank d 17 ∧
        X (WeightedLevelColumnSave.wcell 27) =
          MatrixWeightedEntryController.persistentBank d 27 ∧
        X (WeightedLevelColumnSave.wcell 28) =
          MatrixWeightedEntryController.persistentBank d 28 ∧
        X (WeightedLevelColumnSave.wcell 21) =
          MatrixWeightedEntryController.persistentBank d 21 ∧
        X (WeightedLevelColumnSave.wcell 26) =
          MatrixWeightedEntryController.persistentBank d 26 ∧
        X (WeightedLevelColumnSave.wcell 29) =
          MatrixWeightedEntryController.persistentBank d 29 ∧
        X (WeightedLevelColumnSave.save 3) =
          List.replicate d.stagePrefixRows true ∧
        X (WeightedLevelColumnSave.save 0) =
          List.replicate (Iteration.a G c b y lvl M) true ∧
        X (WeightedLevelColumnSave.save 1) =
          List.replicate (Iteration.q₂ G c b y lvl M) true ∧
        X (WeightedLevelColumnSave.save 2) =
          List.replicate (Iteration.labels G c b y lvl M) true := by
  intro d i g s q a L W''
  obtain ⟨p17, p27, p28, p21, p26, p29, pst⟩ := persistent_fields G c b y lvl M
  obtain ⟨F, Q, P, hrest⟩ := WeightedLevelPublicClock.save_column_public i G W
    h17 h62 h27 h63 h28 h61 h7 h8 h9 h10 h11 h12 h13 h14 h15 h18
    h54 h55 h56 h57 h58 h60
  refine ⟨F, Q, P, ?_⟩
  obtain ⟨u, hu, hrun, o26, o29, o21, o28, o17, o27, s0, s1, s2, s3⟩ := hrest
  refine ⟨u, hu, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, s0, s1, s2⟩
  · exact o17.trans p17.symm
  · exact o27.trans p27.symm
  · exact o28.trans p28.symm
  · exact o21.trans p21.symm
  · exact o26.trans p26.symm
  · exact o29.trans p29.symm
  · rw [pst]; exact s3

#print axioms bank17
#print axioms bank27
#print axioms bank28
#print axioms bank21
#print axioms bank26
#print axioms bank29
#print axioms persistent_fields
#print axioms level_scalar_identity

end
end EthInapproximability.CurrentPaper.WeightedLevelIdentity
