import CurrentAdditive.GaussCellFieldFrame
import CurrentAdditive.GaussReusableRawCellBounded

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace CurrentAdditive.GaussFramedCell
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GaussCellFieldFrame

noncomputable def rawBank (S : Bank → List Bool) : GaussFetchedArithmetic.Bank → List Bool :=
  fun i => S (old i)

noncomputable def rawProgram (l : GaussReusableRawCell.Label) :=
  BitMachineStackEmbedding.stmt old id id id none (GaussReusableRawCell.program l)

noncomputable def program := BitMachineRawSequence.program rawProgram
  GaussCellFieldFrame.program GaussCellFieldFrame.start
  GaussReusableRawCell.control GaussCellFieldFrame.control

abbrev Label := BitMachineRawSequence.Label GaussReusableRawCell.Label GaussCellFieldFrame.Label
abbrev Control := BitMachineRawSequence.Control GaussReusableRawCell.Control GaussCellFieldFrame.Control
noncomputable def start : Label := BitMachineRawSequence.leftLabel GaussReusableRawCell.start
noncomputable def control : Control := (GaussReusableRawCell.control,GaussCellFieldFrame.control)

def answer {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot i : Fin m) (c j : Fin k) : List Bool :=
  CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat
    (SequentialTotality.clearTyped (SequentialTotality.swapTyped B r pivot) r c i j))

/-- A concrete cell subprogram for the actual inner grid: output29 is the
V2 length field followed by the entire canonical rational cell. Both unary
addresses and every persistent/scratch stack are restored exactly. -/
theorem physical_cell {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot i : Fin m) (c j : Fin k) (hn : B pivot c≠0)
    (S : Bank → List Bool) (sizeCap indexCap : Nat)
    (hSize : ∀ z : Fin 64,(S (loc z)).length ≤ sizeCap)
    (hmCap : m ≤ indexCap) (hkCap : k ≤ indexCap)
    (hMatrixCap : (GaussPhysical.encodeTypedMatrix B).length ≤ indexCap)
    (hCellCap : ∀ u v,(CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B u v))).length ≤ indexCap)
    (h7 : S (loc 7)=List.replicate i.val true)
    (h8 : S (loc 8)=GaussPhysical.encodeTypedMatrix B)
    (h9 : S (loc 9)=List.replicate r.val true)
    (h10 : S (loc 10)=List.replicate pivot.val true)
    (h19 : S (loc 19)=List.replicate j.val true)
    (h20 : S (loc 20)=List.replicate c.val true)
    (h29 : S (loc 29)=[]) (h30 : S (loc 30)=[])
    (hclean : ∀ z : Fin 64, ¬GaussCellScratchReset.retained z → S (loc z)=[])
    (harith : ∀ z,S (old (GaussFetchedArithmetic.slots.machine z))=[])
    (hframe : ∀ z : Fin 10,S (fresh z)=[]) :
    ∃ a t : Nat, ∃ S1 S2 S3 : Fin 64 → List Bool,
      a ≤ GaussReusableRawCellBounded.boundedRequestLimit B r pivot i c j sizeCap indexCap ∧
      t ≤ GaussReusableRawCell.totalLimit B r pivot i c j (rawBank S) a +
        4*(answer B r pivot i c j).length+V2FieldContext.clock (answer B r pivot i c j)+10 ∧
      ((advance program)^[t])
        (⟨some start,control,S⟩ : TM2.Cfg (fun _ : Bank => Bool) Label Control) =
        ⟨none,control,Function.update S (loc 29)
          (V2FieldContext.field (answer B r pivot i c j))⟩ := by
  let R := rawBank S
  let word := answer B r pivot i c j
  obtain ⟨a,t,S1,S2,S3,ha,ht,hraw⟩ :=
    GaussReusableRawCellBounded.physical_cell_bounded B r pivot i c j hn R
      sizeCap indexCap hSize hmCap hkCap hMatrixCap hCellCap
      h7 h8 h9 h10 h19 h20 h29 h30 hclean harith
  have hh := congrArg (fun c => c.l) hraw
  change _=none at hh
  obtain ⟨u,hu,he⟩ := BitMachineStackEmbedding.outputs old S id id id
    (by intro x; rfl) none GaussReusableRawCell.program rawProgram
    (by intro l; rfl)
    (⟨some GaussReusableRawCell.start,GaussReusableRawCell.control,R⟩ :
      TM2.Cfg (fun _ : GaussFetchedArithmetic.Bank => Bool) _ _) t hh
  rw [hraw] at he
  simp only [BitMachineStackEmbedding.cfg,BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg,id_eq] at he
  have hbank : BitMachineStackEmbedding.bank old S R=S :=
    BitMachineStackEmbedding.bank_restrict old S
  rw [hbank,BitMachineStackEmbedding.bank_update,hbank] at he
  let T:=Function.update S (loc 29) word
  have h29T : T (loc 29)=word := by simp [T]
  have h28T : T (loc 28)=[] := by
    have hne : loc 28≠loc 29 := by
      intro h; have hv:=congrArg (fun z : Bank => z.val) h
      change (28 : Nat)=29 at hv; omega
    exact (Function.update_of_ne hne word S).trans (hclean 28 (by decide))
  have hframeT (z : Fin 10) : T (fresh z)=[] := by
    have hne : fresh z≠loc 29 := by
      intro h; have hv:=congrArg (fun z : Bank => z.val) h
      dsimp [fresh,loc,old,GaussFetchedArithmetic.lower] at hv
      omega
    exact (Function.update_of_ne hne word S).trans (hframe z)
  obtain ⟨b,hb,hframeRun⟩ := GaussCellFieldFrame.physical_frame T word h29T h28T hframeT
  have hfinal : Function.update T (loc 29) (V2FieldContext.field word)=
      Function.update S (loc 29) (V2FieldContext.field word) :=
    by simp only [T,Function.update_idem]
  rw [hfinal] at hframeRun
  obtain ⟨n,hn,hfull⟩ := BitMachineRawSequence.runs rawProgram GaussCellFieldFrame.program
    GaussReusableRawCell.start GaussCellFieldFrame.start
    GaussReusableRawCell.control GaussReusableRawCell.control
    GaussCellFieldFrame.control GaussCellFieldFrame.control
    S T (Function.update S (loc 29) (V2FieldContext.field word)) u b he hframeRun
  dsimp only [R] at ht
  dsimp only [word] at hb
  exact ⟨a,n,S1,S2,S3,ha,by omega,hfull⟩

#print axioms physical_cell
end CurrentAdditive.GaussFramedCell
