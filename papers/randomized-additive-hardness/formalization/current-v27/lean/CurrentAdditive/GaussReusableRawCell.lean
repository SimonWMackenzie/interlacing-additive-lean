import CurrentAdditive.GaussRawCellJoin
import CurrentAdditive.GaussSwapAddresses64
import CurrentAdditive.GaussTypedCellAddress
import CurrentAdditive.GaussCellScratchReset

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace CurrentAdditive.GaussReusableRawCell
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext GaussFetchedArithmetic

def addressProgram (l : GaussSwapAddresses64.CompleteLabel) :=
  BitMachineStackEmbedding.stmt lower id id id none
    (GaussSwapAddresses64.completeProgram l)

noncomputable def tailProgram := BitMachineRawSequence.program
  GaussFetchedArithmetic.program GaussCellScratchReset.program
  (.clear 0) GaussFetchedArithmetic.control ((),none)

noncomputable def program := BitMachineRawSequence.program addressProgram tailProgram
  (BitMachineRawSequence.leftLabel GaussFetchedArithmetic.start)
  GaussSwapAddresses64.completeControl
  (GaussFetchedArithmetic.control,((),none))

abbrev Label := BitMachineRawSequence.Label GaussSwapAddresses64.CompleteLabel
  (BitMachineRawSequence.Label GaussFetchedArithmetic.Label GaussCellScratchReset.Label)
abbrev Control := BitMachineRawSequence.Control GaussSwapAddresses64.CompleteControl
  (BitMachineRawSequence.Control GaussFetchedArithmetic.Control GaussCellScratchReset.Control)

noncomputable def start : Label :=
  BitMachineRawSequence.leftLabel GaussSwapAddresses64.completeStart
noncomputable def control : Control :=
  (GaussSwapAddresses64.completeControl,(GaussFetchedArithmetic.control,((),none)))

noncomputable def addressBank (S : Bank → List Bool) (i r pivot : Nat) :=
  Function.update
    (Function.update
      (Function.update (Function.update S (lower 28) [decide (i=r)])
        (lower 31) [decide (i=pivot)])
      (lower 17) (List.replicate (GaussSwapAddresses64.source i r pivot) true))
    (lower 18) (List.replicate pivot true)

/-- The physical swap-address selection in the same ambient bank as the
actual arithmetic call. -/
theorem addresses_run (S : Bank → List Bool) (i r pivot : Nat)
    (h7 : S (lower 7) = List.replicate i true)
    (h9 : S (lower 9) = List.replicate r true)
    (h10 : S (lower 10) = List.replicate pivot true)
    (hclean : ∀ z : Fin 64, ¬GaussCellScratchReset.retained z → S (lower z)=[]) :
    ∃ t ≤ (2*i+2*r+max i r+10)+(2*i+2*pivot+max i pivot+10)+
      2*GaussSwapAddresses64.source i r pivot+2*pivot+10, ∃ v,
      ((advance addressProgram)^[t])
        (⟨some GaussSwapAddresses64.completeStart,
          GaussSwapAddresses64.completeControl,S⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none,v,addressBank S i r pivot⟩ := by
  have hb (z : Fin 64) (hz : ¬GaussCellScratchReset.retained z) :
      GaussRawCellJoin.lowBank S z=[] := hclean z hz
  obtain ⟨a,ha,v,hrun⟩ := GaussSwapAddresses64.physical_addresses
    (GaussRawCellJoin.lowBank S) i r pivot h7 h9 h10
    (hb 15 (by decide)) (hb 16 (by decide)) (hb 17 (by decide))
    (hb 18 (by decide)) (hb 28 (by decide)) (hb 31 (by decide)) (hb 63 (by decide))
  have hh := congrArg (fun c => c.l) hrun
  change _=none at hh
  obtain ⟨u,hu,he⟩ := BitMachineStackEmbedding.outputs lower S
    id id id (by intro x; rfl) none
    GaussSwapAddresses64.completeProgram addressProgram (by intro l; rfl)
    (⟨some GaussSwapAddresses64.completeStart,GaussSwapAddresses64.completeControl,
      GaussRawCellJoin.lowBank S⟩ : TM2.Cfg (fun _ : Fin 64 => Bool) _ _) a hh
  rw [hrun] at he
  simp only [BitMachineStackEmbedding.cfg,BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg,id_eq] at he
  have hi : BitMachineStackEmbedding.bank lower S (GaussRawCellJoin.lowBank S)=S :=
    BitMachineStackEmbedding.bank_restrict lower S
  rw [hi] at he
  simp only [BitMachineStackEmbedding.bank_update] at he
  rw [hi] at he
  exact ⟨u,hu.trans ha,v,he⟩


noncomputable def requestLimit {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot i : Fin m) (c j : Fin k) (S : Bank → List Bool)
    (S1 S2 S3 : Fin 64 → List Bool) : Nat :=
  let ri:=GaussCellSourceBridge.sourceRow r pivot i
  let cur:=CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B ri j))
  let col:=CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B ri c))
  let row:=CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B pivot j))
  let pv:=CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B pivot c))
  GaussFourOperands64.fourClock
    (GaussRawCellJoin.lowBank (addressBank S i.val r.val pivot.val)) S1 S2 S3
    (GaussPhysical.encodeTypedMatrix B) cur col row pv ri.val pivot.val j.val c.val +
    GaussAdaptPrepare64.time (decide (i=r)) cur col +
    2*(GaussFetchedAdaptedRequest.packet (decide (i=r)) cur col row pv).length+4

noncomputable def totalLimit {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot i : Fin m) (c j : Fin k) (S : Bank → List Bool) (a : Nat) : Nat :=
  let ri:=GaussCellSourceBridge.sourceRow r pivot i
  let packet:=GaussFixedArithmeticClock.inputPacket (decide (i=r))
    (GaussPhysical.rawOfRat (B ri j)) (GaussPhysical.rawOfRat (B ri c))
    (GaussPhysical.rawOfRat (B pivot j)) (GaussPhysical.rawOfRat (B pivot c))
  let answer:=CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat
    (SequentialTotality.clearTyped (SequentialTotality.swapTyped B r pivot) r c i j))
  (2*i.val+2*r.val+max i.val r.val+10)+
    (2*i.val+2*pivot.val+max i.val pivot.val+10)+
    2*GaussSwapAddresses64.source i.val r.val pivot.val+2*pivot.val+10+
    a+MachineInvokeFull.uniformBound M packet
      (GaussFixedArithmeticClock.coefficient*(packet.length+1)^GaussUniformMatrixRun.exponent)+
    GaussCellScratchReset.clock
      (Function.update (GaussRawCellJoin.requestedBank
        (addressBank S i.val r.val pivot.val) a) slots.target answer)+3
/-- The complete cell worker restores every fixed bank and both original
unary addresses. The only changed stack is the canonical rational answer29.
It executes physical address selection, four getters, exact arithmetic and
charged scratch cleanup. -/
theorem physical_cell {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot i : Fin m) (c j : Fin k)
    (hn : B pivot c ≠ 0) (S : Bank → List Bool)
    (h7 : S (lower 7)=List.replicate i.val true)
    (h8 : S (lower 8)=GaussPhysical.encodeTypedMatrix B)
    (h9 : S (lower 9)=List.replicate r.val true)
    (h10 : S (lower 10)=List.replicate pivot.val true)
    (h19 : S (lower 19)=List.replicate j.val true)
    (h20 : S (lower 20)=List.replicate c.val true)
    (h29 : S slots.target=[])
    (h30 : S slots.scratch=[])
    (hclean : ∀ z : Fin 64, ¬GaussCellScratchReset.retained z → S (lower z)=[])
    (hblank : ∀ z, S (slots.machine z)=[]) :
    ∃ a t : Nat, ∃ S1 S2 S3 : Fin 64 → List Bool,
      a ≤ requestLimit B r pivot i c j S S1 S2 S3 ∧
      t ≤ totalLimit B r pivot i c j S a ∧
      ((advance program)^[t])
        (⟨some start,control,S⟩ : TM2.Cfg (fun _ : Bank => Bool) Label Control) =
        ⟨none,control,Function.update S slots.target
          (CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat
            (SequentialTotality.clearTyped
              (SequentialTotality.swapTyped B r pivot) r c i j)))⟩ := by
  let ri := GaussCellSourceBridge.sourceRow r pivot i
  let current := GaussPhysical.rawOfRat (B ri j)
  let column := GaussPhysical.rawOfRat (B ri c)
  let row := GaussPhysical.rawOfRat (B pivot j)
  let pv := GaussPhysical.rawOfRat (B pivot c)
  let flag := decide (i=r)
  let T := addressBank S i.val r.val pivot.val
  have hT (z : Fin 64) : T (lower z) =
      if z=18 then List.replicate pivot.val true else
      if z=17 then List.replicate ri.val true else
      if z=31 then [decide (i=pivot)] else
      if z=28 then [flag] else S (lower z) := by
    have hs := GaussSwapAddresses64.source_eq_swap i r pivot
    have hir : (i.val=r.val) ↔ i=r := Fin.val_inj
    have hip : (i.val=pivot.val) ↔ i=pivot := Fin.val_inj
    have hz18 : (z.val=18) ↔ z=(18 : Fin 64) := by
      constructor
      · intro he; exact Fin.ext (by simpa using he)
      · intro he; simpa using congrArg (fun x : Fin 64 => x.val) he
    have hz17 : (z.val=17) ↔ z=(17 : Fin 64) := by
      constructor
      · intro he; exact Fin.ext (by simpa using he)
      · intro he; simpa using congrArg (fun x : Fin 64 => x.val) he
    have hz31 : (z.val=31) ↔ z=(31 : Fin 64) := by
      constructor
      · intro he; exact Fin.ext (by simpa using he)
      · intro he; simpa using congrArg (fun x : Fin 64 => x.val) he
    have hz28 : (z.val=28) ↔ z=(28 : Fin 64) := by
      constructor
      · intro he; exact Fin.ext (by simpa using he)
      · intro he; simpa using congrArg (fun x : Fin 64 => x.val) he
    simp [T,addressBank,lower,ri,flag,hs,hir,hip,Function.update_apply,hz18,hz17,hz31,hz28]
  have hTclean (z : Fin 64) (hz : z≠17 ∧ z≠18 ∧ z≠28 ∧ z≠31)
      (hp : ¬GaussCellScratchReset.retained z) : T (lower z)=[] := by
    rw [hT]
    simp [hz.1,hz.2.1,hz.2.2.1,hz.2.2.2,hclean z hp]
  have hTforeign (z : Bank) (hz : ¬ ∃ a : Fin 64,lower a=z) : T z=S z := by
    have hne (a : Fin 64) : z≠lower a := fun h => hz ⟨a,h.symm⟩
    simp [T,addressBank,hne]
  have hTblank (z : Fin M.stackCount) : T (slots.machine z)=[] := by
    have hz : ¬∃ a : Fin 64,lower a=slots.machine z := by
      rintro ⟨a,ha⟩; have hv:=congrArg Fin.val ha
      change a.val=64+z.val at hv; omega
    exact (hTforeign _ hz).trans (hblank z)
  have hnum : 0 < EncodedCommunication.bitsValue pv.numerator := by
    apply GaussPhysical.numerator_positive_of_nonzero_value
    simpa [pv,GaussPhysical.rawOfRat_value] using hn
  have hmat : GaussRawCellJoin.lowBank T 8=GaussPhysical.encodeTypedMatrix B := by
    simpa [GaussRawCellJoin.lowBank,hT] using h8
  have hempty (z : Fin 64) (hz : z.val<7) : GaussRawCellJoin.lowBank T z=[] := by
    apply hTclean z
    · constructor
      · intro he; have := congrArg Fin.val he; omega
      · constructor
        · intro he; have := congrArg Fin.val he; omega
        · constructor <;> intro he <;> have := congrArg Fin.val he <;> omega
    · simp only [GaussCellScratchReset.retained]; omega
  have hb (z : Fin 64) (hz : z≠17 ∧ z≠18 ∧ z≠28 ∧ z≠31)
      (hp : ¬GaussCellScratchReset.retained z) : GaussRawCellJoin.lowBank T z=[] :=
    hTclean z hz hp
  have htarget : T slots.target=[] := by
    change T (lower 29)=[]; rw [hT]; simpa using h29
  have hscratch : T slots.scratch=[] := by
    change T (lower 30)=[]; rw [hT]; simpa using h30
  obtain ⟨a,t,S1,S2,S3,ha,ht,hraw,hm,hforeign⟩ :=
    GaussRawCellJoin.physical_cell T (GaussPhysical.encodeTypedMatrix B) flag
      current column row pv
      (GaussPhysical.rawOfRat_valid _) (GaussPhysical.rawOfRat_valid _)
      (GaussPhysical.rawOfRat_valid _) (GaussPhysical.rawOfRat_valid _) hnum
      ri.val pivot.val j.val c.val hmat
      (GaussTypedCellAddress.cell_at B ri j) (GaussTypedCellAddress.cell_at B ri c)
      (GaussTypedCellAddress.cell_at B pivot j) (GaussTypedCellAddress.cell_at B pivot c)
      (by change T (lower 17)=_; simp [hT])
      (by change T (lower 18)=_; simp [hT])
      (by change T (lower 19)=_; simpa [hT] using h19)
      (by change T (lower 20)=_; simpa [hT] using h20)
      (by change T (lower 28)=_; simp [hT]) hempty
      (hb 21 (by decide) (by decide)) (hb 22 (by decide) (by decide))
      (hb 23 (by decide) (by decide)) (hb 24 (by decide) (by decide))
      (hb 25 (by decide) (by decide)) (hb 26 (by decide) (by decide))
      (hb 27 (by decide) (by decide)) (hb 63 (by decide) (by decide))
      htarget hscratch hTblank
  let R := GaussRawCellJoin.requestedBank T a
  let answer := CodeDCodec.encodeRawRat
    (GaussPhysical.rawOfRat (SequentialTotality.clearTyped
      (SequentialTotality.swapTyped B r pivot) r c i j))
  have hanswer : CodeDCodec.encodeRawRat
      (GaussCellArithmeticTarget.cellRaw flag current column row pv)=answer := by
    have h := GaussCellArithmeticTarget.sourceCellPacket_target B r pivot c i j
    rw [GaussSwapIndexSpec.sourceRow_current] at h
    exact congrArg CodeDCodec.encodeRawRat h
  rw [hanswer] at hraw
  have hRkeep (z : Fin 64) (hp : GaussCellScratchReset.retained z) :
      R (lower z)=S (lower z) := by
    have hz : 7≤z.val ∧ z.val<32 ∧ z≠15 ∧ z≠16 ∧ z≠21 ∧ z≠22 ∧
        z≠23 ∧ z≠24 ∧ z≠25 ∧ z≠26 ∧ z≠27 ∧ z≠28 := by
      fin_cases z <;> simp [GaussCellScratchReset.retained] at hp ⊢
    rcases hz with ⟨hlo,hhi,h15,h16,h21,h22,h23,h24,h25,h26,h27,h28⟩
    have hpersist := hforeign z hlo hhi h15 h16 h21 h22 h23 h24 h25 h26 h27 h28
    have hTs : T (lower z)=S (lower z) := by
      rw [hT]
      fin_cases z <;> simp [GaussCellScratchReset.retained] at hp ⊢
    exact hpersist.trans hTs
  have hRforeign (z : Bank) (hz : ¬∃ i : Fin 64,lower i=z) : R z=S z :=
    (BitMachineStackEmbedding.bank_outside lower T _ z hz).trans (hTforeign z hz)
  have hrestore := GaussCellScratchReset.restore_eq S R answer hclean hRkeep hRforeign
  have hreset := GaussCellScratchReset.physical_reset (Function.update R slots.target answer)
  rw [hrestore] at hreset
  obtain ⟨u,hu,htail⟩ := BitMachineRawSequence.runs
    GaussFetchedArithmetic.program GaussCellScratchReset.program
    GaussFetchedArithmetic.start (.clear 0)
    GaussFetchedArithmetic.control GaussFetchedArithmetic.control ((),none) ((),none)
    T (Function.update R slots.target answer) (Function.update S slots.target answer)
    t (GaussCellScratchReset.clock (Function.update R slots.target answer)) hraw hreset
  obtain ⟨v,hv,vcontrol,haddress⟩ := addresses_run S i.val r.val pivot.val h7 h9 h10 hclean
  obtain ⟨n,hn,hfull⟩ := BitMachineRawSequence.runs addressProgram tailProgram
    GaussSwapAddresses64.completeStart
    (BitMachineRawSequence.leftLabel GaussFetchedArithmetic.start)
    GaussSwapAddresses64.completeControl vcontrol
    (GaussFetchedArithmetic.control,((),none)) (GaussFetchedArithmetic.control,((),none))
    S T (Function.update S slots.target answer) v u haddress htail
  refine ⟨a,n,S1,S2,S3,ha,?_,hfull⟩
  dsimp only [totalLimit,GaussFixedArithmeticClock.inputPacket]
  dsimp only [ri,current,column,row,pv,flag,T,R,answer] at ht hu
  change n ≤ _
  omega

#print axioms addresses_run
#print axioms physical_cell
end CurrentAdditive.GaussReusableRawCell
