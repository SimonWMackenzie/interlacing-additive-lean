import CurrentAdditive.GaussReusableRawCell
import CurrentAdditive.GaussBoundedRawCellJoin

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace CurrentAdditive.GaussReusableRawCellBounded
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext GaussFetchedArithmetic
open GaussReusableRawCell

noncomputable def boundedRequestLimit {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot i : Fin m) (c j : Fin k) (sizeCap indexCap : Nat) : Nat :=
  let ri:=GaussCellSourceBridge.sourceRow r pivot i
  let cur:=CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B ri j))
  let col:=CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B ri c))
  let row:=CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B pivot j))
  let pv:=CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B pivot c))
  GaussFourFetchEnvelope64.fourBound (sizeCap+indexCap+1) indexCap +
    GaussAdaptPrepare64.time (decide (i=r)) cur col +
    2*(GaussFetchedAdaptedRequest.packet (decide (i=r)) cur col row pv).length+4
theorem physical_cell_bounded {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot i : Fin m) (c j : Fin k)
    (hn : B pivot c ≠ 0) (S : Bank → List Bool)
    (sizeCap indexCap : Nat)
    (hSize : ∀ z : Fin 64,(S (lower z)).length ≤ sizeCap)
    (hmCap : m ≤ indexCap) (hkCap : k ≤ indexCap)
    (hMatrixCap : (GaussPhysical.encodeTypedMatrix B).length ≤ indexCap)
    (hCellCap : ∀ u v,(CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B u v))).length ≤ indexCap)
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
      a  ≤  boundedRequestLimit B r pivot i c j sizeCap indexCap ∧
      t  ≤  totalLimit B r pivot i c j S a ∧
      ((advance GaussReusableRawCell.program)^[t])
        (⟨some GaussReusableRawCell.start,GaussReusableRawCell.control,S⟩ : TM2.Cfg (fun _ : Bank => Bool) GaussReusableRawCell.Label GaussReusableRawCell.Control) =
        ⟨none,GaussReusableRawCell.control,Function.update S slots.target
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
  have hTsize (z : Fin 64) : (GaussBoundedRawCellJoin.lowBank T z).length ≤ sizeCap+indexCap+1 := by
    have hs:=hSize z
    have hrile:=ri.isLt
    have hpile:=pivot.isLt
    change (T (lower z)).length ≤ _
    rw [hT]
    split_ifs <;> (try simp only [List.length_replicate,List.length_singleton]) <;> omega
  obtain ⟨a,t,S1,S2,S3,ha,ht,hraw,hm,hforeign⟩ :=
    GaussBoundedRawCellJoin.physical_cell T (GaussPhysical.encodeTypedMatrix B) flag
      current column row pv
      (GaussPhysical.rawOfRat_valid _) (GaussPhysical.rawOfRat_valid _)
      (GaussPhysical.rawOfRat_valid _) (GaussPhysical.rawOfRat_valid _) hnum
      ri.val pivot.val j.val c.val (sizeCap+indexCap+1) indexCap hTsize
      (by have:=ri.isLt;omega) (by have:=pivot.isLt;omega)
      (by have:=j.isLt;omega) (by have:=c.isLt;omega)
      hMatrixCap (hCellCap ri j) (hCellCap ri c) (hCellCap pivot j) (hCellCap pivot c) hmat
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
  let R := GaussBoundedRawCellJoin.requestedBank T a
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
    have hz : 7 ≤ z.val ∧ z.val<32 ∧ z≠15 ∧ z≠16 ∧ z≠21 ∧ z≠22 ∧
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
  change u ≤ t+GaussCellScratchReset.clock
    (Function.update (GaussRawCellJoin.requestedBank T a) slots.target answer)+1 at hu
  dsimp only [totalLimit,GaussFixedArithmeticClock.inputPacket]
  dsimp only [ri,current,column,row,pv,flag,T,R,answer] at ht hu
  change n  ≤  _
  omega

#print axioms physical_cell_bounded
end CurrentAdditive.GaussReusableRawCellBounded
