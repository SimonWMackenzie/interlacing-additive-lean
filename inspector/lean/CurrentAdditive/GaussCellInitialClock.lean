import CurrentAdditive.GaussFramedCell
import CurrentAdditive.GaussRequestGrowth64

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace CurrentAdditive.GaussCellInitialClock
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext GaussFetchedArithmetic

noncomputable def packet {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot i : Fin m) (c j : Fin k) :=
  GaussFixedArithmeticClock.inputPacket (decide (i=r))
    (GaussPhysical.rawOfRat (B (GaussCellSourceBridge.sourceRow r pivot i) j))
    (GaussPhysical.rawOfRat (B (GaussCellSourceBridge.sourceRow r pivot i) c))
    (GaussPhysical.rawOfRat (B pivot j)) (GaussPhysical.rawOfRat (B pivot c))

def packetCap (n : Nat) : Nat := 32*(n+1)+54
noncomputable def requestCap (s n : Nat) : Nat :=
  GaussFourFetchEnvelope64.fourBound (s+n+1) n+(2*n+5)+2*packetCap n+4
noncomputable def arithmeticCap (n : Nat) : Nat :=
  GaussFixedArithmeticClock.coefficient*(packetCap n+1)^GaussUniformMatrixRun.exponent
noncomputable def invocationCap (n : Nat) : Nat :=
  MachineInvokeFull.uniformBound M (List.replicate (packetCap n) true) (arithmeticCap n)
noncomputable def answerCap (n : Nat) : Nat := packetCap n+arithmeticCap n*M.pushBound
noncomputable def rawCap (s n : Nat) : Nat :=
  (14*n+30)+requestCap s n+invocationCap n+
    (52*(s+n+1+requestCap s n*GaussRequestGrowth64.requestPush)+54)+3
noncomputable def framedCap (s n : Nat) : Nat :=
  rawCap s n+4*answerCap n+
    V2FieldContext.clock (List.replicate (answerCap n) true)+10

theorem packet_length_le {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot i : Fin m) (c j : Fin k) (n : Nat)
    (hentry : ∀ u v,(CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B u v))).length ≤ n) :
    (packet B r pivot i c j).length ≤ packetCap n := by
  unfold packet
  rw [GaussFixedArithmeticClock.packet_eq]
  apply GaussUniformCellClock.adapted_packet_length _ _ _ _ _ (n+1) (by omega)
  · have h:=hentry (GaussCellSourceBridge.sourceRow r pivot i) j; omega
  · have h:=hentry (GaussCellSourceBridge.sourceRow r pivot i) c; omega
  · have h:=hentry pivot j; omega
  · have h:=hentry pivot c; omega

theorem request_length_clock {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot i : Fin m) (c j : Fin k) (s n : Nat)
    (hentry : ∀ u v,(CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B u v))).length ≤ n) :
    GaussReusableRawCellBounded.boundedRequestLimit B r pivot i c j s n ≤ requestCap s n := by
  have hpacket:=packet_length_le B r pivot i c j n hentry
  have htime : GaussAdaptPrepare64.time (decide (i=r))
      (CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat
        (B (GaussCellSourceBridge.sourceRow r pivot i) j)))
      (CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat
        (B (GaussCellSourceBridge.sourceRow r pivot i) c))) ≤ 2*n+5 := by
    have hcur:=hentry (GaussCellSourceBridge.sourceRow r pivot i) j
    have hcol:=hentry (GaussCellSourceBridge.sourceRow r pivot i) c
    unfold GaussAdaptPrepare64.time
    split_ifs <;> omega
  change GaussFourFetchEnvelope64.fourBound (s+n+1) n+_+2*(packet B r pivot i c j).length+4 ≤ _
  unfold requestCap
  omega

theorem invocation_le (bits : List Bool) (n : Nat) (h : bits.length ≤ packetCap n) :
    MachineInvokeFull.uniformBound M bits
      (GaussFixedArithmeticClock.coefficient*(bits.length+1)^GaussUniformMatrixRun.exponent) ≤
      invocationCap n := by
  unfold invocationCap arithmeticCap MachineInvokeFull.uniformBound
  simp only [List.length_replicate]
  gcongr

theorem prepared_size (S : Bank → List Bool) (i r pivot s n : Nat)
    (hS : ∀ z : Fin 64,(S (lower z)).length ≤ s)
    (hi : i ≤ n) (hr : r ≤ n) (hp : pivot ≤ n) :
    ∀ z : Fin 64,
      (GaussRawCellJoin.lowBank (GaussReusableRawCell.addressBank S i r pivot) z).length ≤ s+n+1 := by
  have hsource : GaussSwapAddresses64.source i r pivot ≤ n := by
    unfold GaussSwapAddresses64.source
    split_ifs <;> assumption
  intro z
  have hz:=hS z
  simp only [GaussRawCellJoin.lowBank,GaussReusableRawCell.addressBank,Function.update_apply]
  split_ifs <;> (try simp only [List.length_replicate,List.length_singleton]) <;> omega

theorem cleanup_requested (S : Bank → List Bool) (a s : Nat)
    (hS : ∀ z : Fin 64,(S (lower z)).length ≤ s) (answer : List Bool) :
    GaussCellScratchReset.clock
      (Function.update (GaussRawCellJoin.requestedBank S a) slots.target answer) ≤
      52*(s+a*GaussRequestGrowth64.requestPush)+54 := by
  have hbound (i : Fin 52) :
      (Function.update (GaussRawCellJoin.requestedBank S a) slots.target answer
        (GaussCellScratchReset.resetBank i)).length ≤ s+a*GaussRequestGrowth64.requestPush := by
    have hne : GaussCellScratchReset.resetBank i≠slots.target := by
      intro he
      have hm : ∃ j,GaussCellScratchReset.resetBank j=lower 29 := ⟨i,he⟩
      exact ((GaussCellScratchReset.reset_range 29).1 hm) (by decide)
    rw [Function.update_of_ne hne]
    obtain ⟨z,hz⟩:=GaussCellScratchReset.reset_lower i
    rw [← hz]
    rw [GaussRawCellJoin.requestedBank,BitMachineStackEmbedding.bank_at]
    change ((GaussFetchedAdaptedRequest.run a
      (GaussFetchedAdaptedRequest.initial (GaussRawCellJoin.lowBank S))).stk z).length ≤ _
    exact GaussRequestGrowth64.stack_growth (GaussRawCellJoin.lowBank S) a s hS z
  have hsum:=Finset.sum_le_sum (s:=(Finset.univ : Finset (Fin 52))) (fun i _ => hbound i)
  unfold GaussCellScratchReset.clock
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.nsmul_eq_mul] using Nat.add_le_add_right hsum 54

theorem totalLimit_le {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot i : Fin m) (c j : Fin k) (S : Bank → List Bool) (s n a : Nat)
    (hS : ∀ z : Fin 64,(S (lower z)).length ≤ s)
    (hm : m ≤ n)
    (hentry : ∀ u v,(CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B u v))).length ≤ n)
    (ha : a ≤ GaussReusableRawCellBounded.boundedRequestLimit B r pivot i c j s n) :
    GaussReusableRawCell.totalLimit B r pivot i c j S a ≤ rawCap s n := by
  have hi : i.val ≤ n := (Nat.le_of_lt i.isLt).trans hm
  have hr : r.val ≤ n := (Nat.le_of_lt r.isLt).trans hm
  have hp : pivot.val ≤ n := (Nat.le_of_lt pivot.isLt).trans hm
  have hsource : GaussSwapAddresses64.source i.val r.val pivot.val ≤ n := by
    rw [GaussSwapAddresses64.source_eq_swap]
    exact (Nat.le_of_lt (GaussCellSourceBridge.sourceRow r pivot i).isLt).trans hm
  have hmaxr : max i.val r.val ≤ n := max_le hi hr
  have hmaxp : max i.val pivot.val ≤ n := max_le hi hp
  have haddr : (2*i.val+2*r.val+max i.val r.val+10)+
      (2*i.val+2*pivot.val+max i.val pivot.val+10)+
      2*GaussSwapAddresses64.source i.val r.val pivot.val+2*pivot.val+10 ≤ 14*n+30 := by omega
  have haq:=ha.trans (request_length_clock B r pivot i c j s n hentry)
  have hpacket:=packet_length_le B r pivot i c j n hentry
  have hinvoke:=invocation_le (packet B r pivot i c j) n hpacket
  have hprepared:=prepared_size S i.val r.val pivot.val s n hS hi hr hp
  have hcleanup:=cleanup_requested
    (GaussReusableRawCell.addressBank S i.val r.val pivot.val) a (s+n+1) hprepared
    (GaussFramedCell.answer B r pivot i c j)
  have hamul:=Nat.mul_le_mul_right GaussRequestGrowth64.requestPush haq
  change _+a+MachineInvokeFull.uniformBound M (packet B r pivot i c j)
    (GaussFixedArithmeticClock.coefficient*((packet B r pivot i c j).length+1)^GaussUniformMatrixRun.exponent)+
    GaussCellScratchReset.clock
      (Function.update (GaussRawCellJoin.requestedBank
        (GaussReusableRawCell.addressBank S i.val r.val pivot.val) a) slots.target
        (GaussFramedCell.answer B r pivot i c j))+3 ≤ _
  unfold rawCap
  omega

theorem answer_length_le {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot i : Fin m) (c j : Fin k) (hn : B pivot c≠0) (n : Nat)
    (hentry : ∀ u v,(CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B u v))).length ≤ n) :
    (GaussFramedCell.answer B r pivot i c j).length ≤ answerCap n := by
  have hnum : 0 < EncodedCommunication.bitsValue (GaussPhysical.rawOfRat (B pivot c)).numerator := by
    apply GaussPhysical.numerator_positive_of_nonzero_value
    simpa only [GaussPhysical.rawOfRat_value] using hn
  have htarget:=GaussCellArithmeticTarget.sourceCellPacket_target B r pivot c i j
  rw [GaussSwapIndexSpec.sourceRow_current] at htarget
  have hOut:=GaussFixedArithmeticClock.outputs_cell (decide (i=r))
    (GaussPhysical.rawOfRat (B (GaussCellSourceBridge.sourceRow r pivot i) j))
    (GaussPhysical.rawOfRat (B (GaussCellSourceBridge.sourceRow r pivot i) c))
    (GaussPhysical.rawOfRat (B pivot j)) (GaussPhysical.rawOfRat (B pivot c))
    (GaussPhysical.rawOfRat_valid _) (GaussPhysical.rawOfRat_valid _)
    (GaussPhysical.rawOfRat_valid _) (GaussPhysical.rawOfRat_valid _) hnum
  rw [htarget] at hOut
  have hlen:=BitMachine.output_length_bound M hOut
  change (GaussFramedCell.answer B r pivot i c j).length ≤
    (packet B r pivot i c j).length+
    (GaussFixedArithmeticClock.coefficient*((packet B r pivot i c j).length+1)^
      GaussUniformMatrixRun.exponent)*M.pushBound at hlen
  have hpacket:=packet_length_le B r pivot i c j n hentry
  apply hlen.trans
  unfold answerCap arithmeticCap
  gcongr

theorem frame_clock_le (bits : List Bool) (n : Nat) (h : bits.length ≤ answerCap n) :
    V2FieldContext.clock bits ≤ V2FieldContext.clock (List.replicate (answerCap n) true) := by
  unfold V2FieldContext.clock MachineInvokeFull.uniformBound
  simp only [List.length_replicate]
  gcongr

/-- One fixed physical framed-cell program, with a bound computed entirely from
initial bank and matrix size limits. No final or intermediate bank-size premise
is used. Its whole-bank output still restores all persistent and working stacks. -/
theorem physical_cell {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot i : Fin m) (c j : Fin k) (hn : B pivot c≠0)
    (S : GaussCellFieldFrame.Bank → List Bool) (sizeCap indexCap : Nat)
    (hSize : ∀ z : Fin 64,(S (GaussCellFieldFrame.loc z)).length ≤ sizeCap)
    (hmCap : m ≤ indexCap) (hkCap : k ≤ indexCap)
    (hMatrixCap : (GaussPhysical.encodeTypedMatrix B).length ≤ indexCap)
    (hCellCap : ∀ u v,(CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B u v))).length ≤ indexCap)
    (h7 : S (GaussCellFieldFrame.loc 7)=List.replicate i.val true)
    (h8 : S (GaussCellFieldFrame.loc 8)=GaussPhysical.encodeTypedMatrix B)
    (h9 : S (GaussCellFieldFrame.loc 9)=List.replicate r.val true)
    (h10 : S (GaussCellFieldFrame.loc 10)=List.replicate pivot.val true)
    (h19 : S (GaussCellFieldFrame.loc 19)=List.replicate j.val true)
    (h20 : S (GaussCellFieldFrame.loc 20)=List.replicate c.val true)
    (h29 : S (GaussCellFieldFrame.loc 29)=[]) (h30 : S (GaussCellFieldFrame.loc 30)=[])
    (hclean : ∀ z : Fin 64, ¬GaussCellScratchReset.retained z → S (GaussCellFieldFrame.loc z)=[])
    (harith : ∀ z,S (GaussCellFieldFrame.old (GaussFetchedArithmetic.slots.machine z))=[])
    (hframe : ∀ z : Fin 10,S (GaussCellFieldFrame.fresh z)=[]) :
    ∃ t ≤ framedCap sizeCap indexCap,
      ((advance GaussFramedCell.program)^[t])
        (⟨some GaussFramedCell.start,GaussFramedCell.control,S⟩ :
          TM2.Cfg (fun _ : GaussCellFieldFrame.Bank => Bool) GaussFramedCell.Label GaussFramedCell.Control) =
        ⟨none,GaussFramedCell.control,Function.update S (GaussCellFieldFrame.loc 29)
          (V2FieldContext.field (GaussFramedCell.answer B r pivot i c j))⟩ := by
  obtain ⟨a,t,S1,S2,S3,ha,ht,hrun⟩:=GaussFramedCell.physical_cell B r pivot i c j hn S
    sizeCap indexCap hSize hmCap hkCap hMatrixCap hCellCap
    h7 h8 h9 h10 h19 h20 h29 h30 hclean harith hframe
  have hraw:=totalLimit_le B r pivot i c j (GaussFramedCell.rawBank S)
    sizeCap indexCap a hSize hmCap hCellCap ha
  have hans:=answer_length_le B r pivot i c j hn indexCap hCellCap
  have hfr:=frame_clock_le (GaussFramedCell.answer B r pivot i c j) indexCap hans
  exact ⟨t,by unfold framedCap; omega,hrun⟩

#print axioms packet_length_le
#print axioms cleanup_requested
#print axioms totalLimit_le
#print axioms answer_length_le
#print axioms physical_cell
end CurrentAdditive.GaussCellInitialClock
