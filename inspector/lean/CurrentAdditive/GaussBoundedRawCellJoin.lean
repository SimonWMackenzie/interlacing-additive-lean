import CurrentAdditive.GaussFixedArithmeticClock
import CurrentAdditive.GaussRequestBounded64

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace CurrentAdditive.GaussBoundedRawCellJoin
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext
open GaussFetchedArithmetic

noncomputable def lowBank (S : Bank → List Bool) : Fin 64 → List Bool :=
  fun i => S (lower i)

noncomputable def requestedBank (S : Bank → List Bool) (a : Nat) : Bank → List Bool :=
  BitMachineStackEmbedding.bank lower S
    (GaussFetchedAdaptedRequest.run a
      (GaussFetchedAdaptedRequest.initial (lowBank S))).stk

/-- One literal program fetches from the physical rational bank and executes
canonical exact arithmetic. This is not a supplied cell callback. -/
theorem physical_cell
    (S : Bank → List Bool) (matrix : List Bool) (flag : Bool)
    (current column row pivot : CodeDCodec.RawRat)
    (hc : current.Valid) (hcol : column.Valid) (hr : row.Valid) (hp : pivot.Valid)
    (hnum : 0 < EncodedCommunication.bitsValue pivot.numerator)
    (rowA rowB colJ colC sizeCap indexCap : Nat)
    (hS : ∀ j : Fin 64,(lowBank S j).length ≤ sizeCap)
    (hrowAN : rowA ≤ indexCap) (hrowBN : rowB ≤ indexCap)
    (hcolJN : colJ ≤ indexCap) (hcolCN : colC ≤ indexCap)
    (hmatrixN : matrix.length ≤ indexCap)
    (hcurrentN : (CodeDCodec.encodeRawRat current).length ≤ indexCap)
    (hcolumnN : (CodeDCodec.encodeRawRat column).length ≤ indexCap)
    (hrowN : (CodeDCodec.encodeRawRat row).length ≤ indexCap)
    (hpivotN : (CodeDCodec.encodeRawRat pivot).length ≤ indexCap)
    (hmat : lowBank S 8 = matrix)
    (hcurrent : GaussFetchFromBackups64.CellAt matrix rowA colJ
      (CodeDCodec.encodeRawRat current))
    (hcolumn : GaussFetchFromBackups64.CellAt matrix rowA colC
      (CodeDCodec.encodeRawRat column))
    (hrow : GaussFetchFromBackups64.CellAt matrix rowB colJ
      (CodeDCodec.encodeRawRat row))
    (hpivot : GaussFetchFromBackups64.CellAt matrix rowB colC
      (CodeDCodec.encodeRawRat pivot))
    (hrowA : lowBank S 17 = List.replicate rowA true)
    (hrowB : lowBank S 18 = List.replicate rowB true)
    (hcolJ : lowBank S 19 = List.replicate colJ true)
    (hcolC : lowBank S 20 = List.replicate colC true)
    (hflag : lowBank S 28 = [flag])
    (hempty : ∀ j : Fin 64, j.val < 7 → lowBank S j = [])
    (h21 : lowBank S 21 = []) (h22 : lowBank S 22 = [])
    (h23 : lowBank S 23 = []) (h24 : lowBank S 24 = [])
    (h25 : lowBank S 25 = []) (h26 : lowBank S 26 = [])
    (h27 : lowBank S 27 = []) (h63 : lowBank S 63 = [])
    (htarget : S slots.target = []) (hscratch : S slots.scratch = [])
    (hblank : ∀ i, S (slots.machine i) = []) :
    ∃ a t : Nat, ∃ S1 S2 S3 : Fin 64 → List Bool,
      a  ≤  GaussFourFetchEnvelope64.fourBound sizeCap indexCap +

        GaussAdaptPrepare64.time flag
          (CodeDCodec.encodeRawRat current) (CodeDCodec.encodeRawRat column) +
        2*(GaussFetchedAdaptedRequest.packet flag
          (CodeDCodec.encodeRawRat current) (CodeDCodec.encodeRawRat column)
          (CodeDCodec.encodeRawRat row) (CodeDCodec.encodeRawRat pivot)).length+4 ∧
      t  ≤  a + MachineInvokeFull.uniformBound M
        (GaussFetchedAdaptedRequest.packet flag
          (CodeDCodec.encodeRawRat current) (CodeDCodec.encodeRawRat column)
          (CodeDCodec.encodeRawRat row) (CodeDCodec.encodeRawRat pivot))
        (GaussFixedArithmeticClock.coefficient*((GaussFetchedAdaptedRequest.packet flag
          (CodeDCodec.encodeRawRat current) (CodeDCodec.encodeRawRat column)
          (CodeDCodec.encodeRawRat row) (CodeDCodec.encodeRawRat pivot)).length+1)^
          GaussUniformMatrixRun.exponent) + 1 ∧
      ((advance program)^[t])
        (⟨some start,control,S⟩ : TM2.Cfg (fun _ : Bank => Bool) Label Control) =
        ⟨none,control,Function.update (requestedBank S a) slots.target
          (CodeDCodec.encodeRawRat
            (GaussCellArithmeticTarget.cellRaw flag current column row pivot))⟩ ∧
      requestedBank S a (lower 8) = matrix ∧
      (∀ z : Fin 64, 7  ≤  z.val → z.val < 32 → z ≠ 15 → z ≠ 16 →
        z ≠ 21 → z ≠ 22 → z ≠ 23 → z ≠ 24 → z ≠ 25 →
        z ≠ 26 → z ≠ 27 → z ≠ 28 →
        requestedBank S a (lower z) = S (lower z)) := by
  obtain ⟨a,S1,S2,S3,ha,hh,hout,hmatout,hforeign⟩ :=
    GaussRequestBounded64.physical_request_bounded (lowBank S) matrix
      (CodeDCodec.encodeRawRat current) (CodeDCodec.encodeRawRat column)
      (CodeDCodec.encodeRawRat row) (CodeDCodec.encodeRawRat pivot)
      rowA rowB colJ colC sizeCap indexCap flag hS hrowAN hrowBN hcolJN hcolCN
      hmatrixN hcurrentN hcolumnN hrowN hpivotN hmat hcurrent hcolumn hrow hpivot
      hrowA hrowB hcolJ hcolC hflag hempty h21 h22 h23 h24 h25 h26 h27 h63
  let F := GaussFetchedAdaptedRequest.run a
    (GaussFetchedAdaptedRequest.initial (lowBank S))
  let R := requestedBank S a
  have hRlower (i : Fin 64) : R (lower i) = F.stk i :=
    BitMachineStackEmbedding.bank_at lower S F.stk i
  have hRsource : R slots.source = GaussFetchedAdaptedRequest.packet flag
      (CodeDCodec.encodeRawRat current) (CodeDCodec.encodeRawRat column)
      (CodeDCodec.encodeRawRat row) (CodeDCodec.encodeRawRat pivot) := by
    exact (hRlower 23).trans hout
  have hRprotected (z : Fin 64) (hzlo : 7  ≤  z.val) (hzhi : z.val < 32)
      (hz15 : z ≠ 15) (hz16 : z ≠ 16) (hz21 : z ≠ 21)
      (hz22 : z ≠ 22) (hz23 : z ≠ 23) (hz24 : z ≠ 24)
      (hz25 : z ≠ 25) (hz26 : z ≠ 26) (hz27 : z ≠ 27) (hz28 : z ≠ 28) :
      R (lower z) = S (lower z) :=
    (hRlower z).trans (hforeign z hzlo hzhi hz15 hz16 hz21 hz22 hz23 hz24 hz25 hz26 hz27 hz28)
  have hRtarget : R slots.target = [] :=
    (hRprotected 29 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans htarget
  have hRscratch : R slots.scratch = [] :=
    (hRprotected 30 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hscratch
  have hRblank (i : Fin M.stackCount) : R (slots.machine i) = [] := by
    have houtside : ¬ ∃ j, lower j = slots.machine i := by
      rintro ⟨j,h⟩
      have hv := congrArg Fin.val h
      change j.val=64+i.val at hv
      omega
    exact (BitMachineStackEmbedding.bank_outside lower S F.stk
      (slots.machine i) houtside).trans (hblank i)
  obtain ⟨b,hb,hinvoke⟩ := GaussFixedArithmeticClock.invoke_cell R flag
    current column row pivot hc hcol hr hp hnum hRsource hRtarget hRscratch hRblank
  obtain ⟨u,hu,hlift⟩ := BitMachineStackEmbedding.outputs lower S
    id id id (by intro x; rfl) none
    GaussFetchedAdaptedRequest.program requestProgram (by intro l; rfl)
    (GaussFetchedAdaptedRequest.initial (lowBank S)) a hh
  have hinit : BitMachineStackEmbedding.cfg lower S id id none
      (GaussFetchedAdaptedRequest.initial (lowBank S)) =
      (⟨some (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel GaussFetchedAdaptedRequest.fourStart)),
        ((GaussFetchedAdaptedRequest.fourControl,((),none)),none),S⟩ :
        TM2.Cfg (fun _ : Bank => Bool) GaussFetchedAdaptedRequest.Label
          GaussFetchedAdaptedRequest.Control) := by
    simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, GaussFetchedAdaptedRequest.initial, Option.map_some,
      id_eq, Option.or_none]
    congr 1
    exact BitMachineStackEmbedding.bank_restrict lower S
  have hfinal : BitMachineStackEmbedding.cfg lower S id id none F =
      (⟨none,F.var,R⟩ : TM2.Cfg (fun _ : Bank => Bool)
        GaussFetchedAdaptedRequest.Label GaussFetchedAdaptedRequest.Control) := by
    have hFl : F.l=none := hh
    simp only [BitMachineStackEmbedding.cfg,BitMachineStackEmbedding.stackCfg,BitMachineInline.cfg,hFl,id_eq]
    rfl
  rw [hinit,show ((advance GaussFetchedAdaptedRequest.program)^[a])
      (GaussFetchedAdaptedRequest.initial (lowBank S)) = F from rfl,
      hfinal] at hlift
  obtain ⟨t,ht,hfull⟩ := BitMachineRawSequence.runs requestProgram
    (MachineInvokeFull.program slots)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel GaussFetchedAdaptedRequest.fourStart))
    (MachineInvokeFull.start slots)
    ((GaussFetchedAdaptedRequest.fourControl,((),none)),none) F.var
    (MachineInvokeFull.control slots) (MachineInvokeFull.control slots)
    S R (Function.update R slots.target
      (CodeDCodec.encodeRawRat (GaussCellArithmeticTarget.cellRaw flag current column row pivot)))
    u b hlift hinvoke
  dsimp only [GaussFixedArithmeticClock.inputPacket] at hb
  refine ⟨a,t,S1,S2,S3,ha,by omega,?_,?_,hRprotected⟩
  · simpa only [program,start,GaussFetchedArithmetic.control] using hfull
  · exact (hRlower 8).trans hmatout

#print axioms physical_cell
end CurrentAdditive.GaussBoundedRawCellJoin
