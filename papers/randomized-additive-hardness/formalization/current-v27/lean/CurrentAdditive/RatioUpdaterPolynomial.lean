import CurrentAdditive.RatioMappedListPolynomial

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 100
noncomputable section
namespace CurrentAdditive.RatioUpdaterPolynomial
open EthInapproximability.CurrentPaper EntryClockPoly
open RatioUpdaterItemPolynomial RatioMappedListPolynomial

theorem compact_cap_poly : PolyIn (fun n : Nat => n)
    (fun n => CodeDCompactClockV2.polynomialClock n n) := by
  unfold CodeDCompactClockV2.polynomialClock CodeDCompactClockV2.inputBound
    CodeDCompactClockV2.bodyResultBound CodeDCompactClockV2.headerResultBound
    CodeDCompactClockV2.headerClockBound CodeDCompactClockV2.bodyClockBound
    CodeDCompactClockV2.bodyListBound CodeDCompactClockV2.bodyOutputBound
    CodeDCompactClockV2.itemEnvelope CodeDCompactClockV2.itemTime CodeDCompactClockV2.itemOutput
    CodeDCompactClockV2.zeroOutputBound CodeDCompactClockV2.keepFlagClockBound
    CodeDCompactClockV2.keepMarkedBound CodeDCompactClockV2.keepMarkedOutputBound
  solve_update_poly

theorem compact_clock_poly :
    PolyIn (fun xs => (SourceListEncoding.encode xs).length) CodeDCompactJoinV2.clock := by
  have hpoint : ∀ xs,CodeDCompactJoinV2.clock xs ≤
      CodeDCompactClockV2.polynomialClock (SourceListEncoding.encode xs).length
        (SourceListEncoding.encode xs).length := by
    intro xs
    have h := CodeDCompactClockV2.clock_le_polynomial xs
      (SourceListEncoding.encode xs).length
      (fun x hx => RatioListClockBounds.word_le_packet xs x hx)
    have hn := GaussRowCount.rows_le_input xs
    apply h.trans
    unfold CodeDCompactClockV2.polynomialClock CodeDCompactClockV2.inputBound
      CodeDCompactClockV2.bodyResultBound CodeDCompactClockV2.headerResultBound
      CodeDCompactClockV2.headerClockBound CodeDCompactClockV2.bodyClockBound
      CodeDCompactClockV2.bodyListBound CodeDCompactClockV2.bodyOutputBound
      CodeDCompactClockV2.itemEnvelope CodeDCompactClockV2.itemTime CodeDCompactClockV2.itemOutput
      CodeDCompactClockV2.zeroOutputBound CodeDCompactClockV2.keepFlagClockBound
      CodeDCompactClockV2.keepMarkedBound CodeDCompactClockV2.keepMarkedOutputBound
      CodeDZeroListClockV2.polynomialClock CodeDZeroListClockV2.itemEnvelope CodeDZeroListClockV2.framedTime
    unfold CodeDCompactClockV2.inputBound
    gcongr
  exact PolyIn.mono hpoint (compact_cap_poly.comap
    (fun xs => (SourceListEncoding.encode xs).length) (fun _ => le_rfl))

/-- The actual three-stage arithmetic/rewrite/zero-removal clock has one
uniform polynomial in the length of its original ordered request packet.
All intermediate encoded lengths are charged by physical output growth. -/
theorem uniform_update_clock : ∃ C d : Nat,
    ∀ {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ) (lambda : ℚ),
      CodeDUpdateFullPipeline.clock source coeff lambda ≤
        C*((CodeDUpdateRequestABI.requestPacketList source coeff lambda).length+1)^d := by
  obtain ⟨C1,d1,h1⟩ := arithmetic_list_poly
  obtain ⟨C2,d2,h2⟩ := entry_list_poly
  obtain ⟨C3,d3,h3⟩ := compact_clock_poly
  let t1 (n : Nat) := C1*(n+1)^d1
  let pcap (n : Nat) := n+t1 n*CodeDUpdateFinalPairList.machine.pushBound
  let t2 (n : Nat) := C2*(pcap n+1)^d2
  let ecap (n : Nat) := pcap n+t2 n*CodeDUpdatedEntryList.machine.pushBound
  let cap (n : Nat) := t1 n+2*pcap n+2+t2 n+2*ecap n+2+C3*(ecap n+1)^d3
  have hp : PolyIn (fun n : Nat => n) cap := by
    dsimp only [cap,ecap,t2,pcap,t1]
    solve_update_poly
  obtain ⟨C,d,hC⟩ := hp
  refine ⟨C,d,?_⟩
  intro q source coeff lambda
  let L := (CodeDUpdateRequestABI.requestPacketList source coeff lambda).length
  let updated := CodeDUpdatedArithmeticABI.candidateWeights source coeff lambda
  let pairs := CodeDUpdatedEntryList.pairItems source updated
  let entries := (CodeDCompactSequentialBridge.updatedEntries source updated).map CodeDSourceCodecV2.encodeEntry
  have ht1 : CodeDUpdateFinalPairList.clock
      (CodeDUpdateRequestABI.requestItems source coeff lambda) ≤ t1 L := h1 _
  have hpairs : (CodeDCodecV2.encodeItems pairs).length ≤ pcap L := by
    have ho := BitMachine.output_length_bound CodeDUpdateFinalPairList.machine
      (CodeDUpdateFinalPairList.writes_pairItems source coeff lambda)
    have hm := Nat.mul_le_mul_right CodeDUpdateFinalPairList.machine.pushBound ht1
    dsimp only [pcap]
    dsimp only [L,updated,pairs] at *
    omega
  have ht2 : CodeDUpdatedEntryList.clock pairs ≤ t2 L := by
    apply (h2 pairs).trans
    dsimp only [t2]
    gcongr
    exact hpairs
  have hentries : (CodeDCodecV2.encodeItems entries).length ≤ ecap L := by
    have ho := BitMachine.output_length_bound CodeDUpdatedEntryList.machine
      (CodeDUpdatedEntryList.writes_compactor_input source updated)
    have hm := Nat.mul_le_mul_right CodeDUpdatedEntryList.machine.pushBound ht2
    dsimp only [ecap]
    dsimp only [pairs,entries] at *
    omega
  have ht3 : CodeDCompactJoinV2.clock entries ≤ C3*(ecap L+1)^d3 := by
    apply (h3 entries).trans
    gcongr
    exact hentries
  apply (show CodeDUpdateFullPipeline.clock source coeff lambda ≤ cap L from ?_).trans (hC L)
  unfold CodeDUpdateFullPipeline.clock CodeDUpdatedCompactPipeline.clock
  change CodeDUpdateFinalPairList.clock (CodeDUpdateRequestABI.requestItems source coeff lambda)+
    2*(CodeDCodecV2.encodeItems pairs).length+2+
      (CodeDUpdatedEntryList.clock pairs+2*(CodeDCodecV2.encodeItems entries).length+2+
        CodeDCompactJoinV2.clock entries) ≤ cap L
  dsimp only [cap]
  omega

#print axioms compact_clock_poly
#print axioms uniform_update_clock
end CurrentAdditive.RatioUpdaterPolynomial
