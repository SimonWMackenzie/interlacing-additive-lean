import Paper2.FrontPreparedCut
import Paper2.ClearAll
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps

/-! Lane a-bridge-owner-1, segment 1. Private copy (new module name, new
namespace `Paper2.ABridge`) of the frozen Codex matrix-output lane's
`lifted_program_frame` (FrameFields.lean), `publicFields`/`exit_public_fields`
(FrontPublic.lean) and `prep_preserves_packet`/`prepared_packet_run`
(PreparedPacketCells.lean, SHA-256 53D4F223...7F65), with proofs unchanged and
imports re-pointed at the root-replayed `Paper2.FrontPreparedCut`; then the
compiled and repaired candidate `RepackPrefix` (SHA-256 80E23646...B733) and its
charged composition with the prepared packet run. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.ABridge

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding

theorem lifted_program_frame {K J L V : Type*}
    [DecidableEq K] [DecidableEq J]
    (ι : K ↪ J) (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (H : J → List Bool) (l : Option L) (v : V) (t : Nat)
    (z : J) (hz : z ∉ Set.range ι) :
    (((advance (fun a => stackStmt ι (P a)))^[t])
      (⟨l, v, H⟩ : TM2.Cfg (fun _ : J => Bool) L V)).stk z = H z := by
  let S : K → List Bool := fun x => H (ι x)
  have hstart : bank ι H S = H := bank_eq_self ι H S (fun _ => rfl)
  have h := BitMachineStackRun.run ι H P
    (⟨l, v, S⟩ : TM2.Cfg (fun _ : K => Bool) L V) t
  simp only [stackCfg] at h
  rw [hstart] at h
  rw [h]
  exact bank_outside ι H _ z hz

def publicFields (a b Δ : Nat) (g : EncodedGraph.Graph) (k : Nat)
    (H : FullFront.JF → List Bool) : Prop :=
  H (FullFront.jt (TMFront.mc 13)) =
      List.replicate (FrontPreparedCut.frontMX a b Δ g k) true ∧
  H (FullFront.jt (TMFront.mc 10)) =
      List.replicate (FrontPreparedCut.frontMY a b Δ g k) true ∧
  H (FullFront.jt (TMFront.tc ThrProducer.thrC)) =
      List.replicate (FullFront.bV a b Δ g k) true

theorem exit_public_fields (a b Δ : Nat) (g : EncodedGraph.Graph)
    (hg : g.Valid) (k : Nat) (word : List Bool)
    (FL : CountFront.LK → List Bool) (FQ : CountFront.QK → List Bool)
    (FT : TMFront.TK → List Bool) (FM : TMFront.MK → List Bool)
    (hT : TMFront.TFacts k (FullFront.vT a b Δ g) FT)
    (hM : TMFront.MFacts (FullFront.bV a b Δ g k) k
      (FullFront.Lg g) FM) :
    publicFields a b Δ g k
      (FullFront.exitBank a b Δ g hg k word FL FQ FT FM) := by
  rcases hT with ⟨hthr, _⟩
  rcases hM with
    ⟨_, _, _, _, _, _, _, _, _, _, h10, _, _, h13, _, _, _, _⟩
  constructor
  · simpa only [publicFields, FullFront.exitBank, FullFront.exitBankG,
      FullFront.jt, TMFront.mc, FrontPreparedCut.frontMX,
      FullFront.mXV, FullFront.Zv, FullFront.bV,
      TMFront.MFacts, MProducer.u] using h13
  constructor
  · simpa only [publicFields, FullFront.exitBank, FullFront.exitBankG,
      FullFront.jt, TMFront.mc, FrontPreparedCut.frontMY,
      FullFront.mYV, FullFront.Zv, FullFront.bV,
      MProducer.u] using h10
  · simpa only [publicFields, FullFront.exitBank, FullFront.exitBankG,
      FullFront.jt, TMFront.tc, FullFront.bV, FullFront.vT,
      TMFront.thrVal, ThrProducer.u] using hthr

theorem prep_preserves_packet (H : FullFront.JF → List Bool)
    (l : Option _) (v : _) (t : Nat) (i : Fin 3) :
    (((advance FrontPreparedCut.prepProgram)^[t])
      (⟨l, v, H⟩ : TM2.Cfg (fun _ : FullFront.JF => Bool) _ _)).stk
      (FullFront.pk i) = H (FullFront.pk i) := by
  apply lifted_program_frame FrontPreparedCut.prepSlots
    SamplerParameterJoin.preparedCleanupProgram H l v t
  rintro ⟨x, hx⟩
  cases x <;> cases hx

/-- The first two packet fields remain literal while the third field has
been cut physically in the consumer region. The original packet word is not
mistaken for the selected tape. -/
theorem prepared_packet_run (a b Δ : Nat) (g : EncodedGraph.Graph)
    (hg : g.Valid) (k : Nat) (word : List Bool) :
    ∃ t ≤ FullFront.fullBd a b Δ g k word +
      FrontPreparedCut.prepBd g.vertices (FullFront.pV g) (FullFront.sV g)
        (FullFront.q1V g) (FullFront.q2V g) (FullFront.wV g)
        (FullFront.QV a b Δ g) k
        (FrontPreparedCut.frontMX a b Δ g k)
        (FrontPreparedCut.frontMY a b Δ g k) word + 1,
      ∃ H : FullFront.JF → List Bool,
        ((advance (FrontPreparedCut.fullPrepProgram a b Δ))^[t])
          (⟨some (BitMachineRawSequence.leftLabel (FullFront.fullStart a b Δ)),
            (FullFront.fullCtl,
              (((SamplerParameterJoin.startControl, (false, false)), (none, ())), ((), none))),
            FullFront.F0 (FullFront.X0 g k word)⟩ :
            TM2.Cfg (fun _ : FullFront.JF => Bool) _ _) =
          ⟨none,
            (FullFront.fullCtl,
              (((SamplerParameterJoin.finalControl, (false, false)), (none, ())), ((), none))), H⟩ ∧
        H (FullFront.pk 0) = EncodedGraph.encode g ∧
        H (FullFront.pk 1) = List.replicate k true ∧
        H (FrontPreparedCut.prepSlots (.inl (SamplerParameterBank.drawCell 0))) =
          word.take (FrontPreparedCut.frontD a b Δ g k) ∧
        H (FullFront.zs) = [] ∧
        H (FullFront.pk 2) = word ∧
        publicFields a b Δ g k H := by
  obtain ⟨tf, htf, vc, FL, FQ, FT, FM, hf, _, _, hT, hM⟩ :=
    FullFront.full_run a b Δ g hg k word
  let E := FullFront.exitBank a b Δ g hg k word FL FQ FT FM
  have hpubE : publicFields a b Δ g k E :=
    exit_public_fields a b Δ g hg k word FL FQ FT FM hT hM
  obtain ⟨tp, htp, H, hp, hcons⟩ :=
    FrontPreparedCut.lift_run g hg k word FL FQ FT FM g.vertices
      (FullFront.pV g) (FullFront.sV g) (FullFront.q1V g)
      (FullFront.q2V g) (FullFront.wV g) (FullFront.QV a b Δ g)
      (FrontPreparedCut.frontMX a b Δ g k)
      (FrontPreparedCut.frontMY a b Δ g k)
  have hframe (z : FullFront.JF) (hz : z ∉ Set.range FrontPreparedCut.prepSlots) :
      H z = E z := by
    have hp' : ((advance FrontPreparedCut.prepProgram)^[tp])
        (⟨some (.inl (.inl (.inl SamplerParameterJoin.startLabel))),
          (((SamplerParameterJoin.startControl, (false, false)), (none, ())), ((), none)), E⟩ :
          TM2.Cfg (fun _ : FullFront.JF => Bool) _ _) =
        ⟨none, (((SamplerParameterJoin.finalControl, (false, false)), (none, ())), ((), none)), H⟩ := hp
    have h := lifted_program_frame FrontPreparedCut.prepSlots
      SamplerParameterJoin.preparedCleanupProgram E
      (some (.inl (.inl (.inl SamplerParameterJoin.startLabel))))
      (((SamplerParameterJoin.startControl, (false, false)), (none, ())), ((), none))
      tp z hz
    change (((advance FrontPreparedCut.prepProgram)^[tp])
      (⟨some (.inl (.inl (.inl SamplerParameterJoin.startLabel))),
        (((SamplerParameterJoin.startControl, (false, false)), (none, ())), ((), none)), E⟩ :
        TM2.Cfg (fun _ : FullFront.JF => Bool) _ _)).stk z = _ at h
    rw [hp'] at h
    exact h
  have hpk (i : Fin 3) : H (FullFront.pk i) = FullFront.X0 g k word i := by
    rw [hframe (FullFront.pk i) (by rintro ⟨x, hx⟩; cases x <;> cases hx)]
    rfl
  have hpubH : publicFields a b Δ g k H := by
    rcases hpubE with ⟨hr, hc, ht⟩
    exact ⟨(hframe _ (by rintro ⟨x, hx⟩; cases x <;> cases hx)).trans hr,
      (hframe _ (by rintro ⟨x, hx⟩; cases x <;> cases hx)).trans hc,
      (hframe _ (by rintro ⟨x, hx⟩; cases x <;> cases hx)).trans ht⟩
  have hf' : ((advance (FullFront.full a b Δ))^[tf])
      (⟨some (FullFront.fullStart a b Δ), FullFront.fullCtl,
        FullFront.F0 (FullFront.X0 g k word)⟩ :
        TM2.Cfg (fun _ : FullFront.JF => Bool) _ _) =
      ⟨none, vc, E⟩ := hf
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs
    (FullFront.full a b Δ) FrontPreparedCut.prepProgram
    (FullFront.fullStart a b Δ)
    (.inl (.inl (.inl SamplerParameterJoin.startLabel)))
    FullFront.fullCtl vc
    (((SamplerParameterJoin.startControl, (false, false)), (none, ())), ((), none))
    (((SamplerParameterJoin.finalControl, (false, false)), (none, ())), ((), none))
    (FullFront.F0 (FullFront.X0 g k word)) E H tf tp hf' hp
  refine ⟨t, by omega, H, hrun, ?_, ?_, ?_, ?_, ?_, hpubH⟩
  · simpa only [FullFront.X0] using hpk 0
  · simpa only [FullFront.X0] using hpk 1
  · simpa only [FrontPreparedCut.frontD, FrontPreparedCut.frontMX,
      FrontPreparedCut.frontMY] using
      (hcons (SamplerParameterBank.drawCell 0)).trans
        (SamplerParameterBank.initial_tape _ _ _ _ _ _ _ _ _ _ _ _ _)
  · rw [hframe FullFront.zs (by rintro ⟨x, hx⟩; cases x <;> cases hx)]
    rfl
  · simpa only [FullFront.X0] using hpk 2

#print axioms prep_preserves_packet
#print axioms prepared_packet_run

/-! ### Repack (repaired candidate of `RepackPrefix.lean`) -/

open EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps

def prefixCell : FullFront.JF :=
  FrontPreparedCut.prepSlots (.inl (SamplerParameterBank.drawCell 0))

def clearCell : Fin 1 → FullFront.JF := fun _ => FullFront.pk 2

theorem prefixCell_ne_pk (i : Fin 3) : prefixCell ≠ FullFront.pk i := by
  simp [prefixCell, FrontPreparedCut.prepSlots, FullFront.pk]

theorem prefixCell_ne_zs : prefixCell ≠ FullFront.zs := by
  simp [prefixCell, FrontPreparedCut.prepSlots, FullFront.zs]

theorem pk_ne_zs (i : Fin 3) : FullFront.pk i ≠ FullFront.zs := by
  simp [FullFront.pk, FullFront.zs]

def copySlots : Fin 3 ↪ FullFront.JF :=
  FullFront.mkE prefixCell (FullFront.pk 2) FullFront.zs
    (prefixCell_ne_pk 2) prefixCell_ne_zs (pk_ne_zs 2)

def repackProgram :=
  BitMachineRawSequence.program (ClearAll.prog clearCell)
    (copyProgram copySlots) BitMachineCopy.Label.scan
    (none : Option Bool) (none : Option Bool)

theorem clear_at (H : FullFront.JF → List Bool) :
    ClearAll.clearFrom clearCell 0 H = Function.update H (FullFront.pk 2) [] := by
  funext z
  by_cases hz : z = FullFront.pk 2
  · subst z
    simp [ClearAll.clearFrom, clearCell]
  · simp [ClearAll.clearFrom, clearCell, hz, Function.update_of_ne hz]
    intro h
    exact absurd h.symm hz

/-- One local controller physically replaces `pk 2` by the prefix already
produced at the consumer draw cell: it pops every bit of the old tape and then
copies the prefix. The exit bank is stated exactly. -/
theorem repack_run (H : FullFront.JF → List Bool)
    (word pre : List Bool)
    (hraw : H (FullFront.pk 2) = word)
    (hprefix : H prefixCell = pre)
    (hscratch : H FullFront.zs = []) :
    ∃ t ≤ 1 * (word.length + 1) + 1 + (2 * pre.length + 2) + 1,
      ∃ v,
        ((advance repackProgram)^[t])
          (⟨some (BitMachineRawSequence.leftLabel (⟨0, by omega⟩ : Fin 2)),
            ((none : Option Bool), (none : Option Bool)), H⟩ :
            TM2.Cfg (fun _ : FullFront.JF => Bool) _ _) =
          ⟨none, v, Function.update H (FullFront.pk 2) pre⟩ := by
  obtain ⟨tc, htc, vc, hc⟩ := ClearAll.all_run clearCell
    (by intro i j _; exact Subsingleton.elim i j)
    word.length H (by intro i; simp [clearCell, hraw]) none
  let C := ClearAll.clearFrom clearCell 0 H
  have hC : C = Function.update H (FullFront.pk 2) [] := clear_at H
  have hsrc : C (copySlots 0) = pre := by
    change C prefixCell = pre
    rw [hC, Function.update_of_ne (prefixCell_ne_pk 2)]
    exact hprefix
  have hdst : C (copySlots 1) = [] := by
    change C (FullFront.pk 2) = []
    simp [hC]
  have hscr : C (copySlots 2) = [] := by
    change C FullFront.zs = []
    rw [hC, Function.update_of_ne (pk_ne_zs 2).symm]
    exact hscratch
  have hcopy := copy_run copySlots C hscr
  rw [hsrc, hdst, List.append_nil] at hcopy
  have hF : Function.update C (copySlots 1) pre = Function.update H (FullFront.pk 2) pre := by
    change Function.update C (FullFront.pk 2) pre = _
    rw [hC, Function.update_idem]
  rw [hF] at hcopy
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (ClearAll.prog clearCell) (copyProgram copySlots)
    (⟨0, by omega⟩ : Fin 2) BitMachineCopy.Label.scan
    (none : Option Bool) vc (none : Option Bool) (none : Option Bool)
    H C (Function.update H (FullFront.pk 2) pre) tc (2 * pre.length + 2) hc hcopy
  exact ⟨t, by omega, _, hr⟩

#print axioms repack_run

/-! ### Segment 1: one charged run from the raw three-cell packet -/

def packetProgram (a b Δ : ℕ) :=
  BitMachineRawSequence.program (FrontPreparedCut.fullPrepProgram a b Δ) repackProgram
    (BitMachineRawSequence.leftLabel (⟨0, by omega⟩ : Fin 2))
    (FullFront.fullCtl,
      (((SamplerParameterJoin.startControl, (false, false)), (none, ())), ((), none)))
    ((none : Option Bool), (none : Option Bool))

/-- **Segment 1.** From the literal start bank `F0 ![encode g, 1^k, word]`,
ONE fixed controller (graph-byte front, public-count preparation and exact
prefix cut, then the charged pop/copy repack) halts with `pk 0 = encode g`,
`pk 1 = 1^k`, `pk 2 = word.take (frontD a b Δ g k)`; the exit bank is the
prepared bank `H` with only `pk 2` replaced. Every stage and handoff is in the
stated clock. -/
theorem packet_repack_run (a b Δ : Nat) (g : EncodedGraph.Graph)
    (hg : g.Valid) (k : Nat) (word : List Bool) :
    ∃ t ≤ FullFront.fullBd a b Δ g k word +
      FrontPreparedCut.prepBd g.vertices (FullFront.pV g) (FullFront.sV g)
        (FullFront.q1V g) (FullFront.q2V g) (FullFront.wV g)
        (FullFront.QV a b Δ g) k
        (FrontPreparedCut.frontMX a b Δ g k)
        (FrontPreparedCut.frontMY a b Δ g k) word + 1 +
      (word.length + 2 * (word.take (FrontPreparedCut.frontD a b Δ g k)).length + 5) + 1,
      ∃ v, ∃ H : FullFront.JF → List Bool,
        ((advance (packetProgram a b Δ))^[t])
          (⟨some (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel (FullFront.fullStart a b Δ))),
            ((FullFront.fullCtl,
              (((SamplerParameterJoin.startControl, (false, false)), (none, ())), ((), none))),
              ((none : Option Bool), (none : Option Bool))), FullFront.F0 (FullFront.X0 g k word)⟩ :
            TM2.Cfg (fun _ : FullFront.JF => Bool) _ _) =
          ⟨none, v, Function.update H (FullFront.pk 2)
            (word.take (FrontPreparedCut.frontD a b Δ g k))⟩ ∧
        H (FullFront.pk 0) = EncodedGraph.encode g ∧
        H (FullFront.pk 1) = List.replicate k true ∧
        H prefixCell = word.take (FrontPreparedCut.frontD a b Δ g k) ∧
        H FullFront.zs = [] ∧
        H (FullFront.pk 2) = word ∧
        publicFields a b Δ g k H := by
  obtain ⟨tp, htp, H, hp, h0, h1, hpre, hz, h2, hpub⟩ :=
    prepared_packet_run a b Δ g hg k word
  obtain ⟨tr, htr, vr, hr⟩ := repack_run H word
    (word.take (FrontPreparedCut.frontD a b Δ g k)) h2 hpre hz
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs
    (FrontPreparedCut.fullPrepProgram a b Δ) repackProgram
    (BitMachineRawSequence.leftLabel (FullFront.fullStart a b Δ))
    (BitMachineRawSequence.leftLabel (⟨0, by omega⟩ : Fin 2))
    (FullFront.fullCtl,
      (((SamplerParameterJoin.startControl, (false, false)), (none, ())), ((), none)))
    (FullFront.fullCtl,
      (((SamplerParameterJoin.finalControl, (false, false)), (none, ())), ((), none)))
    ((none : Option Bool), (none : Option Bool)) vr
    (FullFront.F0 (FullFront.X0 g k word)) H _ tp tr hp hr
  exact ⟨t, by omega, _, H, hrun, h0, h1, hpre, hz, h2, hpub⟩

#print axioms packet_repack_run

end

end Paper2.ABridge
