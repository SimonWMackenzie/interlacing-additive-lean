import EthInapproximability.CurrentPaper.ActualRoundParts
import EthInapproximability.CurrentPaper.EntryClockPoly3LevelJ

/-! Rebase the existing concrete level-j writer-22 clock onto its *actual*
instance, graph-stream and incoming-word sizes. The source-p conversion is
proved separately; no coarse one-level envelope is used. -/

noncomputable section

namespace EthInapproximability.CurrentPaper.ActualWriterClock

open EntryClockPoly ActualCountClock
open EntryClockPoly3 (LI sI)
open EthInapproximability.ParameterizedNP.GuardedSourceGraph

set_option maxHeartbeats 3000000

def instJ (i : LI) : PI :=
  ⟨EntryClockPoly.instL i.G i.c i.b i.y i.lv i.M,
    EntryClockPoly.instL_pos i.G i.c i.b i.y i.lv i.M⟩

def graphJ (i : LI) : GI :=
  ⟨i.V, i.E, i.G, sI i⟩

def JEnv (i : LI) : ℕ :=
  A i + (instJ i).1.U + UG (graphJ i) +
    (MatrixMaterialization.rowMajor i.M.entry).length

theorem rest_poly : PolyIn JEnv (fun i => restI (instJ i).1) :=
  PolyIn.comap instJ (fun i => by unfold JEnv; omega) restI_poly

theorem graph_poly : PolyIn JEnv (fun i => bvG (graphJ i)) :=
  PolyIn.comap graphJ (fun i => by unfold JEnv; omega) bvG_poly

theorem boundV_poly : PolyIn JEnv
    (fun i => EntryPrepVecJ.boundV_j i.G i.c i.b i.y i.lv i.M) :=
  PolyIn.mono
    (fun i => EntryClockPoly3.boundV_j_le i.G i.c i.b i.y i.lv i.M)
    graph_poly

theorem word_poly : PolyIn JEnv
    (fun i => (MatrixMaterialization.rowMajor i.M.entry).length) :=
  PolyIn.of_le fun i => by unfold JEnv; omega

/-- The literal writer-22 clock, excluding its supplied family fuel, is a
uniform polynomial of actual counts. -/
theorem writer_extra_poly : PolyIn JEnv
    (fun i => EntryWriter22J.writerBound_j i.G i.c i.b i.y i.lv i.M 0) := by
  have h2w := PolyIn.mul (PolyIn.const (2 : ℕ)) word_poly
  have hfirst : PolyIn JEnv
      (fun i => ((2 * (MatrixMaterialization.rowMajor i.M.entry).length + 2) + 0) + 1) := by
    simpa only [Nat.add_zero] using
      (PolyIn.add (PolyIn.add h2w (PolyIn.const (2 : ℕ))) (PolyIn.const (1 : ℕ)))
  have hrest := rest_poly
  have hbv := boundV_poly
  have hs := PolyIn.add (PolyIn.add hfirst hrest) hbv
  have h7 : PolyIn JEnv
      (fun i => (((2 * (MatrixMaterialization.rowMajor i.M.entry).length + 2) + 0) + 1) +
        restI (instJ i).1 + EntryPrepVecJ.boundV_j i.G i.c i.b i.y i.lv i.M + 0 + 7) := by
    simpa only [Nat.add_zero] using (PolyIn.add hs (PolyIn.const (7 : ℕ)))
  exact PolyIn.mono (fun i => le_of_eq
    (EntryClockPoly3.writerBound_j_split i.G i.c i.b i.y i.lv i.M 0)) h7

private theorem from_clog {x p : ℕ} (h : Nat.clog 2 x ≤ p) : x ≤ 2 ^ p :=
  (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) _).trans
    (Nat.pow_le_pow_right (by decide) h)

theorem instance_source_bound (i : LI) (p : ℕ)
    (h : ActualOrderFromCarrier.SourceNames i p) :
    (instJ i).1.U ≤ 20 * (2 ^ p) ^ 2 * (EntryClockPoly3.ell3 i.G + 1) := by
  let P := 2 ^ p
  let X := EntryClockPoly3.ell3 i.G + 1
  have hP : 1 ≤ P := by dsimp [P]; exact Nat.one_le_pow _ _ (by decide)
  have hP2 : P ≤ P ^ 2 := by nlinarith
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hs : sI i ≤ P := from_clog h.binsDescription
  have hrx : EntryClockPoly3.rxI i ≤ P := from_clog h.inputRows
  have hV : Fintype.card i.V ≤ EntryClockPoly3.ell3 i.G := by
    have h := EntryClockPoly3.card_le_ell3 i.G
    omega
  have hL :=
    (ActualCarrierBounds.level_large_counts_of_raw_carriers i p h.rawRows h.rawCols).1
  have hcol : MatrixStage4Codes.cols (EntryClockPoly3.aI i) (sI i)
      (EntryClockPoly3.qI i) (EntryClockPoly3.cyI i) ≤ P := by
    have hc := from_clog h.rawCols
    rw [(ActualCarrierBounds.iteration_raw_carrier_sizes i).2] at hc
    exact hc
  have hfl : Construction.firstLength (EntryClockPoly3.aI i) (sI i) ≤ 3 * P := by
    unfold Construction.firstLength
    have hp : p ≤ P := Nat.le_of_lt Nat.lt_two_pow_self
    have := h.firstWidth
    omega
  have hnv : GraphVectors.vertexCount i.V (sI i) ≤ 4 * P * EntryClockPoly3.ell3 i.G := by
    unfold GraphVectors.vertexCount
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 4 hs) hV
  have hnb : GraphVectors.auxiliaryCount (sI i) ≤ 4 * P ^ 2 := by
    unfold GraphVectors.auxiliaryCount
    have hsub : sI i - 3 ≤ P := (Nat.sub_le _ _).trans hs
    nlinarith
  change MatrixStage4Codes.cols (EntryClockPoly3.aI i) (sI i)
      (EntryClockPoly3.qI i) (EntryClockPoly3.cyI i) + sI i + EntryClockPoly3.LI' i +
      EntryClockPoly3.rxI i +
      (GraphVectors.vertexCount i.V (sI i) + GraphVectors.auxiliaryCount (sI i)) +
      Construction.firstLength (EntryClockPoly3.aI i) (sI i) ≤ _
  dsimp [P, X] at *
  nlinarith

theorem graph_source_bound (i : LI) (p : ℕ)
    (h : ActualOrderFromCarrier.SourceNames i p) :
    UG (graphJ i) ≤ 32 * 2 ^ p * (EntryClockPoly3.ell3 i.G + 1) ^ 2 := by
  let P := 2 ^ p
  let X := EntryClockPoly3.ell3 i.G + 1
  have hP : 1 ≤ P := by dsimp [P]; exact Nat.one_le_pow _ _ (by decide)
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hs : sI i ≤ P := from_clog h.binsDescription
  have hq := ActualCountClock.q2_le_of_actual_bin i p hs
  have hstr := EntryClockPoly.stream_le i.G
  change sI i + EntryClockPoly3.ell3 i.G + EntryClockPoly3.qI i +
    EntryClockPoly.strG i.G ≤ _
  have hq' : EntryClockPoly3.qI i ≤ 24 * P * X := by
    exact hq.trans (Nat.mul_le_mul_left (24 * P) (by dsimp [X]; omega))
  have hstr' : EntryClockPoly.strG i.G ≤ 2 * X ^ 2 := by
    dsimp [X] at *
    have heq : EntryClockPoly.ellG i.G = EntryClockPoly3.ell3 i.G := rfl
    rw [heq] at hstr
    nlinarith
  dsimp [P, X] at *
  nlinarith

theorem incoming_word_source_bound (i : LI) (p : ℕ)
    (h : ActualOrderFromCarrier.SourceNames i p) :
    (MatrixMaterialization.rowMajor i.M.entry).length ≤ (2 ^ p) ^ 2 := by
  have hr := from_clog h.inputRows
  have hc := from_clog h.inputCols
  rw [MatrixMaterialization.rowMajor_length]
  exact (Nat.mul_le_mul hr hc).trans_eq (by ring)

/-- A single actual-size envelope for both the family and level-j writer
programs. The square in `2^p` comes only from named incoming word length and
internal instance/stream expansion, not from a coarse `oneLevelBound`. -/
theorem envelope_source_bound (i : LI) (p : ℕ)
    (h : ActualOrderFromCarrier.SourceNames i p) :
    JEnv i ≤ 1024 * (2 ^ p) ^ 2 * (EntryClockPoly3.ell3 i.G + 1) ^ 2 := by
  let P := 2 ^ p
  let X := EntryClockPoly3.ell3 i.G + 1
  have hP : 1 ≤ P := by dsimp [P]; exact Nat.one_le_pow _ _ (by decide)
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hA := ActualSourceNames.actual_counts_source_bound i p h.toNames
  have hI := instance_source_bound i p h
  have hG := graph_source_bound i p h
  have hW := incoming_word_source_bound i p h
  have hPP : P ≤ P ^ 2 := by nlinarith
  have hXX : X ≤ X ^ 2 := by nlinarith
  have hPX : P * X ≤ P ^ 2 * X ^ 2 := Nat.mul_le_mul hPP hXX
  have hP2X : P ^ 2 * X ≤ P ^ 2 * X ^ 2 := Nat.mul_le_mul_left _ hXX
  have hPX2 : P * X ^ 2 ≤ P ^ 2 * X ^ 2 := Nat.mul_le_mul_right _ hPP
  have hP2 : P ^ 2 ≤ P ^ 2 * X ^ 2 := Nat.le_mul_of_pos_right _ (by nlinarith)
  unfold JEnv
  dsimp [P, X] at *
  nlinarith

/-- The fixed writer-22 controller excluding its family fuel has an additive
source-shaped clock for every admissible `p`. -/
theorem writer_extra_clock_source : ∃ C : ℕ, ∀ (i : LI) (n p : ℕ),
    Nat.clog 2 (n + 2) ≤ p →
    ActualOrderFromCarrier.SourceNames i p →
    EntryWriter22J.writerBound_j i.G i.c i.b i.y i.lv i.M 0 ≤
      (n + EntryClockPoly3.ell3 i.G + 2) ^ C + 2 ^ (C * p) := by
  obtain ⟨K, D, hKD⟩ := writer_extra_poly
  let C := K + 26 * D
  refine ⟨C, fun i n p hfloor hnames => ?_⟩
  have hp : 1 ≤ p := by
    have hclog := Nat.clog_pos (by decide : 1 < 2) (by omega : 1 < n + 2)
    omega
  let X := n + EntryClockPoly3.ell3 i.G + 2
  have hX : 2 ≤ X := by dsimp [X]; omega
  have h1024 : 1024 ≤ 2 ^ (10 * p) := by
    calc
      1024 = 2 ^ 10 := by norm_num
      _ ≤ 2 ^ (10 * p) := Nat.pow_le_pow_right (by decide) (by omega)
  have hJ : JEnv i ≤ 2 ^ (12 * p) * X ^ 2 := by
    calc
      JEnv i ≤ 1024 * (2 ^ p) ^ 2 * (EntryClockPoly3.ell3 i.G + 1) ^ 2 :=
        envelope_source_bound i p hnames
      _ ≤ 2 ^ (10 * p) * (2 ^ p) ^ 2 * X ^ 2 := by
        have hx : (EntryClockPoly3.ell3 i.G + 1) ^ 2 ≤ X ^ 2 :=
          Nat.pow_le_pow_left (by dsimp [X]; omega) 2
        exact Nat.mul_le_mul (Nat.mul_le_mul_right _ h1024) hx
      _ = 2 ^ (12 * p) * X ^ 2 := by
        rw [← pow_mul, ← pow_add, show 10 * p + p * 2 = 12 * p by omega]
  have hab := EntryClockPoly.absorb K D 12 2 X p (JEnv i) hX hp hJ
  calc
    EntryWriter22J.writerBound_j i.G i.c i.b i.y i.lv i.M 0 ≤
        K * (JEnv i + 1) ^ D := hKD i
    _ ≤ X ^ (K + 4 * D) + 2 ^ ((K + 26 * D) * p) := by
      simpa only [show 2 * 2 * D = 4 * D by omega,
        show 2 * (12 + 1) * D = 26 * D by omega] using hab
    _ ≤ X ^ C + 2 ^ (C * p) :=
      Nat.add_le_add (Nat.pow_le_pow_right (by omega) (by dsimp [C]; omega))
        (by dsimp [C]; exact le_refl _)

theorem writer_full_clock_source : ∃ C : ℕ, ∀ (i : LI) (n p : ℕ),
    Nat.clog 2 (n + 2) ≤ p →
    ActualOrderFromCarrier.SourceNames i p →
    EntryWriter22J.writerBound_j i.G i.c i.b i.y i.lv i.M
      (EntryPrepFamilyJ.TFJ i.G i.c i.b i.y i.lv i.M) ≤
      (n + EntryClockPoly3.ell3 i.G + 2) ^ C + 2 ^ (C * p) := by
  obtain ⟨Cw, hw⟩ := writer_extra_clock_source
  obtain ⟨Cf, hf⟩ := ActualOrderFromCarrier.TFJ_clock_from_source_names
  refine ⟨max Cw Cf + 1, fun i n p hfloor hnames => ?_⟩
  have hp : 1 ≤ p := by
    have hclog := Nat.clog_pos (by decide : 1 < 2) (by omega : 1 < n + 2)
    omega
  have hX : 2 ≤ n + EntryClockPoly3.ell3 i.G + 2 := by omega
  have hsplit := EntryClockPoly3.writerBound_j_split i.G i.c i.b i.y i.lv i.M
    (EntryPrepFamilyJ.TFJ i.G i.c i.b i.y i.lv i.M)
  have hsplit0 := EntryClockPoly3.writerBound_j_split i.G i.c i.b i.y i.lv i.M 0
  have heq : EntryWriter22J.writerBound_j i.G i.c i.b i.y i.lv i.M
      (EntryPrepFamilyJ.TFJ i.G i.c i.b i.y i.lv i.M) =
      EntryWriter22J.writerBound_j i.G i.c i.b i.y i.lv i.M 0 +
        EntryPrepFamilyJ.TFJ i.G i.c i.b i.y i.lv i.M := by omega
  rw [heq]
  exact (Nat.add_le_add (hw i n p hfloor hnames) (hf i n p hfloor hnames)).trans
    (EntryClockPoly3.merge2 _ _ _ _ hX hp)

#print axioms writer_extra_poly
#print axioms instance_source_bound
#print axioms graph_source_bound
#print axioms incoming_word_source_bound
#print axioms envelope_source_bound
#print axioms writer_extra_clock_source
#print axioms writer_full_clock_source

end EthInapproximability.CurrentPaper.ActualWriterClock
