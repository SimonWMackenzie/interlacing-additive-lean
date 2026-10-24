import Paper2.PublicGraphEndpointMachine
import Paper2.FallbackFiniteClock
import Paper2.HeaderOut
import Paper2.CopyAll
import Paper2.A3Branch

/-!
# Unit 3 endpoint, segment 1: the unscheduled branch (`¬ Checks`) as ONE program

Lane `owner:a-h-a3-assembly-2` (private, 26 September 2026). Paper A, lock v12.

ONE fixed program `progU` on the joint bank `JU = GS ⊕ (Unit ⊕ (FJ ⊕ HB))`:
* `GS`: the admitted public-graph endpoint machine bank (`PublicGraphEndpointMachine.Stack`);
  the literal public bytes `EncodedGraph.encode g` enter in the decoder input cell;
* `Unit`: the public unary `k`;
* `FJ`: the admitted finite fallback bank (`FallbackBranch.J`);
* `HB`: the admitted header bank (`HeaderA.HB`).

Stages (every handoff charged by production `BitMachineRawSequence`):
1. `PublicGraphEndpointMachine.program` (admitted, lifted): bytes to unary `n = g.vertices` and the
   canonical terminated-unary endpoint tape `word (graphEdge g hg)`;
2. `CopyAll` (three source-preserving copies): unary `n` to the fallback vertex cell, the endpoint
   tape to the fallback edge-tape cell (`word_eq`: it IS `edgesWord (edgeList edge)`), unary `k` to
   the fallback `k` cell. The fallback start bank is then produced exactly (`bankB_eq`);
3. `FallbackBranchT.program` (admitted, lifted), clock from `FallbackFiniteClock.failed_schedule_run`;
4. `CopyAll`: unary `rows k`, unary `cols k`, and the table word into the header entry cells;
   the threshold cell stays blank (unary `0`);
5. `HeaderA.prog` (admitted, lifted).
On `¬ Checks` the header output cell holds EXACTLY `EncodedSelectedOutput.outputBits … t`
(`A3Branch.outputBits_unscheduled`, lane owner-1, private).
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Paper2.A3Assembly.Unsched

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open BitMachineRawSequence (leftLabel)

/-! ### The endpoint tape is the fallback edge tape -/

theorem edgeList_graph (g : EncodedGraph.Graph) (hg : g.Valid) :
    FallbackColourSearch.edgeList (CanonicalEdgeTape.graphEdge g hg) = g.edges := by
  unfold FallbackColourSearch.edgeList
  have h : (fun z : Fin g.edges.length =>
      ((CanonicalEdgeTape.graphEdge g hg z false).val,
        (CanonicalEdgeTape.graphEdge g hg z true).val)) = fun z => g.edges.get z := by
    funext z
    rw [CanonicalEdgeTape.graphEdge_false, CanonicalEdgeTape.graphEdge_true]
  rw [h, ← List.ofFn_eq_map, List.ofFn_get]

theorem edgesWord_eq (es : List (ℕ × ℕ)) :
    FallbackColourSearch.edgesWord es =
      es.flatMap (fun p => EncodedGraph.unary p.1 ++ EncodedGraph.unary p.2) := by
  induction es with
  | nil => rfl
  | cons p es ih =>
    obtain ⟨a, b⟩ := p
    simp [FallbackColourSearch.edgesWord, FallbackColourSearch.edgeWord1, EncodedGraph.unary, ih]

theorem word_eq (g : EncodedGraph.Graph) (hg : g.Valid) :
    CanonicalEdgeTape.word (CanonicalEdgeTape.graphEdge g hg) =
      FallbackColourSearch.edgesWord
        (FallbackColourSearch.edgeList (CanonicalEdgeTape.graphEdge g hg)) := by
  rw [← PublicGraphEndpointMachine.endpoint_word_eq g hg, edgeList_graph, edgesWord_eq]
  unfold SourceNormalizationMachineDecode.endpointStream
  simp [List.flatMap_assoc]

/-! ### The joint bank -/

abbrev GS := PublicGraphEndpointMachine.Stack
abbrev FJ := FallbackBranch.J
abbrev HB := HeaderA.HB
abbrev JU := GS ⊕ (Unit ⊕ (FJ ⊕ HB))

instance instDecGS : DecidableEq GS := inferInstance
instance instDecHB : DecidableEq HB := inferInstance
instance instDecJU : DecidableEq JU := instDecidableEqSum

def ιG : GS ↪ JU := ⟨Sum.inl, Sum.inl_injective⟩
def ιF : FJ ↪ JU := ⟨fun j => .inr (.inr (.inl j)), by intro a b h; simpa using h⟩
def ιH : HB ↪ JU := ⟨fun j => .inr (.inr (.inr j)), by intro a b h; simpa using h⟩

theorem bank_G (X Z : GS → List Bool) (Y : Unit ⊕ (FJ ⊕ HB) → List Bool) :
    bank ιG (Sum.elim X Y) Z = Sum.elim Z Y := by
  funext c
  rcases c with c | c
  · exact bank_at ιG _ Z c
  · exact bank_outside ιG _ Z (.inr c) (by rintro ⟨k, hk⟩; cases hk)

theorem bank_F (X : GS → List Bool) (K : Unit → List Bool) (Y Z : FJ → List Bool)
    (H : HB → List Bool) :
    bank ιF (Sum.elim X (Sum.elim K (Sum.elim Y H))) Z =
      Sum.elim X (Sum.elim K (Sum.elim Z H)) := by
  funext c
  rcases c with c | c | c | c
  · exact bank_outside ιF _ Z (.inl c) (by rintro ⟨k, hk⟩; cases hk)
  · exact bank_outside ιF _ Z (.inr (.inl c)) (by rintro ⟨k, hk⟩; cases hk)
  · exact bank_at ιF _ Z c
  · exact bank_outside ιF _ Z (.inr (.inr (.inr c))) (by rintro ⟨k, hk⟩; cases hk)

theorem bank_H (X : GS → List Bool) (K : Unit → List Bool) (Y : FJ → List Bool)
    (H Z : HB → List Bool) :
    bank ιH (Sum.elim X (Sum.elim K (Sum.elim Y H))) Z =
      Sum.elim X (Sum.elim K (Sum.elim Y Z)) := by
  funext c
  rcases c with c | c | c | c
  · exact bank_outside ιH _ Z (.inl c) (by rintro ⟨k, hk⟩; cases hk)
  · exact bank_outside ιH _ Z (.inr (.inl c)) (by rintro ⟨k, hk⟩; cases hk)
  · exact bank_outside ιH _ Z (.inr (.inr (.inl c))) (by rintro ⟨k, hk⟩; cases hk)
  · exact bank_at ιH _ Z c

/-! ### Named cells -/

def kIn : JU := .inr (.inl ())
def vertJ : JU := .inl (.inl (.inr 0))
def streamJ : JU := .inl (.inl (.inr 4))
def scrJ : JU := .inl (.inr 1)
def fV : JU := .inr (.inr (.inl (.inr (.inr ()))))
def fE : JU := .inr (.inr (.inl (.inl (.inl 1))))
def fK : JU := .inr (.inr (.inl (.inr (.inl (.inl 0)))))
def fRows : JU := .inr (.inr (.inl (.inr (.inl (.inr (.inr .rows))))))
def fCols : JU := .inr (.inr (.inl (.inr (.inl (.inr (.inr .cols))))))
def fOut : JU := .inr (.inr (.inl (.inr (.inl (.inr (.inr .output))))))
def h0 : JU := .inr (.inr (.inr (.inr 0)))
def h1 : JU := .inr (.inr (.inr (.inr 1)))
def hOut : JU := .inr (.inr (.inr (.inr 5)))

theorem hOut_eq : hOut = ιH HeaderA.outH := rfl

def srcB : Fin 3 → JU := ![vertJ, streamJ, kIn]
def dstB : Fin 3 → JU := ![fV, fE, fK]
def cpB (i : Fin 3) : Fin 3 ↪ JU :=
  ⟨![srcB i, dstB i, scrJ], by
    intro a b h
    fin_cases i <;> fin_cases a <;> fin_cases b <;>
      simp_all [srcB, dstB, vertJ, streamJ, kIn, fV, fE, fK, scrJ]⟩

def srcD : Fin 3 → JU := ![fRows, fCols, fOut]
def dstD : Fin 3 → JU := ![h0, h1, hOut]
def cpD (i : Fin 3) : Fin 3 ↪ JU :=
  ⟨![srcD i, dstD i, scrJ], by
    intro a b h
    fin_cases i <;> fin_cases a <;> fin_cases b <;>
      simp_all [srcD, dstD, fRows, fCols, fOut, h0, h1, hOut, scrJ]⟩

/-! ### Banks -/

def restA (k : ℕ) : Unit ⊕ (FJ ⊕ HB) → List Bool :=
  Sum.elim (fun _ => List.replicate k true) (Sum.elim (fun _ => []) (fun _ => []))

/-- Entry bank: literal public graph bytes in the decoder input cell, unary `k`, all else blank. -/
def entry (g : EncodedGraph.Graph) (k : ℕ) : JU → List Bool :=
  Sum.elim (PublicGraphEndpointMachine.initialBank (EncodedGraph.encode g)) (restA k)

def bankA (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) : JU → List Bool :=
  Sum.elim (PublicGraphEndpointMachine.resultBank g hg) (restA k)

/-- The fallback start bank installed inside the joint bank. -/
def bankB (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) : JU → List Bool :=
  Sum.elim (PublicGraphEndpointMachine.resultBank g hg)
    (Sum.elim (fun _ => List.replicate k true)
      (Sum.elim (FallbackBranchT.start (CanonicalEdgeTape.graphEdge g hg) k).stk (fun _ => [])))

/-- The exact fallback exit region (`FallbackFiniteClock.RunsToTable`), counter scratch `q`. -/
def fbFinal {v e : ℕ} (edge : Fin e → Bool → Fin v) (k : ℕ) (q : List Bool) : FJ → List Bool :=
  Sum.elim (FallbackBranch.SA (FallbackColourSearch.edgeList edge) q)
    (Sum.elim (Sum.elim (FallbackDimsPrinter.pbank k 0)
      (MatrixTableWriter.ready (fun _ => [])
        (FiniteFallbackOutput.rows k) (FiniteFallbackOutput.cols k) 0 0 0 0 []
        (MatrixMaterialization.rowMajor
          (FiniteFallbackOutput.fallbackMatrix edge k))).contents) (fun _ => []))

def bankC (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) (q : List Bool) : JU → List Bool :=
  Sum.elim (PublicGraphEndpointMachine.resultBank g hg)
    (Sum.elim (fun _ => List.replicate k true)
      (Sum.elim (fbFinal (CanonicalEdgeTape.graphEdge g hg) k q) (fun _ => [])))

def tableU (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) : List Bool :=
  MatrixMaterialization.rowMajor
    (FiniteFallbackOutput.fallbackMatrix (CanonicalEdgeTape.graphEdge g hg) k)

def bankD (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) (q : List Bool) : JU → List Bool :=
  Sum.elim (PublicGraphEndpointMachine.resultBank g hg)
    (Sum.elim (fun _ => List.replicate k true)
      (Sum.elim (fbFinal (CanonicalEdgeTape.graphEdge g hg) k q)
        (HeaderA.Hin (FiniteFallbackOutput.rows k) (FiniteFallbackOutput.cols k) 0
          (tableU g hg k) [])))

/-- The exact exit bank; `F` is the header region (admitted header: only `outH` is stated). -/
def exitU (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) (q : List Bool) (F : HB → List Bool) :
    JU → List Bool :=
  Sum.elim (PublicGraphEndpointMachine.resultBank g hg)
    (Sum.elim (fun _ => List.replicate k true)
      (Sum.elim (fbFinal (CanonicalEdgeTape.graphEdge g hg) k q) F))

/-! ### Cell values -/

theorem resultBank_vert (g : EncodedGraph.Graph) (hg : g.Valid) :
    PublicGraphEndpointMachine.resultBank g hg (.inl (.inr 0)) = List.replicate g.vertices true := rfl

theorem resultBank_stream (g : EncodedGraph.Graph) (hg : g.Valid) :
    PublicGraphEndpointMachine.resultBank g hg (.inl (.inr 4)) =
      CanonicalEdgeTape.word (CanonicalEdgeTape.graphEdge g hg) := rfl

theorem resultBank_scr (g : EncodedGraph.Graph) (hg : g.Valid) :
    PublicGraphEndpointMachine.resultBank g hg (.inr 1) = [] := rfl

theorem doneB (T : JU → List Bool) :
    CopyAll.done cpB 3 T =
      Function.update (Function.update (Function.update T fV (T vertJ ++ T fV))
        fE (T streamJ ++ T fE)) fK (T kIn ++ T fK) := rfl

theorem doneD (T : JU → List Bool) :
    CopyAll.done cpD 3 T =
      Function.update (Function.update (Function.update T h0 (T fRows ++ T h0))
        h1 (T fCols ++ T h1)) hOut (T fOut ++ T hOut) := rfl

theorem bankB_eq (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) :
    CopyAll.done cpB 3 (bankA g hg k) = bankB g hg k := by
  rw [doneB]
  funext c
  rcases c with c | c | (j | c)
  · rfl
  · rfl
  · rcases j with (s | u) | ((p | ((b | x) | w)) | u)
    · fin_cases s
      · rfl
      · exact (List.append_nil _).trans (word_eq g hg)
      · rfl
      · rfl
      · rfl
      · rfl
    · rfl
    · fin_cases p
      · exact List.append_nil _
      · rfl
      · rfl
      · rfl
    · rfl
    · fin_cases x <;> rfl
    · cases w <;> rfl
    · exact List.append_nil _
  · rfl

theorem bankD_eq (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) (q : List Bool) :
    CopyAll.done cpD 3 (bankC g hg k q) = bankD g hg k q := by
  rw [doneD]
  funext c
  rcases c with c | c | c | (x | j)
  · rfl
  · rfl
  · rfl
  · rfl
  · fin_cases j
    · exact List.append_nil _
    · exact List.append_nil _
    · rfl
    · rfl
    · rfl
    · rfl

/-! ### The program -/

def gProg := fun l => stackStmt ιG (PublicGraphEndpointMachine.program l)
def fProg := fun l => stackStmt ιF (FallbackBranchT.program l)
def hProg := fun l => stackStmt ιH (HeaderA.prog l)

def ctlA : BitMachineRawSequence.Control (Option Bool) SourceNormalizationMachineDecode.Control :=
  (none, PublicGraphEndpointMachine.parserControl)
def ctlF : FallbackBranchT.ACtl := FallbackBranchT.embedS FallbackBranchT.sStart

def p1 := BitMachineRawSequence.program gProg (CopyAll.prog cpB) (.inl ⟨0, by omega⟩) ctlA
  (none : Option Bool)
def p2 := BitMachineRawSequence.program p1 fProg (Sum.inl FallbackBranch.Adm.alloc)
  (ctlA, (none : Option Bool)) ctlF
def p3 := BitMachineRawSequence.program p2 (CopyAll.prog cpD) (.inl ⟨0, by omega⟩)
  ((ctlA, (none : Option Bool)), ctlF) (none : Option Bool)
/-- ONE fixed program for the unscheduled branch. -/
def progU := BitMachineRawSequence.program p3 hProg HeaderA.progStart
  (((ctlA, (none : Option Bool)), ctlF), (none : Option Bool)) HeaderA.progCtl

abbrev LabG := BitMachineRawSequence.Label BitMachineCopy.Label SourceNormalizationMachineDecode.Label
abbrev LabH := BitMachineRawSequence.Label (BitMachineRawSequence.Label
    (BitMachineRawSequence.Label MatrixExactUnaryHeaderSequence.ConversionLabel
      MatrixExactUnaryHeaderSequence.ConversionLabel)
    MatrixExactUnaryHeaderSequence.ConversionLabel) MatrixInstanceEncoding.Label
abbrev LabU := BitMachineRawSequence.Label (BitMachineRawSequence.Label (BitMachineRawSequence.Label
  (BitMachineRawSequence.Label LabG (CopyAll.Lab 3)) FallbackBranchT.ALab) (CopyAll.Lab 3)) LabH

def startU : LabU := leftLabel (leftLabel (leftLabel (leftLabel
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))))
def ctlU := ((((ctlA, (none : Option Bool)), ctlF), (none : Option Bool)), HeaderA.progCtl)

/-! ### Clock -/

def LB (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) : ℕ :=
  g.vertices + (CanonicalEdgeTape.word (CanonicalEdgeTape.graphEdge g hg)).length + k

def LD (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) : ℕ :=
  FiniteFallbackOutput.rows k + FiniteFallbackOutput.cols k + (tableU g hg k).length

def headerClock (k : ℕ) : ℕ :=
  UnaryBinaryEncoding.coefficient * (FiniteFallbackOutput.rows k + 1) ^ 2 +
    UnaryBinaryEncoding.coefficient * (FiniteFallbackOutput.cols k + 1) ^ 2 +
    UnaryBinaryEncoding.coefficient * (0 + 1) ^ 2 +
    (2 * (EncodedCommunication.natField (FiniteFallbackOutput.rows k) ++
      EncodedCommunication.natField (FiniteFallbackOutput.cols k) ++
      EncodedCommunication.natField 0).length + 2) + 3

def clockU (g : EncodedGraph.Graph) (hg : g.Valid) (Δ : ℕ) (γ : ℚ) (k : ℕ) : ℕ :=
  103 * ((EncodedGraph.encode g).length + 1) ^ 3 + (3 * (2 * LB g hg k + 3) + 1) +
    FallbackFiniteClock.coefficient (CompletePublicScheduleScratch.sizeThreshold Δ γ) Δ *
      2 ^ (3 * k) +
    (3 * (2 * LD g hg k + 3) + 1) + headerClock k + 4

/-! ### Stage runs -/

theorem stageA (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) :
    ∃ t ≤ 103 * ((EncodedGraph.encode g).length + 1) ^ 3,
      ((advance gProg)^[t]) (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
        ctlA, entry g k⟩ : TM2.Cfg (fun _ : JU => Bool) _ _) =
        ⟨none, (none, SourceNormalizationMachineDecode.doneControl true), bankA g hg k⟩ := by
  obtain ⟨t, ht, hr⟩ := PublicGraphEndpointMachine.physical_run_public g hg
  refine ⟨t, ht, ?_⟩
  have h := BitMachineStackRun.run ιG (entry g k) PublicGraphEndpointMachine.program
    (PublicGraphEndpointMachine.start (EncodedGraph.encode g)) t
  have hr' : ((advance PublicGraphEndpointMachine.program)^[t])
      (PublicGraphEndpointMachine.start (EncodedGraph.encode g)) =
      ⟨none, (none, SourceNormalizationMachineDecode.doneControl true),
        PublicGraphEndpointMachine.resultBank g hg⟩ := hr
  rw [hr'] at h
  change ((advance gProg)^[t]) ⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
      ctlA, bank ιG (Sum.elim (PublicGraphEndpointMachine.initialBank (EncodedGraph.encode g))
        (restA k)) (PublicGraphEndpointMachine.initialBank (EncodedGraph.encode g))⟩ =
    ⟨none, (none, SourceNormalizationMachineDecode.doneControl true),
      bank ιG (Sum.elim (PublicGraphEndpointMachine.initialBank (EncodedGraph.encode g))
        (restA k)) (PublicGraphEndpointMachine.resultBank g hg)⟩ at h
  rw [bank_G, bank_G] at h
  exact h

theorem stageB (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) :
    ∃ t ≤ 3 * (2 * LB g hg k + 3) + 1, ∃ v',
      ((advance (CopyAll.prog cpB))^[t])
          (⟨some (.inl ⟨0, by omega⟩), (none : Option Bool), bankA g hg k⟩ :
            TM2.Cfg (fun _ : JU => Bool) (CopyAll.Lab 3) (Option Bool)) =
        ⟨none, v', bankB g hg k⟩ := by
  have hsd : ∀ i j, cpB i 0 ≠ cpB j 1 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [cpB, srcB, dstB, vertJ, streamJ, kIn, fV, fE, fK]
  have hzd : ∀ i j, cpB i 2 ≠ cpB j 1 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [cpB, dstB, scrJ, fV, fE, fK]
  have hdd : ∀ i j, cpB i 1 = cpB j 1 → i = j := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [cpB, dstB, fV, fE, fK]
  have hz : ∀ i, bankA g hg k (cpB i 2) = [] := by
    intro i
    fin_cases i <;> rfl
  have hL : ∀ i, (bankA g hg k (cpB i 0)).length ≤ LB g hg k := by
    intro i
    fin_cases i
    · show (List.replicate g.vertices true).length ≤ _
      simp only [LB, List.length_replicate]; omega
    · show (CanonicalEdgeTape.word (CanonicalEdgeTape.graphEdge g hg)).length ≤ _
      simp only [LB]; omega
    · show (List.replicate k true).length ≤ _
      simp only [LB, List.length_replicate]; omega
  obtain ⟨t, ht, v', h⟩ := CopyAll.all_run cpB hsd hzd hdd (bankA g hg k) hz (LB g hg k) hL none
  rw [bankB_eq] at h
  exact ⟨t, ht, v', h⟩

theorem stageC (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (Δ : ℕ) (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (k : ℕ)
    (hinc : ∀ v, ∃ e b, CanonicalEdgeTape.graphEdge g hg e b = v)
    (hdeg : ∀ v, SourceItems.degree (CanonicalEdgeTape.graphEdge g hg) v ≤ Δ)
    (hc : ¬ CompletePublicScheduleScratch.Checks (V := Fin g.vertices) (E := Fin g.edges.length)
      (Nat.clog 2 g.vertices) Δ γ) :
    ∃ t ≤ FallbackFiniteClock.coefficient (CompletePublicScheduleScratch.sizeThreshold Δ γ) Δ *
        2 ^ (3 * k),
      ∃ (ctl : FallbackBranchT.ACtl) (q : List Bool),
        ((advance fProg)^[t]) (⟨some (Sum.inl FallbackBranch.Adm.alloc), ctlF, bankB g hg k⟩ :
          TM2.Cfg (fun _ : JU => Bool) _ _) = ⟨none, ctl, bankC g hg k q⟩ := by
  haveI : Nonempty (Fin g.vertices) := ⟨⟨0, hn⟩⟩
  obtain ⟨t, ht, ctl, q, hr⟩ := FallbackFiniteClock.failed_schedule_run
    (CanonicalEdgeTape.graphEdge g hg) Δ γ hγ hΔ hinc hdeg hc k
  refine ⟨t, ht, ctl, q, ?_⟩
  unfold FallbackFiniteClock.RunsToTable at hr
  have h := BitMachineStackRun.run ιF (bankB g hg k) FallbackBranchT.program
    (FallbackBranchT.start (CanonicalEdgeTape.graphEdge g hg) k) t
  have hr' : ((advance FallbackBranchT.program)^[t])
      (FallbackBranchT.start (CanonicalEdgeTape.graphEdge g hg) k) =
      ⟨none, ctl, fbFinal (CanonicalEdgeTape.graphEdge g hg) k q⟩ := hr
  rw [hr'] at h
  change ((advance fProg)^[t]) ⟨some (Sum.inl FallbackBranch.Adm.alloc), ctlF,
      bank ιF (bankB g hg k) (FallbackBranchT.start (CanonicalEdgeTape.graphEdge g hg) k).stk⟩ =
    ⟨none, ctl, bank ιF (bankB g hg k) (fbFinal (CanonicalEdgeTape.graphEdge g hg) k q)⟩ at h
  unfold bankB at h
  rw [bank_F, bank_F] at h
  exact h

theorem stageD (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) (q : List Bool) :
    ∃ t ≤ 3 * (2 * LD g hg k + 3) + 1, ∃ v',
      ((advance (CopyAll.prog cpD))^[t])
          (⟨some (.inl ⟨0, by omega⟩), (none : Option Bool), bankC g hg k q⟩ :
            TM2.Cfg (fun _ : JU => Bool) (CopyAll.Lab 3) (Option Bool)) =
        ⟨none, v', bankD g hg k q⟩ := by
  have hsd : ∀ i j, cpD i 0 ≠ cpD j 1 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [cpD, srcD, dstD, fRows, fCols, fOut, h0, h1, hOut]
  have hzd : ∀ i j, cpD i 2 ≠ cpD j 1 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [cpD, dstD, scrJ, h0, h1, hOut]
  have hdd : ∀ i j, cpD i 1 = cpD j 1 → i = j := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [cpD, dstD, h0, h1, hOut]
  have hz : ∀ i, bankC g hg k q (cpD i 2) = [] := by
    intro i
    fin_cases i <;> rfl
  have hL : ∀ i, (bankC g hg k q (cpD i 0)).length ≤ LD g hg k := by
    intro i
    fin_cases i
    · show (List.replicate (FiniteFallbackOutput.rows k) true).length ≤ _
      simp only [LD, List.length_replicate]; omega
    · show (List.replicate (FiniteFallbackOutput.cols k) true).length ≤ _
      simp only [LD, List.length_replicate]; omega
    · show (tableU g hg k).length ≤ _
      simp only [LD]; omega
  obtain ⟨t, ht, v', h⟩ := CopyAll.all_run cpD hsd hzd hdd (bankC g hg k q) hz (LD g hg k) hL none
  rw [bankD_eq] at h
  exact ⟨t, ht, v', h⟩

theorem stageE (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) (q : List Bool) :
    ∃ t ≤ headerClock k, ∃ v, ∃ F : HB → List Bool,
      ((advance hProg)^[t]) (⟨some HeaderA.progStart, HeaderA.progCtl, bankD g hg k q⟩ :
          TM2.Cfg (fun _ : JU => Bool) _ _) = ⟨none, v, exitU g hg k q F⟩ ∧
        F HeaderA.outH = EncodedCommunication.encodeInstance
          ⟨FiniteFallbackOutput.rows k, FiniteFallbackOutput.cols k, 0, tableU g hg k⟩ := by
  obtain ⟨t, ht, v, F, hr, hF⟩ := HeaderA.header_instance
    ⟨FiniteFallbackOutput.rows k, FiniteFallbackOutput.cols k, 0, tableU g hg k⟩ []
  refine ⟨t, ht, v, F, ?_, by rw [hF, List.append_nil]⟩
  have h := BitMachineStackRun.run ιH (bankD g hg k q) HeaderA.prog
    ⟨some HeaderA.progStart, HeaderA.progCtl,
      HeaderA.Hin (FiniteFallbackOutput.rows k) (FiniteFallbackOutput.cols k) 0 (tableU g hg k) []⟩ t
  rw [hr] at h
  change ((advance hProg)^[t]) ⟨some HeaderA.progStart, HeaderA.progCtl,
      bank ιH (bankD g hg k q) (HeaderA.Hin (FiniteFallbackOutput.rows k)
        (FiniteFallbackOutput.cols k) 0 (tableU g hg k) [])⟩ =
    ⟨none, v, bank ιH (bankD g hg k q) F⟩ at h
  unfold bankD at h
  rw [bank_H, bank_H] at h
  exact h

/-! ### Segment 1 main theorem -/

/-- **Segment 1.** On `¬ Checks`, the ONE fixed program `progU`, started on the literal public
bytes `EncodedGraph.encode g` and unary `k` (all other cells blank), halts within the explicit
clock `clockU` in the exact exit bank `exitU` (public-graph region `resultBank g hg`, unary `k`
restored, fallback region exactly `RunsToTable`'s with counter scratch `q`, header region `F`),
and the header output cell holds EXACTLY the consumer word `outputBits hn edge Δ γ k t`. -/
theorem unscheduled_run (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices)
    (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ) (k : ℕ)
    (hinc : ∀ v, ∃ e b, CanonicalEdgeTape.graphEdge g hg e b = v)
    (hdeg : ∀ v, SourceItems.degree (CanonicalEdgeTape.graphEdge g hg) v ≤ Δ)
    (hc : ¬ CompletePublicScheduleScratch.Checks (V := Fin g.vertices) (E := Fin g.edges.length)
      (Nat.clog 2 g.vertices) Δ γ)
    (t : (TotalFiniteConstructorScratch.select hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape) :
    ∃ T ≤ clockU g hg Δ γ k, ∃ ctl, ∃ (q : List Bool) (F : HB → List Bool),
      ((advance progU)^[T]) (⟨some startU, ctlU, entry g k⟩ : TM2.Cfg (fun _ : JU => Bool) _ _) =
        ⟨none, ctl, exitU g hg k q F⟩ ∧
      F HeaderA.outH = EncodedSelectedOutput.outputBits hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k t ∧
      (TotalFiniteConstructorScratch.select hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits t
        = [] := by
  obtain ⟨tA, htA, hA⟩ := stageA g hg k
  obtain ⟨tB, htB, vB, hB⟩ := stageB g hg k
  obtain ⟨tC, htC, ctlC, q, hC⟩ := stageC g hg hn Δ γ hγ hΔ k hinc hdeg hc
  obtain ⟨tD, htD, vD, hD⟩ := stageD g hg k q
  obtain ⟨tE, htE, vE, F, hE, hF⟩ := stageE g hg k q
  obtain ⟨u1, hu1, r1⟩ := BitMachineRawSequence.runs gProg (CopyAll.prog cpB) _ _ _ _ _ _ _ _ _
    tA tB hA hB
  obtain ⟨u2, hu2, r2⟩ := BitMachineRawSequence.runs p1 fProg _ _ _ _ _ _ _ _ _
    u1 tC r1 hC
  obtain ⟨u3, hu3, r3⟩ := BitMachineRawSequence.runs p2 (CopyAll.prog cpD) _ _ _ _ _ _ _ _ _
    u2 tD r2 hD
  obtain ⟨u4, hu4, r4⟩ := BitMachineRawSequence.runs p3 hProg _ _ _ _ _ _ _ _ _
    u3 tE r3 hE
  obtain ⟨hbits, htape⟩ := A3Assembly.Branch.outputBits_unscheduled hn
    (CanonicalEdgeTape.graphEdge g hg) Δ γ k hc t
  refine ⟨u4, ?_, _, q, F, r4, ?_, htape⟩
  · unfold clockU; omega
  · rw [hF, hbits]; rfl

end

#print axioms word_eq
#print axioms bankB_eq
#print axioms bankD_eq
#print axioms stageA
#print axioms stageB
#print axioms stageC
#print axioms stageD
#print axioms stageE
#print axioms unscheduled_run

end Paper2.A3Assembly.Unsched
