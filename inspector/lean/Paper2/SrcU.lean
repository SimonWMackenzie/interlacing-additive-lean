import Paper2.OTTags
import Paper2.ScanValue
import Paper2.SourcePos
import Paper2.ItemOperands
import Paper2.SourceTailFetch

/-! Unit 3, segment (1): ONE-bank assembly of the source case for the
UNRESTRICTED tag: item operands -> outer-token equality and token extraction
-> physical `scanAtCanonical` -> unary `sourcePosition` -> tail fetch.

Bank `JA = OTBody.B ⊕ (ScanJoin.JJ ⊕ Fin 4)`. Program `srcU` (production
`BitMachineRawSequence` handoffs):
1. `ItemOperands.program` splits the raw source-row word (cell `srcA`) into
   unary item group, kind bit, terminated item value, written DIRECTLY into
   the `ScanJoin` entry cells `K 12`, `R 5`, `R 2`; the row word `u` stays;
2. `OTGen.fullG` over `FetchIndexed.rowProgram` (lifted by `Sum.inl`):
   outer-token equality bit (cell `eqC`) and unary token `(Z.2 0).1` (cell
   `aC`);
3. `ScanJoin.full` lifted by an injective placement SHARING `ScanJoin`'s
   decode cell `K 0` with `aC` (no copy);
4. `OTOps.clr` clears the unary index cell (it held `s` after step 2);
5. `SourcePos.program` lifted by a placement sharing its cells with `eqC`,
   the scan's activity and rank cells, `sC` (unary `s`) and the index cell;
6. the production `FetchIndexed.colProgram` (column code) at the unary
   source position: the Codex-checked
   `SourceTailFetch.unrestricted_source_tail_fetch`.

Result (`srcU_run`): the label cell holds
`C.2.encode (sourceColumn activity i Z)` with
`activity = SourceActiveRank.scanAtCanonical (graphEdge g hg) hs hq`, the
row cell holds `C.1.encode u`: together the encoded
`baseRequest activity (.inr (i, u)) Z` (`eq:raw-source`). -/

set_option maxHeartbeats 32000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.SrcU

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource RecursiveRequestCodeShape
open RecursiveLabelCodecScratch RecursiveEntries SourceMatrix
open BitMachineRawSequence (leftLabel)
open Paper2.OTOps (u)
open Paper2.OTBody (B BB aC eqC sC idxB lblB ob)
open Paper2.ScanDecodeMachine (K D0)
open Paper2.RankRun (R RB)

abbrev JA := B ⊕ (ScanJoin.JJ ⊕ Fin 4)

def srcA : JA := .inr (.inr 0)
def sp5 : JA := .inr (.inr 1)
def sp6 : JA := .inr (.inr 2)
def K0 : ScanJoin.JJ := .inl (0 : K)
def rkC : ScanJoin.JJ := .inr (.inr 3)
def iA : JA := .inr (.inl (.inl (12 : K)))
def iK : JA := .inr (.inl (.inr (.inr (5 : R))))
def iX : JA := .inr (.inl (.inr (.inr (2 : R))))

def ιB : B ↪ JA := ⟨Sum.inl, Sum.inl_injective⟩
def ιF : FetchIndexed.Stack ↪ JA := ⟨fun k => .inl (.inl k), fun a b h => by simpa using h⟩

def ιSf (x : ScanJoin.JJ) : JA := if x = K0 then .inl aC else .inr (.inl x)

theorem ιSf_inj : Function.Injective ιSf := by
  intro a b h
  simp only [ιSf] at h
  split_ifs at h <;> simp_all [aC]

def ιS : ScanJoin.JJ ↪ JA := ⟨ιSf, ιSf_inj⟩

def ιPf : Fin 7 → JA :=
  ![.inl eqC, .inr (.inl ScanJoin.actC), .inr (.inl rkC), .inl sC, .inl idxB, sp5, sp6]

theorem ιPf_inj : Function.Injective ιPf := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp_all [ιPf, eqC, sC, idxB, sp5, sp6, ScanJoin.actC, rkC, FetchIndexed.idxC]

def ιP : Fin 7 ↪ JA := ⟨ιPf, ιPf_inj⟩

/-! ### Programs -/

def S1 := ItemOperands.program srcA iA iK iX
def S2 := fun l => stackStmt ιB (OTGen.fullG FetchIndexed.rowProgram FetchIndexed.rowStart
  FetchIndexed.rowControl l)
def S3 := fun l => stackStmt ιS (ScanJoin.full l)
def S4 := OTOps.clr (.inl idxB : JA)
def S5 := fun l => stackStmt ιP (SourcePos.program l)
def S6 := fun l => stackStmt ιF (FetchIndexed.colProgram l)

abbrev c1 := ((none : Option Bool), (((none : Option Bool), (none : Option Bool)),
  (none : Option Bool)))
abbrev c2 := OTGen.fullGCtl FetchIndexed.rowControl
abbrev c3 := (ScanJoin.testCtl, ((none : Option Bool), ((), (ScanJoin.opCtl,
  RankRun.startCtl))))
abbrev c5 := ((none : Option Bool), ((none : Option Bool), ((), (none : Option Bool))))

def z1 := BitMachineRawSequence.program S1 S2
  (OTGen.fullGStart FetchIndexed.rowProgram FetchIndexed.rowStart FetchIndexed.rowControl) c1 c2
def z2 := BitMachineRawSequence.program z1 S3
  (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel ()))))) (c1, c2) c3
def z3 := BitMachineRawSequence.program z2 S4 () ((c1, c2), c3) ob
def z4 := BitMachineRawSequence.program z3 S5 (leftLabel .l0) (((c1, c2), c3), ob) c5
/-- The unrestricted source arm: one fixed program. -/
def srcU := BitMachineRawSequence.program z4 S6 FetchIndexed.colStart ((((c1, c2), c3), ob), c5)
  FetchIndexed.colControl
def srcUStart := FetchIndexed.labelOf srcU
  (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel ()))))))
def srcUCtl := (((((c1, c2), c3), ob), c5), FetchIndexed.colControl)

/-! ### Bank lemmas -/

theorem bank_ιB (X : B → List Bool) (Y : ScanJoin.JJ ⊕ Fin 4 → List Bool) (T : B → List Bool) :
    bank ιB (Sum.elim X Y) T = Sum.elim T Y := by
  funext j
  cases j with
  | inl j => exact bank_at ιB _ T j
  | inr j => exact bank_outside ιB _ T (.inr j) (by rintro ⟨k, hk⟩; cases hk)

theorem ιS_K0 : ιS K0 = .inl aC := by
  show ιSf K0 = _
  unfold ιSf
  exact if_pos rfl

theorem ιS_ne (j : ScanJoin.JJ) (hj : j ≠ K0) : ιS j = .inr (.inl j) := by
  show ιSf j = _
  unfold ιSf
  exact if_neg hj

theorem ιS_range (x : JA) (hx : ∀ k, k ≠ K0 → x ≠ .inr (.inl k)) (ha : x ≠ .inl aC) :
    ¬ ∃ k, ιS k = x := by
  rintro ⟨k, hk⟩
  by_cases hk0 : k = K0
  · subst hk0
    rw [ιS_K0] at hk
    exact ha hk.symm
  · rw [ιS_ne k hk0] at hk
    exact hx k hk0 hk.symm

theorem bank_ιS (X : B → List Bool) (Y : ScanJoin.JJ → List Bool) (Z : Fin 4 → List Bool)
    (T : ScanJoin.JJ → List Bool) :
    bank ιS (Sum.elim X (Sum.elim Y Z)) T =
      Sum.elim (Function.update X aC (T K0)) (Sum.elim (Function.update T K0 (Y K0)) Z) := by
  funext j
  rcases j with j | j | j
  · by_cases hj : j = aC
    · subst hj
      rw [← ιS_K0, bank_at, ιS_K0, Sum.elim_inl, Function.update_self]
    · rw [bank_outside ιS _ T (.inl j) (ιS_range _ (fun k _ h => by cases h)
        (fun h => hj (Sum.inl_injective h))), Sum.elim_inl, Sum.elim_inl,
        Function.update_of_ne hj]
  · by_cases hj : j = K0
    · subst hj
      rw [bank_outside ιS _ T (.inr (.inl K0)) (ιS_range _
        (fun k hk h => hk (Sum.inl_injective (Sum.inr_injective h)).symm) (fun h => by cases h)),
        Sum.elim_inr, Sum.elim_inl, Sum.elim_inr, Sum.elim_inl, Function.update_self]
    · rw [← ιS_ne j hj, bank_at, ιS_ne j hj, Sum.elim_inr, Sum.elim_inl,
        Function.update_of_ne hj]
  · rw [bank_outside ιS _ T (.inr (.inr j)) (ιS_range _
      (fun k _ h => by cases h) (fun h => by cases h)), Sum.elim_inr, Sum.elim_inr,
      Sum.elim_inr, Sum.elim_inr]

/-! ### Clocks -/

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

/-- The exact scan-and-position clock (branch on the group/padding test). -/
def scanPosBound (g : EncodedGraph.Graph) (hg : g.Valid) (a r ig xv : ℕ) (kb : Bool) : ℕ :=
  if h : 0 < g.edges.length ∧ a / r / 3 / g.edges.length = ig then
    let e : Fin g.edges.length := ⟨a / r / 3 % g.edges.length, Nat.mod_lt _ h.1⟩
    let edge := CanonicalEdgeTape.graphEdge g hg
    ((ScanDecodeMachine.decodeBound a r g.edges.length +
        (a / r / 3 / g.edges.length + ig + 4) + 1) +
        ((((103 * ((EncodedGraph.encode g).length + 1)^3 +
          (2 * (CanonicalEdgeTape.word edge).length + 2) + (2 * g.vertices + 2) +
          (2 * e.val + 2) + (2 * e.val + 2) + 1 + 1 +
          UnaryFieldListParserScratch.fuel g.vertices (2 * (e.val + 1))
            (CanonicalEdgeTape.word edge) + 7) +
          ((edge e true).val + (edge e false).val + 7) + 1) +
          (max (edge e false).val (max (edge e true).val xv) + 7) + 1) + 1) + 1) +
    (CanonicalEndpointRankMachine.semanticRank (RankRun.kindOfNat (a / r % 3))
        (RankRun.itemOfBool kb) (edge e false).val (edge e true).val xv + 3)
  else
    ((ScanDecodeMachine.decodeBound a r g.edges.length +
        (a / r / 3 / g.edges.length + ig + 4) + 1) + (1 + 1) + 1) + (0 + 3)

end

end Paper2.SrcU
