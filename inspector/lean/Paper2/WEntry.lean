import Paper2.EntryCore
import Paper2.SuccessFetchJoin
import Paper2.FullSupport

/-! Unit 3, segment (4), first part: the per-entry program of the row-major writer.
Bank `A = Aux ⊕ Fin 3`, `Aux = JL ⊕ (Fin 5 ⊕ (FetchLabel.Stack ⊕ Fin 2))`:
the loop bank at rest `restL g r` (master region), five retained cells `cR 0..4`
(0: row word, 1: column word, 2: serialized level-`K` row code, 3: serialized
level-`K` column code, 4: unary `K`), the `FetchLabel` scratch, the forward sample
word `fwA` (columns first, then rows), the unary column count `myA`; the three writer
cells `.inr 0` (unary `x`), `.inr 1` (unary `y`), `.inr 2` (answer).
ONE fixed program `wprog`: the admitted `FetchIndexed.rowProgram` placed with its
label cell on `cR 0` and its index cell on the writer's `x` cell; the admitted
`FetchIndexed.colProgram` placed with its label cell on `cR 1` and its index cell on
the writer's `y` cell (both with `cc = cR 3`, `rc = cR 2`); the exact-restore entry
evaluator `RLoop.coreProg` placed with its output cell on the writer's answer cell;
`ClearAll` of `cR 0`, `cR 1`. Each handoff is one charged step. -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.WEntry

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource
open RecursiveLabelCodecScratch RecursiveEntries
open RecursiveSamplingProgram RecursiveSamplingLaws RecursiveRequestCodeShape
open BitMachineRawSequence (leftLabel)
open Paper2.RLoop (JL JE restL readyE coreProg coreStart coreCtl loopBd)

abbrev Aux := JL ⊕ (Fin 5 ⊕ (FetchLabel.Stack ⊕ Fin 2))
abbrev A := Aux ⊕ Fin 3

def cR (i : Fin 5) : A := .inl (.inr (.inl i))
def fS (j : FetchLabel.Stack) : A := .inl (.inr (.inr (.inl j)))
def fwA : A := .inl (.inr (.inr (.inr 0)))
def myA : A := .inl (.inr (.inr (.inr 1)))
def xA : A := .inr 0
def yA : A := .inr 1
def ansA : A := .inr 2

/-! ### Placements -/

def eCf : JE → A
  | .inl a => .inl (.inl a)
  | .inr i => (![cR 0, cR 1, cR 2, cR 3, cR 4, ansA] : Fin 6 → A) i

theorem eCf_injective : Function.Injective eCf := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b
  · simpa [eCf] using h
  · fin_cases b <;> simp [eCf, cR, ansA] at h
  · fin_cases a <;> simp [eCf, cR, ansA] at h
  · fin_cases a <;> fin_cases b <;> first | rfl | (simp [eCf, cR, ansA] at h)

def eC : JE ↪ A := ⟨eCf, eCf_injective⟩

/-- Fetch placement with label cell `cR lb` and index cell `.inr ix`. -/
def eFf (lb : Fin 5) (ix : Fin 3) : FetchIndexed.Stack → A
  | .inl (.inl k) => fS (.inl k)
  | .inl (.inr i) => (![fS (.inr 0), fS (.inr 1), fS (.inr 2), cR lb] : Fin 4 → A) i
  | .inr i => (![fwA, cR 3, cR 2, myA, .inr ix] : Fin 5 → A) i

theorem eFf_injective (lb : Fin 5) (ix : Fin 3) (h2 : lb ≠ 2) (h3 : lb ≠ 3) :
    Function.Injective (eFf lb ix) := by
  intro a b h
  rcases a with (a | a) | a <;> rcases b with (b | b) | b
  · simpa [eFf, fS] using h
  · fin_cases b <;> simp [eFf, fS, cR] at h
  · fin_cases b <;> simp [eFf, fS, cR, fwA, myA] at h
  · fin_cases a <;> simp [eFf, fS, cR] at h
  · fin_cases a <;> fin_cases b <;> first | rfl | (simp [eFf, fS, cR] at h) |
      (exact absurd (Fin.ext_iff.mpr (by simpa [eFf, fS, cR] using h)) (by decide))
  · fin_cases a <;> fin_cases b <;> (try simp [eFf, fS, cR, fwA, myA] at h) <;>
      first | rfl | exact absurd h h2 | exact absurd h h3 | exact absurd h.symm h2 |
        exact absurd h.symm h3
  · fin_cases a <;> simp [eFf, fS, cR, fwA, myA] at h
  · fin_cases a <;> fin_cases b <;> (try simp [eFf, fS, cR, fwA, myA] at h) <;>
      first | rfl | exact absurd h h2 | exact absurd h h3 | exact absurd h.symm h2 |
        exact absurd h.symm h3
  · fin_cases a <;> fin_cases b <;> first | rfl | (simp [eFf, fS, cR, fwA, myA] at h)

def eRow : FetchIndexed.Stack ↪ A := ⟨eFf 0 0, eFf_injective 0 0 (by decide) (by decide)⟩
def eCol : FetchIndexed.Stack ↪ A := ⟨eFf 1 1, eFf_injective 1 1 (by decide) (by decide)⟩

theorem eRow_lbl : eRow SuccessFetchJoin.lblF = cR 0 := rfl
theorem eCol_lbl : eCol SuccessFetchJoin.lblF = cR 1 := rfl

def clCells : Fin 2 → A := ![cR 0, cR 1]

theorem clCells_injective : Function.Injective clCells := by
  intro a b h; fin_cases a <;> fin_cases b <;> first | rfl | (simp [clCells, cR] at h)

/-! ### The program -/

def rowL := fun l => stackStmt eRow (FetchIndexed.rowProgram l)
def colL := fun l => stackStmt eCol (FetchIndexed.colProgram l)
def coreL := fun l => stackStmt eC (coreProg l)

def w1 := BitMachineRawSequence.program rowL colL FetchIndexed.colStart
  FetchIndexed.rowControl FetchIndexed.colControl
def w2 := BitMachineRawSequence.program w1 coreL coreStart
  (FetchIndexed.rowControl, FetchIndexed.colControl) coreCtl
/-- The per-entry program: ONE fixed program. -/
def wprog := BitMachineRawSequence.program w2 (ClearAll.prog clCells) ⟨0, by omega⟩
  ((FetchIndexed.rowControl, FetchIndexed.colControl), coreCtl) (none : Option Bool)
def wStart := FetchIndexed.labelOf wprog (leftLabel (leftLabel (leftLabel FetchIndexed.rowStart)))
def wCtl := (((FetchIndexed.rowControl, FetchIndexed.colControl), coreCtl), (none : Option Bool))

/-! ### Banks -/

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

/-- The serialized column words of the sample, in column order. -/
def colWords (g : EncodedGraph.Graph) (K mY : ℕ)
    (ys : Fin mY → Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K) : List (List Bool) :=
  List.ofFn (fun j => (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q K).2.encode (ys j))

/-- The serialized row words of the sample, in row order. -/
def rowWords (g : EncodedGraph.Graph) (K mX : ℕ)
    (xs : Fin mX → Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K) : List (List Bool) :=
  List.ofFn (fun i => (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q K).1.encode (xs i))

/-- The fixed (entry-independent) part of the writer bank. -/
def auxBank (g : EncodedGraph.Graph) (r K mX mY : ℕ)
    (xs : Fin mX → Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K)
    (ys : Fin mY → Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K) : Aux → List Bool :=
  Sum.elim (restL (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r)
    (Sum.elim
      ![[], [], encodeCode (seedRecursiveCodes g.vertices p s q₁ q₂ w Q K).1,
        encodeCode (seedRecursiveCodes g.vertices p s q₁ q₂ w Q K).2, List.replicate K true]
      (Sum.elim (fun _ => [])
        ![(colWords g K mY ys).flatten ++ (rowWords g K mX xs).flatten, List.replicate mY true]))

def bankA (g : EncodedGraph.Graph) (r K mX mY : ℕ)
    (xs : Fin mX → Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K)
    (ys : Fin mY → Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K) (x y : ℕ) (ans : List Bool) : A → List Bool :=
  Sum.elim (auxBank g r K mX mY xs ys) ![List.replicate x true, List.replicate y true, ans]

/-- The explicit clock of `RLoop.core_run`. -/
def coreBd (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices] (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin g.edges.length) * r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (K : ℕ)
    (x : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q K)
    (y : Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K) : ℕ :=
  let activity := SourceActiveRank.scanAtCanonical (CanonicalEdgeTape.graphEdge g hg)
    (by omega) hq
  let C := defaultCarrierCodecs g.vertices p s q₁ q₂ w Q K
  let c := seedRecursiveCodes g.vertices p s q₁ q₂ w Q K
  let sd := RecursiveEntries.seedRequest activity ξ K x y
  let C0 := defaultCarrierCodecs g.vertices p s q₁ q₂ w Q 0
  let c0 := seedRecursiveCodes g.vertices p s q₁ q₂ w Q 0
  let Lin := (C.1.encode x).length + (C.2.encode y).length + (encodeCode c.1).length +
    (encodeCode c.2).length + K
  let Lout := (encodeCode c0.1).length + (encodeCode c0.2).length + (C0.1.encode sd.1).length +
    (C0.2.encode sd.2).length + 1
  ((5 * (2 * Lin + 3) + 1 +
      (K * (loopBd g hg hs r hq ξ K x y + 2) + 1 + (9 * p + 13) + 1) + 1) +
      (1 * (2 * 1 + 3) + 1) + 1) + (5 * (Lout + 1) + 1) + 1

/-- The explicit per-entry clock: row fetch, column fetch, evaluator, clear, three handoffs. -/
def entryBd (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices] (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin g.edges.length) * r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (K mX mY : ℕ)
    (xs : Fin mX → Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K)
    (ys : Fin mY → Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K) (i : Fin mX) (j : Fin mY) : ℕ :=
  let C := defaultCarrierCodecs g.vertices p s q₁ q₂ w Q K
  let c := seedRecursiveCodes g.vertices p s q₁ q₂ w Q K
  FetchIndexed.rowBound c.2 c.1 (colWords g K mY ys) (rowWords g K mX xs) i.val [] +
    FetchIndexed.colBound c.2 (colWords g K mY ys) j.val (rowWords g K mX xs).flatten +
    coreBd g hg hs r hq ξ K (xs i) (ys j) +
    (2 * ((C.1.encode (xs i)).length + (C.2.encode (ys j)).length + 1) + 1) + 3

/-! ### Lifting lemma -/

theorem liftA {Kk L V : Type*} [DecidableEq Kk] (ι : Kk ↪ A)
    (P : L → TM2.Stmt (fun _ : Kk => Bool) L V)
    (W : A → List Bool) (S T : Kk → List Bool) (hS : ∀ k, S k = W (ι k)) (l : L) (v v' : V)
    (t : ℕ)
    (hrun : ((advance P)^[t]) (⟨some l, v, S⟩ : TM2.Cfg (fun _ : Kk => Bool) L V) =
      ⟨none, v', T⟩) :
    ((advance (fun l => stackStmt ι (P l)))^[t])
        (⟨some l, v, W⟩ : TM2.Cfg (fun _ : A => Bool) L V) =
      ⟨none, v', bank ι W T⟩ := by
  have hs := BitMachineStackRun.run ι W P (⟨some l, v, S⟩ : TM2.Cfg (fun _ : Kk => Bool) L V) t
  rw [hrun] at hs
  simp only [stackCfg] at hs
  rwa [bank_eq_self ι W S hS] at hs

/-! ### The per-entry run -/

theorem entry_run (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hp : 0 < p) (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin g.edges.length) * r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (hfix : ∀ (k : ℕ) (i : SourceConstruction.Items s (Fin g.vertices))
      (js : Fin s → SourceMatrix.OuterColumn q₁ q₂ s (Column (Fin p → Bool) (Fin p)
        (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q k)),
      (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k).2.encode
        (SourceMatrix.sourceColumn (SourceActiveRank.scanAtCanonical
          (CanonicalEdgeTape.graphEdge g hg) (by omega) hq) i
          (SourceMatrix.forgetTag (ξ k) (.fixedTail js))) =
        (CanonicalDefaultWordScratch.words p s q₁ q₂ w Q k).2)
    (K mX mY : ℕ)
    (xs : Fin mX → Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K)
    (ys : Fin mY → Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K) (i : Fin mX) (j : Fin mY) :
    let activity := SourceActiveRank.scanAtCanonical (CanonicalEdgeTape.graphEdge g hg)
      (by omega) hq
    ∃ t ≤ entryBd g hg hs r hq ξ K mX mY xs ys i j, ∃ v,
      ((advance wprog)^[t])
        (⟨some wStart, wCtl, bankA g r K mX mY xs ys i.val j.val []⟩ :
          TM2.Cfg (fun _ : A => Bool) _ _) =
        ⟨none, v, bankA g r K mX mY xs ys i.val j.val
          [RecursiveEntries.matrix (LookupSeed.matrix p) activity ξ K (xs i) (ys j)]⟩ := by
  intro activity
  set C := defaultCarrierCodecs g.vertices p s q₁ q₂ w Q K with hC
  set c := seedRecursiveCodes g.vertices p s q₁ q₂ w Q K with hc
  set cs := colWords g K mY ys with hcs
  set rs := rowWords g K mX xs with hrs
  set W0 := bankA g r K mX mY xs ys i.val j.val [] with hW0
  set b := RecursiveEntries.matrix (LookupSeed.matrix p) activity ξ K (xs i) (ys j) with hb
  have hshape := OutputSkipper.shape_seedRecursiveCodes g.vertices p s q₁ q₂ w Q K (by omega)
  obtain ⟨hfr, hfc⟩ := FullSupport.codes_full (n := g.vertices) (p := p) (s := s) (q₁ := q₁)
    (q₂ := q₂) (w := w) (Q := Q) hp hs K
  have hcsP : ∀ u ∈ cs, Produces (meaning c.2) u := by
    intro u hu
    obtain ⟨jj, rfl⟩ := List.mem_ofFn.mp hu
    exact hfc (ys jj)
  have hrsP : ∀ u ∈ rs, Produces (meaning c.1) u := by
    intro u hu
    obtain ⟨ii, rfl⟩ := List.mem_ofFn.mp hu
    exact hfr (xs ii)
  have hxlen : i.val < rs.length := by simp [hrs, rowWords]
  have hylen : j.val < cs.length := by simp [hcs, colWords]
  have hrget : rs.getD i.val [] = C.1.encode (xs i) := by
    simp [hrs, rowWords, List.getD_eq_getElem?_getD, hC]
  have hcget : cs.getD j.val [] = C.2.encode (ys j) := by
    simp [hcs, colWords, List.getD_eq_getElem?_getD, hC]
  -- (1) the row fetch
  obtain ⟨t1, ht1, v1, r1⟩ := SuccessFetchJoin.lift_row eRow W0 c.2 c.1 hshape.2 hshape.1 cs rs
    hcsP hrsP [] i.val hxlen
    (by
      intro jj
      rcases jj with k | k
      · rfl
      · fin_cases k <;> rfl)
    (by rw [List.append_nil]; rfl) rfl rfl
    (by show List.replicate mY true = List.replicate cs.length true; simp [hcs, colWords]) rfl
  rw [hrget, eRow_lbl] at r1
  set W1 := Function.update W0 (cR 0) (C.1.encode (xs i)) with hW1
  -- (2) the column fetch
  obtain ⟨t2, ht2, v2, r2⟩ := SuccessFetchJoin.lift_col eCol W1 c.2 hshape.2 cs hcsP rs.flatten
    j.val hylen
    (by
      intro jj
      rcases jj with k | k
      · rw [hW1, Function.update_of_ne (by simp [eCol, eFf, fS, cR])]; rfl
      · fin_cases k
        · rw [hW1, Function.update_of_ne (by simp [eCol, eFf, fS, cR])]; rfl
        · rw [hW1, Function.update_of_ne (by simp [eCol, eFf, fS, cR])]; rfl
        · rw [hW1, Function.update_of_ne (by simp [eCol, eFf, fS, cR])]; rfl
        · rw [hW1, Function.update_of_ne (by simp [eCol, eFf, cR])]; rfl)
    (by rw [hW1, Function.update_of_ne (by simp [eCol, eFf, fwA, cR, FetchIndexed.fwC])]; rfl)
    (by rw [hW1, Function.update_of_ne (by simp [eCol, eFf, cR, FetchIndexed.ccC])]; rfl)
    (by rw [hW1, Function.update_of_ne (by simp [eCol, eFf, cR, yA, FetchIndexed.idxC])]; rfl)
  rw [hcget, eCol_lbl] at r2
  set W2 := Function.update W1 (cR 1) (C.2.encode (ys j)) with hW2
  obtain ⟨u1, hu1, s1⟩ := BitMachineRawSequence.runs rowL colL FetchIndexed.rowStart
    FetchIndexed.colStart FetchIndexed.rowControl v1 FetchIndexed.colControl v2 W0 W1 W2
    t1 t2 r1 r2
  -- (3) the evaluator
  obtain ⟨t3, ht3, v3, r3⟩ := Paper2.RLoop.core_run g hg hp hs r hq ξ hfix K (xs i) (ys j)
  have hS3 : ∀ k, readyE (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r
      (C.1.encode (xs i)) (C.2.encode (ys j)) (encodeCode c.1) (encodeCode c.2) K [] k =
      W2 (eC k) := by
    intro k
    rcases k with k | k
    · show restL g r k = W2 (.inl (.inl k))
      rw [hW2, Function.update_of_ne (by simp [cR]), hW1, Function.update_of_ne (by simp [cR])]
      rfl
    · fin_cases k
      · show C.1.encode (xs i) = W2 (cR 0)
        rw [hW2, Function.update_of_ne (by simp [cR]), hW1, Function.update_self]
      · show C.2.encode (ys j) = W2 (cR 1)
        rw [hW2, Function.update_self]
      · show encodeCode c.1 = W2 (cR 2)
        rw [hW2, Function.update_of_ne (by simp [cR]), hW1, Function.update_of_ne (by simp [cR])]
        rfl
      · show encodeCode c.2 = W2 (cR 3)
        rw [hW2, Function.update_of_ne (by simp [cR]), hW1, Function.update_of_ne (by simp [cR])]
        rfl
      · show List.replicate K true = W2 (cR 4)
        rw [hW2, Function.update_of_ne (by simp [cR]), hW1, Function.update_of_ne (by simp [cR])]
        rfl
      · show ([] : List Bool) = W2 ansA
        rw [hW2, Function.update_of_ne (by simp [cR, ansA]), hW1,
          Function.update_of_ne (by simp [cR, ansA])]
        rfl
  have r3L := liftA eC coreProg W2 _ _ hS3 _ _ _ _ r3
  set W3 := bank eC W2 (readyE (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r
      (C.1.encode (xs i)) (C.2.encode (ys j)) (encodeCode c.1) (encodeCode c.2) K [b]) with hW3
  obtain ⟨u2, hu2, s2⟩ := BitMachineRawSequence.runs w1 coreL
    (leftLabel FetchIndexed.rowStart) coreStart (FetchIndexed.rowControl, FetchIndexed.colControl)
    (FetchIndexed.rowControl, v2) coreCtl v3 W0 W2 W3 u1 t3 s1 r3L
  -- (4) clear the two words
  have hW3c0 : W3 (cR 0) = C.1.encode (xs i) := by
    rw [hW3, show cR 0 = eC (.inr 0) from rfl, bank_at]; rfl
  have hW3c1 : W3 (cR 1) = C.2.encode (ys j) := by
    rw [hW3, show cR 1 = eC (.inr 1) from rfl, bank_at]; rfl
  obtain ⟨t4, ht4, v4, r4⟩ := ClearAll.all_run clCells clCells_injective
    ((C.1.encode (xs i)).length + (C.2.encode (ys j)).length) W3
    (by
      intro jj
      fin_cases jj
      · show (W3 (cR 0)).length ≤ _
        rw [hW3c0]; omega
      · show (W3 (cR 1)).length ≤ _
        rw [hW3c1]; omega)
    none
  obtain ⟨u3, hu3, s3⟩ := BitMachineRawSequence.runs w2 (ClearAll.prog clCells)
    (leftLabel (leftLabel FetchIndexed.rowStart)) ⟨0, by omega⟩
    ((FetchIndexed.rowControl, FetchIndexed.colControl), coreCtl)
    ((FetchIndexed.rowControl, FetchIndexed.colControl), v3) none v4 W0 W3 _ u2 t4 s2 r4
  have hfinal : ClearAll.clearFrom clCells 0 W3 = bankA g r K mX mY xs ys i.val j.val [b] := by
    funext a
    rcases a with ((a | (k | (k | k))) | k)
    · rw [Paper2.RLoop.clr_out clCells W3 _ (by intro jj; fin_cases jj <;> simp [clCells, cR]),
        hW3, show (Sum.inl (Sum.inl a) : A) = eC (.inl a) from rfl, bank_at]
      rfl
    · by_cases hk : k.val < 2
      · rw [Paper2.RLoop.clr_in clCells W3 _ ⟨⟨k.val, hk⟩, by
          fin_cases k <;> first | rfl | (simp at hk)⟩]
        fin_cases k <;> first | rfl | (simp at hk)
      · rw [Paper2.RLoop.clr_out clCells W3 _ (by
          intro jj; fin_cases jj <;> fin_cases k <;> simp_all [clCells, cR])]
        fin_cases k
        · simp at hk
        · simp at hk
        · rw [hW3]; exact (bank_at eC W2 _ (.inr 2)).trans rfl
        · rw [hW3]; exact (bank_at eC W2 _ (.inr 3)).trans rfl
        · rw [hW3]; exact (bank_at eC W2 _ (.inr 4)).trans rfl
    · rw [Paper2.RLoop.clr_out clCells W3 _ (by intro jj; fin_cases jj <;> simp [clCells, cR]),
        hW3, bank_outside eC W2 _ _ (by
          rintro ⟨kk, hkk⟩
          rcases kk with kk | kk
          · cases hkk
          · fin_cases kk <;> simp [eC, eCf, cR, ansA] at hkk),
        hW2, Function.update_of_ne (by simp [cR]), hW1, Function.update_of_ne (by simp [cR])]
      rfl
    · rw [Paper2.RLoop.clr_out clCells W3 _ (by intro jj; fin_cases jj <;> simp [clCells, cR]),
        hW3, bank_outside eC W2 _ _ (by
          rintro ⟨kk, hkk⟩
          rcases kk with kk | kk
          · cases hkk
          · fin_cases kk <;> simp [eC, eCf, cR, ansA] at hkk),
        hW2, Function.update_of_ne (by simp [cR]), hW1, Function.update_of_ne (by simp [cR])]
      rfl
    · by_cases h2 : k = 2
      · subst h2
        rw [Paper2.RLoop.clr_out clCells W3 _ (by intro jj; fin_cases jj <;> simp [clCells, cR]),
          hW3, show (Sum.inr 2 : A) = eC (.inr 5) from rfl, bank_at]
        rfl
      · rw [Paper2.RLoop.clr_out clCells W3 _ (by intro jj; fin_cases jj <;> simp [clCells, cR]),
          hW3, bank_outside eC W2 _ _ (by
            rintro ⟨kk, hkk⟩
            rcases kk with kk | kk
            · cases hkk
            · fin_cases kk <;> fin_cases k <;> simp_all [eC, eCf, cR, ansA]),
          hW2, Function.update_of_ne (by simp [cR]), hW1, Function.update_of_ne (by simp [cR])]
        fin_cases k
        · rfl
        · rfl
        · exact absurd rfl h2
  refine ⟨u3, ?_, (((FetchIndexed.rowControl, FetchIndexed.colControl), coreCtl), v4), ?_⟩
  · have hcore : t3 ≤ coreBd g hg hs r hq ξ K (xs i) (ys j) := ht3
    have hE : entryBd g hg hs r hq ξ K mX mY xs ys i j =
        FetchIndexed.rowBound c.2 c.1 cs rs i.val [] +
          FetchIndexed.colBound c.2 cs j.val rs.flatten +
          coreBd g hg hs r hq ξ K (xs i) (ys j) +
          (2 * ((C.1.encode (xs i)).length + (C.2.encode (ys j)).length + 1) + 1) + 3 := rfl
    rw [hE]
    omega
  · rw [← hfinal]; exact s3

end

#print axioms eCf_injective
#print axioms eFf_injective
#print axioms entry_run

end Paper2.WEntry
