import Paper2.FallbackDimsPrinter
import Paper2.FallbackColourSearch

/-! U16 complete branch composition (private, lane owner:a-uniform-clock-2).
ONE fixed program on the ambient bank
`J := (search region) ⊕ ((printer region) ⊕ (unary v cell))`:

1. `alloc`: consumes the public unary `v`, pushing two zero bits per vertex onto the
   counter (every step charged);
2. search: the admitted controller with the fixed predicate `FallbackColourSearch.P`
   (enumeration with carry, access, edge test), inlined on the search region;
3. `dispatch` (one step): reads the physical accept bit and peeks at most two units
   of the public unary `k` (restoring them) and selects the printer:
   three-colourable or `k = 0` -> zero table; `k = 1` -> `[0 1]`; `k ≥ 2` -> identity;
4. print: the F1 composite (dimension producer from `k` + admitted writer) for the
   selected entry program, inlined on the printer region.

The printed word is `rowMajor (FiniteFallbackOutput.fallbackMatrix edge k)`. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Paper2.FallbackBranch

open Turing TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

noncomputable section

/-! ### Entry programs with one common label/control type -/

abbrev CL := FallbackIdentityCell.Label
abbrev CV := FallbackIdentityCell.Control
abbrev CS := MatrixTableWriter.CellStack 2

def zeroCell : CL → TM2.Stmt (fun _ : CS => Bool) CL CV
  | _ => push (.inr 2) (fun _ => false) halt

/-- The admitted `FallbackOutputPrint.oneCell` statement, over two (unused) bank
cells and the common control type (diff recorded in CHECKPOINT.md). -/
def oneCell2 : CL → TM2.Stmt (fun _ : CS => Bool) CL CV
  | _ => pop (.inr 1) (fun s a => (a, s.2.1, s.2.2))
      (pop (.inr 1) (fun s b => (s.1, b, s.2.2))
        (branch (fun s => s.2.1.isSome)
          (push (.inr 1) (fun _ => true) (push (.inr 1) (fun _ => true)
            (push (.inr 2) (fun _ => false) halt)))
          (branch (fun s => s.1.isSome)
            (push (.inr 1) (fun _ => true) (push (.inr 2) (fun _ => true) halt))
            (push (.inr 2) (fun _ => false) halt))))

def cinit : CV := (none, none, false)

theorem cell_ext {x : TM2.Cfg (fun _ : CS => Bool) CL CV} {l : Option CL} {v : CV}
    {x0 y0 : Nat} {ans : List Bool}
    (hl : x.l = l) (hv : x.var = v)
    (hs : ∀ j, x.stk j = (MatrixTableWriter.cellCfg l v (fun _ => []) x0 y0 ans).stk j) :
    x = MatrixTableWriter.cellCfg l v (fun _ => []) x0 y0 ans := by
  cases x with
  | mk l' v' S =>
    simp only at hl hv
    subst hl hv
    have : S = (MatrixTableWriter.cellCfg l' v' (fun _ => []) x0 y0 ans).stk := funext hs
    subst this
    rfl

theorem zeroCell_entryRuns (r c : Nat) :
    MatrixTableWriter.EntryRuns zeroCell .move cinit (fun _ => []) r c 1
      (fun _ _ => false) := by
  intro x _ y _
  refine ⟨1, le_rfl, cinit, ?_⟩
  rw [Function.iterate_one]
  apply cell_ext rfl rfl
  intro j; rcases j with j | j <;> fin_cases j <;> rfl

theorem oneCell2_entryRuns (r c : Nat) :
    MatrixTableWriter.EntryRuns oneCell2 .move cinit (fun _ => []) r c 1
      (fun _ y => decide (y = 1)) := by
  intro x _ y _
  rcases y with _ | _ | y
  · refine ⟨1, le_rfl, (none, none, false), ?_⟩
    rw [Function.iterate_one]
    apply cell_ext rfl rfl
    intro j; rcases j with j | j <;> fin_cases j <;> rfl
  · refine ⟨1, le_rfl, (some true, none, false), ?_⟩
    rw [Function.iterate_one]
    apply cell_ext rfl rfl
    intro j; rcases j with j | j <;> fin_cases j <;> rfl
  · refine ⟨1, le_rfl, (some true, some true, false), ?_⟩
    rw [Function.iterate_one]
    apply cell_ext rfl rfl
    intro j; rcases j with j | j <;> fin_cases j <;> rfl

inductive Mode where
  | zero | one | ident

def cellOf : Mode → CL → TM2.Stmt (fun _ : CS => Bool) CL CV
  | .zero => zeroCell
  | .one => oneCell2
  | .ident => FallbackIdentityCell.eqCell

def printProg (m : Mode) := FallbackDimsPrinter.program (K := 2) (cellOf m) .move cinit

/-! ### Ambient machine -/

abbrev SStack := SamplerMachineSearch.Stack FallbackColourSearch.K
abbrev SLab := SamplerMachineSearch.Label FallbackColourSearch.Lab
abbrev SCtl := SamplerMachineSearch.Control FallbackColourSearch.Ctl
abbrev PStack := FallbackDimsPrinter.Stack 2
abbrev PLab := FallbackDimsPrinter.Lab CL
abbrev PCtl := FallbackDimsPrinter.Ctl CV

abbrev J := SStack ⊕ (PStack ⊕ Unit)

instance instDecSStack : DecidableEq SStack := instDecidableEqSum
instance instDecPStack : DecidableEq PStack := instDecidableEqSum
instance instDecPU : DecidableEq (PStack ⊕ Unit) := instDecidableEqSum
instance instDecJ : DecidableEq J := instDecidableEqSum

inductive Adm where
  | alloc | dispatch

abbrev ALab := Adm ⊕ (SLab ⊕ (Mode × PLab))
abbrev ACtl := SCtl × PCtl × (Option Bool × Option Bool)

def searchProg := SamplerMachineSearch.program FallbackColourSearch.P 0
  FallbackColourSearch.Lab.readA FallbackColourSearch.v0 FallbackColourSearch.Ctl.acc

def sStart : SCtl := (FallbackColourSearch.v0, false, none)
def pStart : PCtl := FallbackDimsPrinter.D0 cinit
def embedS (s : SCtl) : ACtl := (s, pStart, (none, none))
def readS (v : ACtl) : SCtl := v.1
def embedP (p : PCtl) : ACtl := (sStart, p, (none, none))
def readP (v : ACtl) : PCtl := v.2.1

def searchIndex : SStack ↪ J := Function.Embedding.inl
def printIndex : PStack ↪ J := ⟨fun p => .inr (.inl p), by intro a b h; cases h; rfl⟩

def counter : J := .inl (.inl 0)
def vcell : J := .inr (.inr ())
def kcell : J := .inr (.inl (.inl 0))

def program : ALab → TM2.Stmt (fun _ : J => Bool) ALab ACtl
  | .inl .alloc => pop vcell (fun v b => (v.1, v.2.1, (b, none)))
      (branch (fun v => v.2.2.1.isSome)
        (push counter (fun _ => false) (push counter (fun _ => false)
          (load (fun _ => embedS sStart) (goto (fun _ => .inl .alloc)))))
        (load (fun _ => embedS sStart)
          (goto (fun _ => .inr (.inl (.inl FallbackColourSearch.Lab.readA))))))
  | .inl .dispatch => branch (fun v => v.1.1.acc)
      (load (fun _ => embedP pStart) (goto (fun _ => .inr (.inr (.zero, .dec)))))
      (pop kcell (fun v b => (v.1, v.2.1, (b, none)))
        (pop kcell (fun v b => (v.1, v.2.1, (v.2.2.1, b)))
          (branch (fun v => v.2.2.2.isSome)
            (push kcell (fun _ => true) (push kcell (fun _ => true)
              (load (fun _ => embedP pStart) (goto (fun _ => .inr (.inr (.ident, .dec)))))))
            (branch (fun v => v.2.2.1.isSome)
              (push kcell (fun _ => true)
                (load (fun _ => embedP pStart) (goto (fun _ => .inr (.inr (.one, .dec))))))
              (load (fun _ => embedP pStart) (goto (fun _ => .inr (.inr (.zero, .dec)))))))))
  | .inr (.inl l) => BitMachineStackEmbedding.stmt searchIndex (fun l => .inr (.inl l))
      embedS readS (some (.inl .dispatch)) (searchProg l)
  | .inr (.inr (m, l)) => BitMachineStackEmbedding.stmt printIndex
      (fun l => .inr (.inr (m, l))) embedP readP none (printProg m l)

/-- Search-region bank in the admitted controller's own layout. -/
def SA (es : List (Nat × Nat)) (q : List Bool) : SStack → List Bool :=
  Sum.elim (Function.update (FallbackColourSearch.Sbank es) 0 q) (fun _ => [])

def PB (k : Nat) : PStack → List Bool := FallbackDimsPrinter.B (K := 2) k 0 0 0

/-- Start: public unary `v` and `k`, the internal edge tape, everything else empty. -/
def start {v e : Nat} (edge : Fin e → Bool → Fin v) (k : Nat) :
    TM2.Cfg (fun _ : J => Bool) ALab ACtl :=
  ⟨some (.inl .alloc), embedS sStart,
    Sum.elim (SA (FallbackColourSearch.edgeList edge) []) (Sum.elim (PB k)
      (fun _ => List.replicate v true))⟩

theorem acfg_ext {x : TM2.Cfg (fun _ : J => Bool) ALab ACtl} {l : Option ALab} {v : ACtl}
    {S : J → List Bool} (hl : x.l = l) (hv : x.var = v) (hs : ∀ j, x.stk j = S j) :
    x = ⟨l, v, S⟩ := by
  cases x with
  | mk l' v' S' =>
    simp only at hl hv
    subst hl hv
    have : S' = S := funext hs
    subst this
    rfl

abbrev astep := advance program

theorem alloc_cons (es : List (Nat × Nat)) (W : List Bool) (Bp : PStack → List Bool)
    (w : List Bool) :
    astep ⟨some (.inl .alloc), embedS sStart, Sum.elim (SA es W) (Sum.elim Bp (fun _ => true :: w))⟩ =
      ⟨some (.inl .alloc), embedS sStart,
        Sum.elim (SA es (false :: false :: W)) (Sum.elim Bp (fun _ => w))⟩ := by
  apply acfg_ext rfl rfl
  intro j
  rcases j with (j | j) | (j | j)
  · fin_cases j <;> rfl
  · rfl
  · rfl
  · rfl

theorem alloc_nil (es : List (Nat × Nat)) (W : List Bool) (Bp : PStack → List Bool) :
    astep ⟨some (.inl .alloc), embedS sStart, Sum.elim (SA es W) (Sum.elim Bp (fun _ => []))⟩ =
      ⟨some (.inr (.inl (.inl FallbackColourSearch.Lab.readA))), embedS sStart,
        Sum.elim (SA es W) (Sum.elim Bp (fun _ => []))⟩ := by
  apply acfg_ext rfl rfl
  intro j
  rcases j with (j | j) | (j | j)
  · fin_cases j <;> rfl
  · rfl
  · rfl
  · rfl

theorem alloc_loop (es : List (Nat × Nat)) (Bp : PStack → List Bool) (n : Nat) :
    ∀ W : List Bool,
      (astep^[n]) ⟨some (.inl .alloc), embedS sStart,
          Sum.elim (SA es W) (Sum.elim Bp (fun _ => List.replicate n true))⟩ =
        ⟨some (.inl .alloc), embedS sStart,
          Sum.elim (SA es (List.replicate (2 * n) false ++ W)) (Sum.elim Bp (fun _ => []))⟩ := by
  induction n with
  | zero => intro W; rfl
  | succ n ih =>
    intro W
    rw [Function.iterate_succ_apply, List.replicate_succ]
    rw [alloc_cons, ih]
    have e : List.replicate (2 * n) false ++ false :: false :: W =
        List.replicate (2 * (n + 1)) false ++ W := by
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, List.replicate_succ', List.replicate_succ',
        List.append_assoc, List.append_assoc]
      rfl
    rw [e]

theorem bank_inl (A : SStack → List Bool) (X : PStack ⊕ Unit → List Bool)
    (A' : SStack → List Bool) :
    BitMachineStackEmbedding.bank searchIndex (Sum.elim A X) A' = Sum.elim A' X := by
  funext j
  cases j with
  | inl k =>
      simpa only [searchIndex, Sum.elim_inl] using
        (BitMachineStackEmbedding.bank_at searchIndex (Sum.elim A X) A' k)
  | inr k =>
      simpa only [Sum.elim_inr] using
        (BitMachineStackEmbedding.bank_outside searchIndex (Sum.elim A X) A' (Sum.inr k : J)
          (by intro h; obtain ⟨x, hx⟩ := h
              change Sum.inl x = Sum.inr k at hx
              cases hx))

theorem bank_mid (A : SStack → List Bool) (Bp : PStack → List Bool) (C : Unit → List Bool)
    (Bp' : PStack → List Bool) :
    BitMachineStackEmbedding.bank printIndex (Sum.elim A (Sum.elim Bp C)) Bp' =
      Sum.elim A (Sum.elim Bp' C) := by
  funext j
  rcases j with j | (j | j)
  · simpa only [Sum.elim_inl] using
      (BitMachineStackEmbedding.bank_outside printIndex (Sum.elim A (Sum.elim Bp C)) Bp'
        (Sum.inl j : J)
        (by intro h; obtain ⟨x, hx⟩ := h
            change Sum.inr (Sum.inl x) = Sum.inl j at hx
            cases hx))
  · simpa only [Sum.elim_inr, Sum.elim_inl] using
      (BitMachineStackEmbedding.bank_at printIndex (Sum.elim A (Sum.elim Bp C)) Bp' j)
  · simpa only [Sum.elim_inr] using
      (BitMachineStackEmbedding.bank_outside printIndex (Sum.elim A (Sum.elim Bp C)) Bp'
        (Sum.inr (Sum.inr j) : J)
        (by intro h; obtain ⟨x, hx⟩ := h
            change Sum.inr (Sum.inl x) = Sum.inr (Sum.inr j) at hx
            cases hx))

/-- Allocation + search, up to the dispatch label. -/
theorem front {v e : Nat} (edge : Fin e → Bool → Fin v) (k : Nat) :
    ∃ t ≤ (v + 1) + 2 ^ (2 * v) * (FallbackColourSearch.T edge + 4 * (2 * v) + 6),
      ∃ (vc : FallbackColourSearch.Ctl) (flag : Bool) (q' : List Bool),
        vc.acc = decide (FiniteFallbackOutput.ThreeColourable edge) ∧
        (astep^[t]) (start edge k) =
          ⟨some (.inl .dispatch), embedS (vc, flag, none),
            Sum.elim (SA (FallbackColourSearch.edgeList edge) q')
              (Sum.elim (PB k) (fun _ => []))⟩ := by
  obtain ⟨ts, vc, flag, q', hts, hacc, hrun⟩ := FallbackColourSearch.search_decides edge
  have ha := alloc_loop (FallbackColourSearch.edgeList edge) (PB k) v []
  simp only [List.append_nil] at ha
  have hb := alloc_nil (FallbackColourSearch.edgeList edge) (List.replicate (2 * v) false) (PB k)
  let c0 : TM2.Cfg (fun _ : SStack => Bool) SLab SCtl :=
    SamplerMachineSearch.cfg 0 (FallbackColourSearch.Sbank (FallbackColourSearch.edgeList edge))
      (some (.inl FallbackColourSearch.Lab.readA)) sStart (List.replicate (2 * v) false) []
  obtain ⟨n, hn, hs⟩ := BitMachineStackEmbedding.outputs searchIndex
    (Sum.elim (SA (FallbackColourSearch.edgeList edge) (List.replicate (2 * v) false))
      (Sum.elim (PB k) (fun _ => [])))
    (fun l => .inr (.inl l)) embedS readS (fun _ => rfl) (some (.inl .dispatch))
    searchProg program (fun _ => rfl) c0 ts (by exact congrArg TM2.Cfg.l hrun)
  change ((advance program)^[n]) (BitMachineStackEmbedding.cfg searchIndex _ _ embedS _ c0) =
    BitMachineStackEmbedding.cfg searchIndex _ _ embedS _
      (SamplerMachineSearch.run FallbackColourSearch.P 0 FallbackColourSearch.Lab.readA
        FallbackColourSearch.v0 FallbackColourSearch.Ctl.acc ts c0) at hs
  rw [show c0 = SamplerMachineSearch.cfg 0
      (FallbackColourSearch.Sbank (FallbackColourSearch.edgeList edge))
      (some (.inl FallbackColourSearch.Lab.readA)) (FallbackColourSearch.v0, false, none)
      (List.replicate (2 * v) false) [] from rfl, hrun] at hs
  refine ⟨n + 1 + v, ?_, vc, flag, q', hacc, ?_⟩
  · omega
  · rw [Function.iterate_add_apply, Function.iterate_add_apply]
    have hstart : start edge k = ⟨some (.inl .alloc), embedS sStart,
        Sum.elim (SA (FallbackColourSearch.edgeList edge) [])
          (Sum.elim (PB k) (fun _ => List.replicate v true))⟩ := rfl
    rw [hstart, ha, Function.iterate_one, hb]
    have hc : (⟨some (.inr (.inl (.inl FallbackColourSearch.Lab.readA))), embedS sStart,
        Sum.elim (SA (FallbackColourSearch.edgeList edge) (List.replicate (2 * v) false))
          (Sum.elim (PB k) (fun _ => []))⟩ : TM2.Cfg (fun _ : J => Bool) ALab ACtl) =
        BitMachineStackEmbedding.cfg searchIndex
          (Sum.elim (SA (FallbackColourSearch.edgeList edge) (List.replicate (2 * v) false))
            (Sum.elim (PB k) (fun _ => [])))
          (fun l => .inr (.inl l)) embedS (some (.inl .dispatch)) c0 := by
      simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
        BitMachineInline.cfg, c0, SamplerMachineSearch.cfg, bank_inl]
      rfl
    rw [hc]
    refine hs.trans ?_
    simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, SamplerMachineSearch.cfg, bank_inl]
    rfl

/-- The printer stage for mode `m`, from the F1 run theorem. -/
theorem print_stage (m : Mode) (A : SStack → List Bool) (k T : Nat) (entry : Nat → Nat → Bool)
    (f : Fin (FiniteFallbackOutput.rows k) → Fin (FiniteFallbackOutput.cols k) → Bool)
    (hf : ∀ x y, entry x.val y.val = f x y)
    (hcell : MatrixTableWriter.EntryRuns (cellOf m) .move cinit (fun _ => [])
      (FiniteFallbackOutput.rows k) (FiniteFallbackOutput.cols k) T entry) :
    ∃ t ≤ FallbackDimsPrinter.dimsClock k + MatrixTableWriter.writerBound
        (FiniteFallbackOutput.rows k) (FiniteFallbackOutput.cols k) T, ∃ ctl : ACtl,
      (astep^[t]) ⟨some (.inr (.inr (m, .dec))), embedP pStart,
          Sum.elim A (Sum.elim (PB k) (fun _ => []))⟩ =
        ⟨none, ctl, Sum.elim A (Sum.elim (Sum.elim (FallbackDimsPrinter.pbank k 0)
          (MatrixTableWriter.ready (fun _ => []) (FiniteFallbackOutput.rows k)
            (FiniteFallbackOutput.cols k) 0 0 0 0 []
            (MatrixMaterialization.rowMajor f)).contents) (fun _ => []))⟩ := by
  obtain ⟨tp, htp, w, hp⟩ := FallbackDimsPrinter.print_from_k (cellOf m) .move cinit k T
    entry f hf hcell
  obtain ⟨n, hn, hs⟩ := BitMachineStackEmbedding.outputs printIndex
    (Sum.elim A (Sum.elim (PB k) (fun _ => [])))
    (fun l => .inr (.inr (m, l))) embedP readP (fun _ => rfl) none
    (printProg m) program (fun _ => rfl) (FallbackDimsPrinter.startCfg cinit k) tp (by
      have h2 := congrArg TM2.Cfg.l hp
      simpa [printProg] using h2)
  change ((advance program)^[n]) (BitMachineStackEmbedding.cfg printIndex _ _ embedP _ _) =
    BitMachineStackEmbedding.cfg printIndex _ _ embedP _
      (((advance (printProg m))^[tp]) (FallbackDimsPrinter.startCfg cinit k)) at hs
  rw [show printProg m = FallbackDimsPrinter.program (K := 2) (cellOf m) .move cinit from rfl,
    hp] at hs
  refine ⟨n, hn.trans htp, embedP (FallbackDimsPrinter.embedWriter w), ?_⟩
  simpa only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, bank_mid, FallbackDimsPrinter.startCfg, PB, pStart] using hs

/-! ### Dispatch (one charged step) -/

abbrev bankD (es : List (Nat × Nat)) (q' : List Bool) (k : Nat) : J → List Bool :=
  Sum.elim (SA es q') (Sum.elim (PB k) (fun _ => []))

theorem dispatch_acc (es : List (Nat × Nat)) (q' : List Bool) (k : Nat)
    (vc : FallbackColourSearch.Ctl) (flag : Bool) (hv : vc.acc = true) :
    astep ⟨some (.inl .dispatch), embedS (vc, flag, none), bankD es q' k⟩ =
      ⟨some (.inr (.inr (.zero, .dec))), embedP pStart, bankD es q' k⟩ := by
  obtain ⟨ca, same, acc, t1, t2, t3⟩ := vc
  simp only at hv
  subst hv
  apply acfg_ext rfl rfl
  intro j; rfl

theorem dispatch_k0 (es : List (Nat × Nat)) (q' : List Bool)
    (vc : FallbackColourSearch.Ctl) (flag : Bool) (hv : vc.acc = false) :
    astep ⟨some (.inl .dispatch), embedS (vc, flag, none), bankD es q' 0⟩ =
      ⟨some (.inr (.inr (.zero, .dec))), embedP pStart, bankD es q' 0⟩ := by
  obtain ⟨ca, same, acc, t1, t2, t3⟩ := vc
  simp only at hv
  subst hv
  apply acfg_ext rfl rfl
  intro j
  rcases j with (j | j) | ((j | j) | j)
  · rfl
  · rfl
  · fin_cases j <;> rfl
  · rfl
  · rfl

theorem dispatch_k1 (es : List (Nat × Nat)) (q' : List Bool)
    (vc : FallbackColourSearch.Ctl) (flag : Bool) (hv : vc.acc = false) :
    astep ⟨some (.inl .dispatch), embedS (vc, flag, none), bankD es q' 1⟩ =
      ⟨some (.inr (.inr (.one, .dec))), embedP pStart, bankD es q' 1⟩ := by
  obtain ⟨ca, same, acc, t1, t2, t3⟩ := vc
  simp only at hv
  subst hv
  apply acfg_ext rfl rfl
  intro j
  rcases j with (j | j) | ((j | j) | j)
  · rfl
  · rfl
  · fin_cases j <;> rfl
  · rfl
  · rfl

theorem dispatch_k2 (es : List (Nat × Nat)) (q' : List Bool) (i : Nat)
    (vc : FallbackColourSearch.Ctl) (flag : Bool) (hv : vc.acc = false) :
    astep ⟨some (.inl .dispatch), embedS (vc, flag, none), bankD es q' (i + 2)⟩ =
      ⟨some (.inr (.inr (.ident, .dec))), embedP pStart, bankD es q' (i + 2)⟩ := by
  obtain ⟨ca, same, acc, t1, t2, t3⟩ := vc
  simp only at hv
  subst hv
  apply acfg_ext rfl rfl
  intro j
  rcases j with (j | j) | ((j | j) | j)
  · rfl
  · rfl
  · fin_cases j <;> rfl
  · rfl
  · rfl

/-- U16 complete branch: allocate, enumerate with carry, access and test, decide,
dispatch, produce the dimension words and print; one fixed program, every step
charged, total clock a function of `v`, `e`, `k` only. -/
theorem fallback_branch_run {v e : Nat} (edge : Fin e → Bool → Fin v) (k : Nat) :
    ∃ t ≤ (v + 1) + 2 ^ (2 * v) * (FallbackColourSearch.T edge + 4 * (2 * v) + 6) + 1 +
        2 ^ (3 * k + 15),
      ∃ (ctl : ACtl) (q' : List Bool),
        (astep^[t]) (start edge k) =
          ⟨none, ctl, Sum.elim (SA (FallbackColourSearch.edgeList edge) q')
            (Sum.elim (Sum.elim (FallbackDimsPrinter.pbank k 0)
              (MatrixTableWriter.ready (fun _ => []) (FiniteFallbackOutput.rows k)
                (FiniteFallbackOutput.cols k) 0 0 0 0 []
                (MatrixMaterialization.rowMajor
                  (FiniteFallbackOutput.fallbackMatrix edge k))).contents) (fun _ => []))⟩ := by
  obtain ⟨t1, ht1, vc, flag, q', hacc, h1⟩ := front edge k
  have finish : ∀ (m : Mode) (T : Nat) (entry : Nat → Nat → Bool),
      T ≤ 3 * 2 ^ k + 3 →
      (∀ x y, entry x.val y.val = FiniteFallbackOutput.fallbackMatrix edge k x y) →
      MatrixTableWriter.EntryRuns (cellOf m) .move cinit (fun _ => [])
        (FiniteFallbackOutput.rows k) (FiniteFallbackOutput.cols k) T entry →
      astep ⟨some (.inl .dispatch), embedS (vc, flag, none),
          bankD (FallbackColourSearch.edgeList edge) q' k⟩ =
        ⟨some (.inr (.inr (m, .dec))), embedP pStart,
          bankD (FallbackColourSearch.edgeList edge) q' k⟩ →
      ∃ t ≤ (v + 1) + 2 ^ (2 * v) * (FallbackColourSearch.T edge + 4 * (2 * v) + 6) + 1 +
          2 ^ (3 * k + 15),
        ∃ (ctl : ACtl) (q' : List Bool),
          (astep^[t]) (start edge k) =
            ⟨none, ctl, Sum.elim (SA (FallbackColourSearch.edgeList edge) q')
              (Sum.elim (Sum.elim (FallbackDimsPrinter.pbank k 0)
                (MatrixTableWriter.ready (fun _ => []) (FiniteFallbackOutput.rows k)
                  (FiniteFallbackOutput.cols k) 0 0 0 0 []
                  (MatrixMaterialization.rowMajor
                    (FiniteFallbackOutput.fallbackMatrix edge k))).contents) (fun _ => []))⟩ := by
    intro m T entry hT hf hcell hd
    obtain ⟨t3, ht3, ctl, h3⟩ := print_stage m (SA (FallbackColourSearch.edgeList edge) q') k T
      entry (FiniteFallbackOutput.fallbackMatrix edge k) hf hcell
    have hpc := FallbackDimsPrinter.print_clock_le k T hT
    refine ⟨t3 + 1 + t1, by omega, ctl, q', ?_⟩
    rw [Function.iterate_add_apply, Function.iterate_add_apply, h1, Function.iterate_one, hd, h3]
  by_cases h : FiniteFallbackOutput.ThreeColourable edge
  · have hv : vc.acc = true := by rw [hacc]; simpa using h
    have hfm : FiniteFallbackOutput.fallbackMatrix edge k = fun _ _ => false := by
      unfold FiniteFallbackOutput.fallbackMatrix; exact if_pos h
    exact finish .zero 1 (fun _ _ => false) (by omega) (by intro x y; rw [hfm])
      (zeroCell_entryRuns _ _) (dispatch_acc _ _ _ vc flag hv)
  · have hv : vc.acc = false := by rw [hacc]; simpa using h
    have hfm : FiniteFallbackOutput.fallbackMatrix edge k = FiniteFallbackOutput.hardMatrix k := by
      unfold FiniteFallbackOutput.fallbackMatrix; exact if_neg h
    rcases k with _ | _ | i
    · exact finish .zero 1 (fun _ _ => false) (by omega) (by intro x y; rw [hfm]; rfl)
        (zeroCell_entryRuns _ _) (dispatch_k0 _ _ vc flag hv)
    · exact finish .one 1 (fun _ y => decide (y = 1)) (by omega)
        (by intro x y; rw [hfm]; exact decide_eq_decide.mpr ⟨fun h => Fin.ext h, fun h => h ▸ rfl⟩)
        (oneCell2_entryRuns _ _) (dispatch_k1 _ _ vc flag hv)
    · have hcell := FallbackIdentityCell.eqCell_entryRuns (2 ^ (i + 1)) (2 ^ (i + 1))
      rw [FallbackDimsPrinter.bank2_eq] at hcell
      have hT : 3 * 2 ^ (i + 1) + 3 ≤ 3 * 2 ^ (i + 2) + 3 := by
        have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show i + 1 ≤ i + 2 by omega)
        omega
      exact finish .ident (3 * 2 ^ (i + 1) + 3) (fun x y => decide (x = y)) hT
        (by intro x y; rw [hfm]; exact decide_eq_decide.mpr Fin.val_inj)
        hcell (dispatch_k2 _ _ i vc flag hv)

/-- The same clock as an explicit function of `v`, `e`, `k`. -/
theorem fallback_branch_clock {v e : Nat} (edge : Fin e → Bool → Fin v) (k : Nat) :
    (v + 1) + 2 ^ (2 * v) * (FallbackColourSearch.T edge + 4 * (2 * v) + 6) + 1 +
        2 ^ (3 * k + 15) ≤
      (v + 2) + 4 ^ v * (10 * (e + 1) * (v + 1)) + 2 ^ (3 * k + 15) := by
  have := FallbackColourSearch.search_clock_le edge
  omega

/-- The printed matrix is the ledger's scanned fallback matrix. -/
theorem printed_eq_scanned {v e : Nat} (edge : Fin e → Bool → Fin v) (k : Nat) :
    MatrixMaterialization.rowMajor (FiniteFallbackOutput.fallbackMatrix edge k) =
      MatrixMaterialization.rowMajor
        (FiniteFallbackSearchScratch.scannedFallbackMatrix edge k) := by
  rw [FiniteFallbackSearchScratch.scannedFallbackMatrix_eq]

#print axioms dispatch_acc
#print axioms dispatch_k0
#print axioms dispatch_k1
#print axioms dispatch_k2
#print axioms fallback_branch_run
#print axioms fallback_branch_clock
#print axioms printed_eq_scanned

#print axioms zeroCell_entryRuns
#print axioms oneCell2_entryRuns
#print axioms alloc_loop
#print axioms front
#print axioms print_stage

end

end Paper2.FallbackBranch
