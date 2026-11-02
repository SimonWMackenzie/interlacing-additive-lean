import Paper2.FallbackBranch
import Paper2.TernaryColourSearch

/-! U16 complete branch with the LITERAL ternary counter (private, lane
owner:a-uniform-clock-2). The same fixed composition as `FallbackBranch`
(allocation of the v-digit all-zero counter from unary `v`, search, one-step
dispatch, F1 dimension production and printing), with the search replaced by
the ternary first-success controller `TernaryColourSearch.tprog`, which
enumerates exactly the `3^v` colourings with carry. Entry programs, bank
layout, embeddings and bank lemmas are reused from `FallbackBranch` by name. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Paper2.FallbackBranchT

open Turing TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

noncomputable section

abbrev ALab := FallbackBranch.Adm ⊕ (TernaryColourSearch.TLab ⊕ (FallbackBranch.Mode × FallbackBranch.PLab))
abbrev ACtl := TernaryColourSearch.TCtl × FallbackBranch.PCtl × (Option Bool × Option Bool)

def sStart : TernaryColourSearch.TCtl := (FallbackColourSearch.v0, false, none, none)
def embedS (s : TernaryColourSearch.TCtl) : ACtl := (s, FallbackBranch.pStart, (none, none))
def readS (v : ACtl) : TernaryColourSearch.TCtl := v.1
def embedP (p : FallbackBranch.PCtl) : ACtl := (sStart, p, (none, none))
def readP (v : ACtl) : FallbackBranch.PCtl := v.2.1

def program : ALab → TM2.Stmt (fun _ : FallbackBranch.J => Bool) ALab ACtl
  | .inl .alloc => pop FallbackBranch.vcell (fun v b => (v.1, v.2.1, (b, none)))
      (branch (fun v => v.2.2.1.isSome)
        (push FallbackBranch.counter (fun _ => false) (push FallbackBranch.counter (fun _ => false)
          (load (fun _ => embedS sStart) (goto (fun _ => .inl .alloc)))))
        (load (fun _ => embedS sStart)
          (goto (fun _ => .inr (.inl (.inl FallbackColourSearch.Lab.readA))))))
  | .inl .dispatch => branch (fun v => v.1.1.acc)
      (load (fun _ => embedP FallbackBranch.pStart) (goto (fun _ => .inr (.inr (.zero, .dec)))))
      (pop FallbackBranch.kcell (fun v b => (v.1, v.2.1, (b, none)))
        (pop FallbackBranch.kcell (fun v b => (v.1, v.2.1, (v.2.2.1, b)))
          (branch (fun v => v.2.2.2.isSome)
            (push FallbackBranch.kcell (fun _ => true) (push FallbackBranch.kcell (fun _ => true)
              (load (fun _ => embedP FallbackBranch.pStart) (goto (fun _ => .inr (.inr (.ident, .dec)))))))
            (branch (fun v => v.2.2.1.isSome)
              (push FallbackBranch.kcell (fun _ => true)
                (load (fun _ => embedP FallbackBranch.pStart) (goto (fun _ => .inr (.inr (.one, .dec))))))
              (load (fun _ => embedP FallbackBranch.pStart) (goto (fun _ => .inr (.inr (.zero, .dec)))))))))
  | .inr (.inl l) => BitMachineStackEmbedding.stmt FallbackBranch.searchIndex (fun l => .inr (.inl l))
      embedS readS (some (.inl .dispatch)) (TernaryColourSearch.tprog l)
  | .inr (.inr (m, l)) => BitMachineStackEmbedding.stmt FallbackBranch.printIndex
      (fun l => .inr (.inr (m, l))) embedP readP none (FallbackBranch.printProg m l)

/-- Start: public unary `v` and `k`, the internal edge tape, everything else empty. -/
def start {v e : Nat} (edge : Fin e → Bool → Fin v) (k : Nat) :
    TM2.Cfg (fun _ : FallbackBranch.J => Bool) ALab ACtl :=
  ⟨some (.inl .alloc), embedS sStart,
    Sum.elim (FallbackBranch.SA (FallbackColourSearch.edgeList edge) []) (Sum.elim (FallbackBranch.PB k)
      (fun _ => List.replicate v true))⟩

theorem acfg_ext {x : TM2.Cfg (fun _ : FallbackBranch.J => Bool) ALab ACtl} {l : Option ALab} {v : ACtl}
    {S : FallbackBranch.J → List Bool} (hl : x.l = l) (hv : x.var = v) (hs : ∀ j, x.stk j = S j) :
    x = ⟨l, v, S⟩ := by
  cases x with
  | mk l' v' S' =>
    simp only at hl hv
    subst hl hv
    have : S' = S := funext hs
    subst this
    rfl

abbrev astep := advance program

theorem alloc_cons (es : List (Nat × Nat)) (W : List Bool) (Bp : FallbackBranch.PStack → List Bool)
    (w : List Bool) :
    astep ⟨some (.inl .alloc), embedS sStart, Sum.elim (FallbackBranch.SA es W) (Sum.elim Bp (fun _ => true :: w))⟩ =
      ⟨some (.inl .alloc), embedS sStart,
        Sum.elim (FallbackBranch.SA es (false :: false :: W)) (Sum.elim Bp (fun _ => w))⟩ := by
  apply acfg_ext rfl rfl
  intro j
  rcases j with (j | j) | (j | j)
  · fin_cases j <;> rfl
  · rfl
  · rfl
  · rfl

theorem alloc_nil (es : List (Nat × Nat)) (W : List Bool) (Bp : FallbackBranch.PStack → List Bool) :
    astep ⟨some (.inl .alloc), embedS sStart, Sum.elim (FallbackBranch.SA es W) (Sum.elim Bp (fun _ => []))⟩ =
      ⟨some (.inr (.inl (.inl FallbackColourSearch.Lab.readA))), embedS sStart,
        Sum.elim (FallbackBranch.SA es W) (Sum.elim Bp (fun _ => []))⟩ := by
  apply acfg_ext rfl rfl
  intro j
  rcases j with (j | j) | (j | j)
  · fin_cases j <;> rfl
  · rfl
  · rfl
  · rfl

theorem alloc_loop (es : List (Nat × Nat)) (Bp : FallbackBranch.PStack → List Bool) (n : Nat) :
    ∀ W : List Bool,
      (astep^[n]) ⟨some (.inl .alloc), embedS sStart,
          Sum.elim (FallbackBranch.SA es W) (Sum.elim Bp (fun _ => List.replicate n true))⟩ =
        ⟨some (.inl .alloc), embedS sStart,
          Sum.elim (FallbackBranch.SA es (List.replicate (2 * n) false ++ W)) (Sum.elim Bp (fun _ => []))⟩ := by
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

/-- Allocation + ternary search, up to the dispatch label. -/
theorem front {v e : Nat} (edge : Fin e → Bool → Fin v) (k : Nat) :
    ∃ t ≤ (v + 1) + 3 ^ v * (FallbackColourSearch.T edge + 3 * v + 4),
      ∃ (vc : FallbackColourSearch.Ctl) (flag : Bool) (q' : List Bool),
        vc.acc = decide (FiniteFallbackOutput.ThreeColourable edge) ∧
        (astep^[t]) (start edge k) =
          ⟨some (.inl .dispatch), embedS (vc, flag, none, none),
            Sum.elim (FallbackBranch.SA (FallbackColourSearch.edgeList edge) q')
              (Sum.elim (FallbackBranch.PB k) (fun _ => []))⟩ := by
  obtain ⟨ts, hts, vc, flag, q', hrun, hacc⟩ := TernaryColourSearch.ternary_search_decides edge
  have hz : FallbackColourSearch.colWord (List.replicate v 0) = List.replicate (2 * v) false := by
    simpa [FallbackColourSearch.colWord] using TernaryColourSearch.colWord_replicate_zero v []
  rw [hz] at hrun
  have ha := alloc_loop (FallbackColourSearch.edgeList edge) (FallbackBranch.PB k) v []
  simp only [List.append_nil] at ha
  have hb := alloc_nil (FallbackColourSearch.edgeList edge) (List.replicate (2 * v) false)
    (FallbackBranch.PB k)
  let c0 : TM2.Cfg (fun _ : TernaryColourSearch.TK => Bool) TernaryColourSearch.TLab
      TernaryColourSearch.TCtl :=
    ⟨some (.inl FallbackColourSearch.Lab.readA), sStart,
      TernaryColourSearch.tb (FallbackColourSearch.edgeList edge) (List.replicate (2 * v) false) []⟩
  obtain ⟨n, hn, hs⟩ := BitMachineStackEmbedding.outputs FallbackBranch.searchIndex
    (Sum.elim (FallbackBranch.SA (FallbackColourSearch.edgeList edge) (List.replicate (2 * v) false))
      (Sum.elim (FallbackBranch.PB k) (fun _ => [])))
    (fun l => .inr (.inl l)) embedS readS (fun _ => rfl) (some (.inl .dispatch))
    TernaryColourSearch.tprog program (fun _ => rfl) c0 ts (by exact congrArg TM2.Cfg.l hrun)
  change ((advance program)^[n]) (BitMachineStackEmbedding.cfg FallbackBranch.searchIndex _ _ embedS _ c0) =
    BitMachineStackEmbedding.cfg FallbackBranch.searchIndex _ _ embedS _
      ((TernaryColourSearch.tstep^[ts]) c0) at hs
  rw [show c0 = ⟨some (.inl FallbackColourSearch.Lab.readA), (FallbackColourSearch.v0, false, none, none),
      TernaryColourSearch.tb (FallbackColourSearch.edgeList edge) (List.replicate (2 * v) false) []⟩
      from rfl, hrun] at hs
  refine ⟨n + 1 + v, ?_, vc, flag, q', hacc, ?_⟩
  · omega
  · rw [Function.iterate_add_apply, Function.iterate_add_apply]
    have hstart : start edge k = ⟨some (.inl .alloc), embedS sStart,
        Sum.elim (FallbackBranch.SA (FallbackColourSearch.edgeList edge) [])
          (Sum.elim (FallbackBranch.PB k) (fun _ => List.replicate v true))⟩ := rfl
    rw [hstart, ha, Function.iterate_one, hb]
    have hc : (⟨some (.inr (.inl (.inl FallbackColourSearch.Lab.readA))), embedS sStart,
        Sum.elim (FallbackBranch.SA (FallbackColourSearch.edgeList edge) (List.replicate (2 * v) false))
          (Sum.elim (FallbackBranch.PB k) (fun _ => []))⟩ : TM2.Cfg (fun _ : FallbackBranch.J => Bool) ALab ACtl) =
        BitMachineStackEmbedding.cfg FallbackBranch.searchIndex
          (Sum.elim (FallbackBranch.SA (FallbackColourSearch.edgeList edge) (List.replicate (2 * v) false))
            (Sum.elim (FallbackBranch.PB k) (fun _ => [])))
          (fun l => .inr (.inl l)) embedS (some (.inl .dispatch)) c0 := by
      simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
        BitMachineInline.cfg, c0, TernaryColourSearch.tb, FallbackBranch.bank_inl]
      rfl
    rw [hc]
    refine hs.trans ?_
    simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, TernaryColourSearch.tb, FallbackBranch.bank_inl]
    rfl

/-- The printer stage for mode `m`, from the F1 run theorem. -/
theorem print_stage (m : FallbackBranch.Mode) (A : FallbackBranch.SStack → List Bool) (k T : Nat) (entry : Nat → Nat → Bool)
    (f : Fin (FiniteFallbackOutput.rows k) → Fin (FiniteFallbackOutput.cols k) → Bool)
    (hf : ∀ x y, entry x.val y.val = f x y)
    (hcell : MatrixTableWriter.EntryRuns (FallbackBranch.cellOf m) .move FallbackBranch.cinit (fun _ => [])
      (FiniteFallbackOutput.rows k) (FiniteFallbackOutput.cols k) T entry) :
    ∃ t ≤ FallbackDimsPrinter.dimsClock k + MatrixTableWriter.writerBound
        (FiniteFallbackOutput.rows k) (FiniteFallbackOutput.cols k) T, ∃ ctl : ACtl,
      (astep^[t]) ⟨some (.inr (.inr (m, .dec))), embedP FallbackBranch.pStart,
          Sum.elim A (Sum.elim (FallbackBranch.PB k) (fun _ => []))⟩ =
        ⟨none, ctl, Sum.elim A (Sum.elim (Sum.elim (FallbackDimsPrinter.pbank k 0)
          (MatrixTableWriter.ready (fun _ => []) (FiniteFallbackOutput.rows k)
            (FiniteFallbackOutput.cols k) 0 0 0 0 []
            (MatrixMaterialization.rowMajor f)).contents) (fun _ => []))⟩ := by
  obtain ⟨tp, htp, w, hp⟩ := FallbackDimsPrinter.print_from_k (FallbackBranch.cellOf m) .move FallbackBranch.cinit k T
    entry f hf hcell
  obtain ⟨n, hn, hs⟩ := BitMachineStackEmbedding.outputs FallbackBranch.printIndex
    (Sum.elim A (Sum.elim (FallbackBranch.PB k) (fun _ => [])))
    (fun l => .inr (.inr (m, l))) embedP readP (fun _ => rfl) none
    (FallbackBranch.printProg m) program (fun _ => rfl) (FallbackDimsPrinter.startCfg FallbackBranch.cinit k) tp (by
      have h2 := congrArg TM2.Cfg.l hp
      simpa [FallbackBranch.printProg] using h2)
  change ((advance program)^[n]) (BitMachineStackEmbedding.cfg FallbackBranch.printIndex _ _ embedP _ _) =
    BitMachineStackEmbedding.cfg FallbackBranch.printIndex _ _ embedP _
      (((advance (FallbackBranch.printProg m))^[tp]) (FallbackDimsPrinter.startCfg FallbackBranch.cinit k)) at hs
  rw [show FallbackBranch.printProg m = FallbackDimsPrinter.program (K := 2) (FallbackBranch.cellOf m) .move FallbackBranch.cinit from rfl,
    hp] at hs
  refine ⟨n, hn.trans htp, embedP (FallbackDimsPrinter.embedWriter w), ?_⟩
  simpa only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, FallbackBranch.bank_mid, FallbackDimsPrinter.startCfg, FallbackBranch.PB, FallbackBranch.pStart] using hs

/-! ### Dispatch (one charged step) -/

abbrev bankD (es : List (Nat × Nat)) (q' : List Bool) (k : Nat) : FallbackBranch.J → List Bool :=
  Sum.elim (FallbackBranch.SA es q') (Sum.elim (FallbackBranch.PB k) (fun _ => []))

theorem dispatch_acc (es : List (Nat × Nat)) (q' : List Bool) (k : Nat)
    (vc : FallbackColourSearch.Ctl) (flag : Bool) (hv : vc.acc = true) :
    astep ⟨some (.inl .dispatch), embedS (vc, flag, none, none), bankD es q' k⟩ =
      ⟨some (.inr (.inr (.zero, .dec))), embedP FallbackBranch.pStart, bankD es q' k⟩ := by
  obtain ⟨ca, same, acc, t1, t2, t3⟩ := vc
  simp only at hv
  subst hv
  apply acfg_ext rfl rfl
  intro j; rfl

theorem dispatch_k0 (es : List (Nat × Nat)) (q' : List Bool)
    (vc : FallbackColourSearch.Ctl) (flag : Bool) (hv : vc.acc = false) :
    astep ⟨some (.inl .dispatch), embedS (vc, flag, none, none), bankD es q' 0⟩ =
      ⟨some (.inr (.inr (.zero, .dec))), embedP FallbackBranch.pStart, bankD es q' 0⟩ := by
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
    astep ⟨some (.inl .dispatch), embedS (vc, flag, none, none), bankD es q' 1⟩ =
      ⟨some (.inr (.inr (.one, .dec))), embedP FallbackBranch.pStart, bankD es q' 1⟩ := by
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
    astep ⟨some (.inl .dispatch), embedS (vc, flag, none, none), bankD es q' (i + 2)⟩ =
      ⟨some (.inr (.inr (.ident, .dec))), embedP FallbackBranch.pStart, bankD es q' (i + 2)⟩ := by
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
theorem fallback_branch_run_ternary {v e : Nat} (edge : Fin e → Bool → Fin v) (k : Nat) :
    ∃ t ≤ (v + 1) + 3 ^ v * (FallbackColourSearch.T edge + 3 * v + 4) + 1 +
        2 ^ (3 * k + 15),
      ∃ (ctl : ACtl) (q' : List Bool),
        (astep^[t]) (start edge k) =
          ⟨none, ctl, Sum.elim (FallbackBranch.SA (FallbackColourSearch.edgeList edge) q')
            (Sum.elim (Sum.elim (FallbackDimsPrinter.pbank k 0)
              (MatrixTableWriter.ready (fun _ => []) (FiniteFallbackOutput.rows k)
                (FiniteFallbackOutput.cols k) 0 0 0 0 []
                (MatrixMaterialization.rowMajor
                  (FiniteFallbackOutput.fallbackMatrix edge k))).contents) (fun _ => []))⟩ := by
  obtain ⟨t1, ht1, vc, flag, q', hacc, h1⟩ := front edge k
  have finish : ∀ (m : FallbackBranch.Mode) (T : Nat) (entry : Nat → Nat → Bool),
      T ≤ 3 * 2 ^ k + 3 →
      (∀ x y, entry x.val y.val = FiniteFallbackOutput.fallbackMatrix edge k x y) →
      MatrixTableWriter.EntryRuns (FallbackBranch.cellOf m) .move FallbackBranch.cinit (fun _ => [])
        (FiniteFallbackOutput.rows k) (FiniteFallbackOutput.cols k) T entry →
      astep ⟨some (.inl .dispatch), embedS (vc, flag, none, none),
          bankD (FallbackColourSearch.edgeList edge) q' k⟩ =
        ⟨some (.inr (.inr (m, .dec))), embedP FallbackBranch.pStart,
          bankD (FallbackColourSearch.edgeList edge) q' k⟩ →
      ∃ t ≤ (v + 1) + 3 ^ v * (FallbackColourSearch.T edge + 3 * v + 4) + 1 +
          2 ^ (3 * k + 15),
        ∃ (ctl : ACtl) (q' : List Bool),
          (astep^[t]) (start edge k) =
            ⟨none, ctl, Sum.elim (FallbackBranch.SA (FallbackColourSearch.edgeList edge) q')
              (Sum.elim (Sum.elim (FallbackDimsPrinter.pbank k 0)
                (MatrixTableWriter.ready (fun _ => []) (FiniteFallbackOutput.rows k)
                  (FiniteFallbackOutput.cols k) 0 0 0 0 []
                  (MatrixMaterialization.rowMajor
                    (FiniteFallbackOutput.fallbackMatrix edge k))).contents) (fun _ => []))⟩ := by
    intro m T entry hT hf hcell hd
    obtain ⟨t3, ht3, ctl, h3⟩ := print_stage m (FallbackBranch.SA (FallbackColourSearch.edgeList edge) q') k T
      entry (FiniteFallbackOutput.fallbackMatrix edge k) hf hcell
    have hpc := FallbackDimsPrinter.print_clock_le k T hT
    refine ⟨t3 + 1 + t1, by omega, ctl, q', ?_⟩
    rw [Function.iterate_add_apply, Function.iterate_add_apply, h1, Function.iterate_one, hd, h3]
  by_cases h : FiniteFallbackOutput.ThreeColourable edge
  · have hv : vc.acc = true := by rw [hacc]; simpa using h
    have hfm : FiniteFallbackOutput.fallbackMatrix edge k = fun _ _ => false := by
      unfold FiniteFallbackOutput.fallbackMatrix; exact if_pos h
    exact finish .zero 1 (fun _ _ => false) (by omega) (by intro x y; rw [hfm])
      (FallbackBranch.zeroCell_entryRuns _ _) (dispatch_acc _ _ _ vc flag hv)
  · have hv : vc.acc = false := by rw [hacc]; simpa using h
    have hfm : FiniteFallbackOutput.fallbackMatrix edge k = FiniteFallbackOutput.hardMatrix k := by
      unfold FiniteFallbackOutput.fallbackMatrix; exact if_neg h
    rcases k with _ | _ | i
    · exact finish .zero 1 (fun _ _ => false) (by omega) (by intro x y; rw [hfm]; rfl)
        (FallbackBranch.zeroCell_entryRuns _ _) (dispatch_k0 _ _ vc flag hv)
    · exact finish .one 1 (fun _ y => decide (y = 1)) (by omega)
        (by intro x y; rw [hfm]; exact decide_eq_decide.mpr ⟨fun h => Fin.ext h, fun h => h ▸ rfl⟩)
        (FallbackBranch.oneCell2_entryRuns _ _) (dispatch_k1 _ _ vc flag hv)
    · have hcell := FallbackIdentityCell.eqCell_entryRuns (2 ^ (i + 1)) (2 ^ (i + 1))
      rw [FallbackDimsPrinter.bank2_eq] at hcell
      have hT : 3 * 2 ^ (i + 1) + 3 ≤ 3 * 2 ^ (i + 2) + 3 := by
        have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show i + 1 ≤ i + 2 by omega)
        omega
      exact finish .ident (3 * 2 ^ (i + 1) + 3) (fun x y => decide (x = y)) hT
        (by intro x y; rw [hfm]; exact decide_eq_decide.mpr Fin.val_inj)
        hcell (dispatch_k2 _ _ i vc flag hv)

/-- The same clock as an explicit function of `v`, `e`, `k`. -/
theorem fallback_branch_ternary_clock {v e : Nat} (edge : Fin e → Bool → Fin v) (k : Nat) :
    (v + 1) + 3 ^ v * (FallbackColourSearch.T edge + 3 * v + 4) + 1 + 2 ^ (3 * k + 15) ≤
      (v + 2) + 3 ^ v * (10 * (e + 1) * (v + 1)) + 2 ^ (3 * k + 15) := by
  have := TernaryColourSearch.ternary_clock_le edge
  omega

#print axioms alloc_loop
#print axioms front
#print axioms print_stage
#print axioms dispatch_acc
#print axioms dispatch_k2
#print axioms fallback_branch_run_ternary
#print axioms fallback_branch_ternary_clock

end

end Paper2.FallbackBranchT
