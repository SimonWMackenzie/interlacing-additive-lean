import EthInapproximability.CurrentPaper.MatrixWeightedEntryController

/-!
# Charged step counts for the physical protected-entry controller

These lemmas retain the explicit bounds already proved for each embedded
finite-stack program.  They do not use the nonconstructive finite supremum of
halting times in `MatrixWeightedEntryBound`.
-/

namespace EthInapproximability.CurrentPaper.MatrixWeightedEntryCost

open MatrixWeightedEntryController Turing Turing.TM2.Stmt
  BitMachineStackEmbedding

def workLength (S : Stack → List Bool) : ℕ :=
  ∑ i : Fin 41, (S (workSlot i)).length

theorem workLength_le_max (S : Stack → List Bool) (M : ℕ)
    (h : ∀ i : Fin 41, (S (workSlot i)).length ≤ M) :
    workLength S ≤ 41 * M := by
  unfold workLength
  calc
    (∑ i : Fin 41, (S (workSlot i)).length) ≤ ∑ _i : Fin 41, M :=
      Finset.sum_le_sum (by intro i _; exact h i)
    _ = 41 * M := by simp

theorem chain_three {c₀ c₁ c₂ c₃ : Config}
    {b₀ b₁ b₂ : ℕ}
    (h₀ : ∃ t ≤ b₀, run t c₀ = c₁)
    (h₁ : ∃ t ≤ b₁, run t c₁ = c₂)
    (h₂ : ∃ t ≤ b₂, run t c₂ = c₃) :
    ∃ t ≤ b₀+b₁+b₂, run t c₀ = c₃ := by
  obtain ⟨t₀, ht₀, he₀⟩ := h₀
  obtain ⟨t₁, ht₁, he₁⟩ := h₁
  obtain ⟨t₂, ht₂, he₂⟩ := h₂
  refine ⟨t₀+(t₁+t₂), by omega, ?_⟩
  rw [run_add he₀, run_add he₁]
  exact he₂

def lookupCost (row width col sourceLength : ℕ) : ℕ :=
  32*(row+width+col+sourceLength+1)^2 + 1

theorem lookup_and_clear_bounded (d : Input) (x y row col : ℕ)
    (v : State) (S : Stack → List Bool)
    (hrow : S (lookupSlots 0) = List.replicate row true)
    (hwidth : S (lookupSlots 1) = List.replicate d.rawWidth true)
    (hcol : S (lookupSlots 2) = List.replicate col true)
    (hsource : S (lookupSlots 6) = d.rawBits)
    (hout : S (lookupSlots 7) = [])
    (hwork : ∀ k : Fin 10, k ≠ 0 → k ≠ 1 → k ≠ 2 →
      k ≠ 6 → k ≠ 7 → S (lookupSlots k) = [])
    (hstable : ∀ k, (∀ i : Fin 41, workSlot i ≠ k) →
      S k = cellBank d x y [] k) :
    ∃ t ≤ lookupCost row d.rawWidth col d.rawBits.length +
      workLength S + 43,
      run t (cfg (some .lookupInit) (v,none) S) =
        cfg none initial
          (cellBank d x y
            [d.rawBits[row*d.rawWidth+col]?.getD false]) := by
  obtain ⟨tl, htl, hl⟩ := lookup_phase v S row d.rawWidth col
    d.rawBits [] hrow hwidth hcol hsource hout hwork
  let bit := d.rawBits[row*d.rawWidth+col]?.getD false
  let S' := Function.update S (.inr 2) [bit]
  have hc := clear_run (.lookup MatrixTableLookup.initial) S'
  have hs : ∀ k, (∀ i : Fin 41, workSlot i ≠ k) →
      S' k = cellBank d x y [bit] k := by
    intro k hk
    by_cases heq : k = .inr 2
    · subst k
      rfl
    · simp only [S', Function.update_of_ne heq]
      rw [hstable k hk]
      cases k with
      | inl k => rfl
      | inr k => fin_cases k <;> simp_all [cellBank]
  have hf : BitMachineClearBank.cleared workSlot S' =
      cellBank d x y [bit] :=
    cleared_to_cellBank d x y [bit] S' hs
  have hlength : workLength S' = workLength S := by
    unfold workLength
    apply Finset.sum_congr rfl
    intro i _
    have hn : (workSlot i) ≠ (.inr 2) := by fin_cases i <;> decide
    simp [S', Function.update_of_ne hn]
  refine ⟨tl + (workLength S' + 43), ?_, ?_⟩
  · rw [hlength]
    dsimp [lookupCost] at htl ⊢
    omega
  · rw [run_add hl, show workLength S' =
        ∑ i, (S' (workSlot i)).length from rfl, hc, hf]

def rowClearCost (S : Stack → List Bool) : ℕ :=
  (S (.inl 23)).length + (S (.inl 63)).length + 2

theorem direct_row_to_lookup_bounded (S T : Fin 64 → List Bool)
    (extra : Fin 3 → List Bool) (v : State) (g : Fin 4)
    (n bound : ℕ) (hg : g.val < 2)
    (hrun : ∃ t ≤ bound,
      MatrixWeightedRowController.run t
        (MatrixWeightedRowController.cfg
          (some MatrixWeightedRowController.start)
          MatrixWeightedRowController.initial S) =
      MatrixWeightedRowController.cfg none (.chosen g) T)
    (hlabel : T 54 = List.replicate n true)
    (hraw : T 25 = []) (hscratch : T 14 = []) :
    let B := Sum.elim T extra
    ∃ t ≤ (bound+1) + rowClearCost B + (2*n+4),
      run t (cfg (some .rowInit) (v,none) (Sum.elim S extra)) =
        cfg (some .lookupInit) (.copy none, none)
          (Function.update (afterRowClear B)
            (.inl 25) (List.replicate n true)) := by
  obtain ⟨tr, htr, hr⟩ := row_phase_from S T extra v g bound hrun
  let B := Sum.elim T extra
  have hc := clear_row_work_run (.row (.chosen g)) B
  obtain ⟨td, htd, hd⟩ := direct_row_run (afterRowClear B) g n hg
    (by simpa only [afterRowClear, B] using hlabel)
    (by simpa only [afterRowClear, B] using hraw)
    (by simpa only [afterRowClear, B] using hscratch)
  refine ⟨tr + rowClearCost B + td, ?_, ?_⟩
  · change tr + rowClearCost (Sum.elim T extra) + td ≤
        (bound+1) + rowClearCost (Sum.elim T extra) + (2*n+4)
    omega
  · rw [show tr + rowClearCost B + td = tr + (rowClearCost B + td)
        by omega]
    rw [run_add hr]
    change run ((B (.inl 23)).length + (B (.inl 63)).length + 2 + td)
      (cfg (some .clearRowWork) (.row (.chosen g), none) B) = _
    rw [run_add hc]
    exact hd

theorem ordered_row_to_lookup_bounded {nv nb : ℕ}
    (order : Construction.ItemOrder nv nb) (j : Fin (nv+nb))
    (S T : Fin 64 → List Bool) (extra : Fin 3 → List Bool)
    (v : State) (g : Fin 4) (aux : Bool)
    (label width sL bound : ℕ)
    (hg : 2 ≤ g.val) (haux : aux = (g == 3))
    (hw : 0 < width)
    (hj : j.val = label / width + (if aux then nv else 0))
    (hrun : ∃ t ≤ bound,
      MatrixWeightedRowController.run t
        (MatrixWeightedRowController.cfg
          (some MatrixWeightedRowController.start)
          MatrixWeightedRowController.initial S) =
      MatrixWeightedRowController.cfg none (.chosen g) T)
    (hinput : ∀ k,
      MatrixWeightedRowOrderMachineRun.inputBank label width nv sL
        (MatrixWeightedRowOrderLookup.orderWord order) [] k =
      afterRowClear (Sum.elim T extra) (orderSlots k)) :
    let B := Sum.elim T extra
    ∃ t ≤ (bound+1) + rowClearCost B +
      (orderBound order j label width sL aux + 2),
      run t (cfg (some .rowInit) (v,none) (Sum.elim S extra)) =
        cfg (some .lookupInit) (.order (.address false), none)
          (BitMachineStackEmbedding.bank orderSlots (afterRowClear B)
            (MatrixWeightedRowOrderMachineRun.terminalBank label width nv sL
              (MatrixWeightedRowOrderLookup.orderWord order) []
              aux j.val (order j).val)) := by
  obtain ⟨tr, htr, hr⟩ := row_phase_from S T extra v g bound hrun
  let B := Sum.elim T extra
  have hc := clear_row_work_run (.row (.chosen g)) B
  obtain ⟨to', hto', ho⟩ := order_phase order j label width sL g aux
    hg haux hw hj (afterRowClear B) hinput
  refine ⟨tr + rowClearCost B + to', ?_, ?_⟩
  · change tr + rowClearCost (Sum.elim T extra) + to' ≤
        (bound+1) + rowClearCost (Sum.elim T extra) +
          (orderBound order j label width sL aux + 2)
    omega
  · rw [show tr + rowClearCost B + to' = tr + (rowClearCost B + to')
        by omega]
    rw [run_add hr]
    change run ((B (.inl 23)).length + (B (.inl 63)).length + 2 + to')
      (cfg (some .clearRowWork) (.row (.chosen g), none) B) = _
    rw [run_add hc]
    exact ho

def copyCost (x y : ℕ) : ℕ := (2*x+2) + (2*y+3)

def fullColumnCost (d : Input) (x : ℕ) : ℕ :=
  1 + ((11*x + 3*d.uniform + 7) +
    (3*min (x/d.uniform) d.fullBoundary + 5) +
    (11*(x/d.uniform) + 3*d.fullDivisor + 10))

def diagonalColumnCost (d : Input) (x : ℕ) : ℕ :=
  1 + ((11*x + 3*d.uniform + 7) +
    (3*min (x/d.uniform) d.fullBoundary + 5) +
    (11*(x/d.uniform-d.fullBoundary) + 3*d.diagonalDivisor + 10))

def diagonalAddressCost (d : Input) (x : ℕ) : ℕ :=
  MatrixWeightedDiagonalMachine.bound (diagonalCode d x)
    d.wordBase d.cy d.s d.binBase + 2

theorem full_prefix_bounded (d : Input) (x y : ℕ)
    (hcolumn : x / d.uniform < d.fullBoundary) :
    ∃ t ≤ copyCost x y + fullColumnCost d x + 1,
      run t (cfg (some start) initial (cellBank d x y [])) =
      cfg (some .rowInit) (.column (.terminal false), none)
        (afterFullColumn d x y []) := by
  obtain ⟨tc, htc, hc⟩ := copy_coordinates_run d x y []
  obtain ⟨tf, htf, hf⟩ := column_full_run d x y [] hcolumn
  have hd : run 1
      (cfg (some .afterColumn) (.column (.terminal false), none)
        (afterFullColumn d x y [])) =
      cfg (some .rowInit) (.column (.terminal false), none)
        (afterFullColumn d x y []) := rfl
  refine ⟨tc + (tf+1), ?_, ?_⟩
  · dsimp [copyCost, fullColumnCost]
    omega
  · rw [run_add hc, run_add hf]
    exact hd

theorem diagonal_prefix_bounded (d : Input) (x y : ℕ)
    (hcolumn : d.fullBoundary ≤ x / d.uniform) :
    ∃ t ≤ copyCost x y + diagonalColumnCost d x +
        diagonalAddressCost d x,
      run t (cfg (some start) initial (cellBank d x y [])) =
      cfg (some .rowInit) (.diagonal .idle, none)
        (Sum.elim (diagonalCore d x y) (writerExtra x y [])) := by
  obtain ⟨tc, htc, hc⟩ := copy_coordinates_run d x y []
  obtain ⟨td, htd, hd⟩ := column_diagonal_run d x y [] hcolumn
  obtain ⟨ta, hta, ha⟩ := diagonal_arithmetic_phase d x y []
  have hu : Function.update (afterDiagonalColumn d x y [])
      (.inl 19)
      (List.replicate
        (MatrixWeightedDiagonalMachine.rawValue (diagonalCode d x)
          d.wordBase d.cy d.s d.binBase) true) =
      Sum.elim (diagonalCore d x y) (writerExtra x y []) := by
    funext k
    cases k with
    | inl k => fin_cases k <;> rfl
    | inr k => fin_cases k <;> rfl
  rw [hu] at ha
  refine ⟨tc + (td+ta), ?_, ?_⟩
  · dsimp [copyCost, diagonalColumnCost, diagonalAddressCost]
    omega
  · rw [run_add hc, run_add hd]
    exact ha

theorem compose_bounded (d : Input) (x y row col : ℕ)
    (v₀ v₁ : State) (core pre : Stack → List Bool)
    (prefixCost rowCost : ℕ)
    (hprefix : ∃ t ≤ prefixCost,
      run t (cfg (some start) initial (cellBank d x y [])) =
        cfg (some .rowInit) (v₀,none) core)
    (hrowRun : ∃ t ≤ rowCost,
      run t (cfg (some .rowInit) (v₀,none) core) =
        cfg (some .lookupInit) (v₁,none) pre)
    (hrow : pre (lookupSlots 0) = List.replicate row true)
    (hwidth : pre (lookupSlots 1) = List.replicate d.rawWidth true)
    (hcol : pre (lookupSlots 2) = List.replicate col true)
    (hsource : pre (lookupSlots 6) = d.rawBits)
    (hout : pre (lookupSlots 7) = [])
    (hwork : ∀ k : Fin 10, k ≠ 0 → k ≠ 1 → k ≠ 2 →
      k ≠ 6 → k ≠ 7 → pre (lookupSlots k) = [])
    (hstable : ∀ k, (∀ i : Fin 41, workSlot i ≠ k) →
      pre k = cellBank d x y [] k) :
    ∃ t ≤ prefixCost + rowCost +
        lookupCost row d.rawWidth col d.rawBits.length +
        workLength pre + 43,
      run t (cfg (some start) initial (cellBank d x y [])) =
        cfg none initial
          (cellBank d x y
            [d.rawBits[row*d.rawWidth+col]?.getD false]) := by
  obtain ⟨tp, htp, hp⟩ := hprefix
  obtain ⟨tr, htr, hr⟩ := hrowRun
  obtain ⟨ts, hts, hs⟩ := lookup_and_clear_bounded
    d x y row col v₁ pre hrow hwidth hcol hsource hout hwork hstable
  refine ⟨tp + (tr+ts), ?_, ?_⟩
  · dsimp [lookupCost] at hts ⊢
    omega
  · rw [run_add hp, run_add hr]
    exact hs

def fullRowCost (d : Input) (y : ℕ) : ℕ :=
  (11*y+11) + (3*min y d.rowBoundary₁+5) +
    (11*y+3*d.rowDivisor₀+10)

def fullFullCost (d : Input) (x y : ℕ) : ℕ :=
  (copyCost x y + fullColumnCost d x + 1) +
  ((fullRowCost d y+1) + rowClearCost (fullFullRowBank d x y) +
    (2*fullLabel d y+4)) +
  lookupCost (fullLabel d y) d.rawWidth
    ((x/d.uniform)/d.fullDivisor) d.rawBits.length +
  workLength (fullFullPreLookup d x y) + 43

theorem full_full_bounded (d : Input) (x y : ℕ)
    (hcolumn : x / d.uniform < d.fullBoundary)
    (hrow : y < d.rowBoundary₁) :
    ∃ t ≤ fullFullCost d x y,
      run t (cfg (some start) initial (cellBank d x y [])) =
        cfg none initial
          (cellBank d x y
            [d.rawBits[fullLabel d y*d.rawWidth+
              ((x/d.uniform)/d.fullDivisor)]?.getD false]) := by
  have hprefix := full_prefix_bounded d x y hcolumn
  have hr := MatrixWeightedRowController.full_controller_run
    (fullCore d x y) y d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
    d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃ hrow
  simp only [fullCore] at hr
  rw [full_row_seed_frame d x y []] at hr
  have hrowRun := direct_row_to_lookup_bounded
    (fullCore d x y) (fullRowResult d (fullCore d x y) y)
    (writerExtra x y []) (.column (.terminal false)) 0
    (fullLabel d y) (fullRowCost d y) (by decide) hr
    (by rfl) (by rfl) (by rfl)
  obtain ⟨h₀,h₁,h₂,h₃,h₄,hwork⟩ := fullFull_lookup_frame d x y
  have h := compose_bounded d x y (fullLabel d y)
    ((x/d.uniform)/d.fullDivisor)
    (.column (.terminal false)) (.copy none)
    (afterFullColumn d x y []) (fullFullPreLookup d x y)
    (copyCost x y + fullColumnCost d x + 1)
    ((fullRowCost d y+1) + rowClearCost (fullFullRowBank d x y) +
      (2*fullLabel d y+4))
    hprefix
    (by simpa only [afterFullColumn, fullCore, fullFullRowBank,
        fullFullPreLookup] using hrowRun)
    h₀ h₁ h₂ h₃ h₄ hwork
    (fullFull_stable d x y)
  simpa only [fullFullCost] using h

def templateRowCost (d : Input) (y : ℕ) : ℕ :=
  (11*y+11) + (3*min y d.rowBoundary₁+5) +
    (3*min (y-d.rowBoundary₁) d.rowBoundary₂+6) +
    (11*(y-d.rowBoundary₁)+3*d.rowDivisor₁+10)

def fullTemplateCost (d : Input) (x y : ℕ) : ℕ :=
  (copyCost x y + fullColumnCost d x + 1) +
  ((templateRowCost d y+1) + rowClearCost (fullTemplateRowBank d x y) +
    (2*templateLabel d y+4)) +
  lookupCost (templateLabel d y) d.rawWidth
    ((x/d.uniform)/d.fullDivisor) d.rawBits.length +
  workLength (fullTemplatePreLookup d x y) + 43

theorem full_template_bounded (d : Input) (x y : ℕ)
    (hcolumn : x / d.uniform < d.fullBoundary)
    (h₁ : d.rowBoundary₁ ≤ y)
    (htemplate : y-d.rowBoundary₁ < d.rowBoundary₂) :
    ∃ t ≤ fullTemplateCost d x y,
      run t (cfg (some start) initial (cellBank d x y [])) =
        cfg none initial
          (cellBank d x y
            [d.rawBits[templateLabel d y*d.rawWidth+
              ((x/d.uniform)/d.fullDivisor)]?.getD false]) := by
  have hprefix := full_prefix_bounded d x y hcolumn
  have hr := MatrixWeightedRowController.template_controller_run
    (fullCore d x y) y d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
    d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃
    h₁ htemplate
  simp only [fullCore] at hr
  rw [full_row_seed_frame d x y []] at hr
  have hrowRun := direct_row_to_lookup_bounded
    (fullCore d x y) (templateRowResult d (fullCore d x y) y)
    (writerExtra x y []) (.column (.terminal false)) 1
    (templateLabel d y) (templateRowCost d y) (by decide) hr
    (by rfl) (by rfl) (by rfl)
  obtain ⟨h₀,h₁',h₂,h₃,h₄,hwork⟩ := fullTemplate_lookup_frame d x y
  have h := compose_bounded d x y (templateLabel d y)
    ((x/d.uniform)/d.fullDivisor)
    (.column (.terminal false)) (.copy none)
    (afterFullColumn d x y []) (fullTemplatePreLookup d x y)
    (copyCost x y + fullColumnCost d x + 1)
    ((templateRowCost d y+1) + rowClearCost (fullTemplateRowBank d x y) +
      (2*templateLabel d y+4))
    hprefix
    (by simpa only [afterFullColumn, fullCore, fullTemplateRowBank,
        fullTemplatePreLookup] using hrowRun)
    h₀ h₁' h₂ h₃ h₄ hwork
    (fullTemplate_stable d x y)
  simpa only [fullTemplateCost] using h

def diagonalColumnValue (d : Input) (x : ℕ) : ℕ :=
  MatrixWeightedDiagonalMachine.rawValue (diagonalCode d x)
    d.wordBase d.cy d.s d.binBase

def diagonalFullCost (d : Input) (x y : ℕ) : ℕ :=
  (copyCost x y + diagonalColumnCost d x + diagonalAddressCost d x) +
  ((fullRowCost d y+1) + rowClearCost (diagonalFullRowBank d x y) +
    (2*fullLabel d y+4)) +
  lookupCost (fullLabel d y) d.rawWidth (diagonalColumnValue d x)
    d.rawBits.length +
  workLength (diagonalFullPreLookup d x y) + 43

theorem diagonal_full_bounded (d : Input) (x y : ℕ)
    (hcolumn : d.fullBoundary ≤ x / d.uniform)
    (hrow : y < d.rowBoundary₁) :
    ∃ t ≤ diagonalFullCost d x y,
      run t (cfg (some start) initial (cellBank d x y [])) =
        cfg none initial
          (cellBank d x y
            [d.rawBits[fullLabel d y*d.rawWidth+
              diagonalColumnValue d x]?.getD false]) := by
  have hprefix := diagonal_prefix_bounded d x y hcolumn
  have hr := MatrixWeightedRowController.full_controller_run
    (diagonalCore d x y) y d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
    d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃ hrow
  simp only [diagonalCore] at hr
  rw [diagonal_row_seed_frame d x y
    (MatrixWeightedDiagonalMachine.rawValue (diagonalCode d x)
      d.wordBase d.cy d.s d.binBase) []] at hr
  have hrowRun := direct_row_to_lookup_bounded
    (diagonalCore d x y) (fullRowResult d (diagonalCore d x y) y)
    (writerExtra x y []) (.diagonal .idle) 0
    (fullLabel d y) (fullRowCost d y) (by decide) hr
    (by rfl) (by rfl) (by rfl)
  obtain ⟨h₀,h₁,h₂,h₃,h₄,hwork⟩ := diagonalFull_lookup_frame d x y
  have h := compose_bounded d x y (fullLabel d y)
    (diagonalColumnValue d x)
    (.diagonal .idle) (.copy none)
    (Sum.elim (diagonalCore d x y) (writerExtra x y []))
    (diagonalFullPreLookup d x y)
    (copyCost x y + diagonalColumnCost d x + diagonalAddressCost d x)
    ((fullRowCost d y+1) + rowClearCost (diagonalFullRowBank d x y) +
      (2*fullLabel d y+4))
    hprefix
    (by simpa only [diagonalFullRowBank,
        diagonalFullPreLookup] using hrowRun)
    h₀ h₁ h₂ h₃ h₄ hwork
    (diagonalFull_stable d x y)
  simpa only [diagonalFullCost, diagonalColumnValue] using h

def diagonalTemplateCost (d : Input) (x y : ℕ) : ℕ :=
  (copyCost x y + diagonalColumnCost d x + diagonalAddressCost d x) +
  ((templateRowCost d y+1) +
    rowClearCost (diagonalTemplateRowBank d x y) +
    (2*templateLabel d y+4)) +
  lookupCost (templateLabel d y) d.rawWidth (diagonalColumnValue d x)
    d.rawBits.length +
  workLength (diagonalTemplatePreLookup d x y) + 43

theorem diagonal_template_bounded (d : Input) (x y : ℕ)
    (hcolumn : d.fullBoundary ≤ x / d.uniform)
    (h₁ : d.rowBoundary₁ ≤ y)
    (htemplate : y-d.rowBoundary₁ < d.rowBoundary₂) :
    ∃ t ≤ diagonalTemplateCost d x y,
      run t (cfg (some start) initial (cellBank d x y [])) =
        cfg none initial
          (cellBank d x y
            [d.rawBits[templateLabel d y*d.rawWidth+
              diagonalColumnValue d x]?.getD false]) := by
  have hprefix := diagonal_prefix_bounded d x y hcolumn
  have hr := MatrixWeightedRowController.template_controller_run
    (diagonalCore d x y) y d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
    d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃
    h₁ htemplate
  simp only [diagonalCore] at hr
  rw [diagonal_row_seed_frame d x y
    (MatrixWeightedDiagonalMachine.rawValue (diagonalCode d x)
      d.wordBase d.cy d.s d.binBase) []] at hr
  have hrowRun := direct_row_to_lookup_bounded
    (diagonalCore d x y) (templateRowResult d (diagonalCore d x y) y)
    (writerExtra x y []) (.diagonal .idle) 1
    (templateLabel d y) (templateRowCost d y) (by decide) hr
    (by rfl) (by rfl) (by rfl)
  obtain ⟨h₀,h₁',h₂,h₃,h₄,hwork⟩ := diagonalTemplate_lookup_frame d x y
  have h := compose_bounded d x y (templateLabel d y)
    (diagonalColumnValue d x)
    (.diagonal .idle) (.copy none)
    (Sum.elim (diagonalCore d x y) (writerExtra x y []))
    (diagonalTemplatePreLookup d x y)
    (copyCost x y + diagonalColumnCost d x + diagonalAddressCost d x)
    ((templateRowCost d y+1) +
      rowClearCost (diagonalTemplateRowBank d x y) +
      (2*templateLabel d y+4))
    hprefix
    (by simpa only [diagonalTemplateRowBank,
        diagonalTemplatePreLookup] using hrowRun)
    h₀ h₁' h₂ h₃ h₄ hwork
    (diagonalTemplate_stable d x y)
  simpa only [diagonalTemplateCost, diagonalColumnValue] using h

def vertexRowCost (d : Input) (y : ℕ) : ℕ :=
  (11*y+11) + (3*min y d.rowBoundary₁+5) +
    (3*min (y-d.rowBoundary₁) d.rowBoundary₂+6) +
    (3*min (y-d.rowBoundary₁-d.rowBoundary₂) d.rowBoundary₃+6) +
    (11*(y-d.rowBoundary₁-d.rowBoundary₂)+3*d.rowDivisor₂+10)

def auxiliaryRowCost (d : Input) (y : ℕ) : ℕ :=
  (11*y+11) + (3*min y d.rowBoundary₁+5) +
    (3*min (y-d.rowBoundary₁) d.rowBoundary₂+6) +
    (3*min (y-d.rowBoundary₁-d.rowBoundary₂) d.rowBoundary₃+6) +
    (11*(y-d.rowBoundary₁-d.rowBoundary₂-d.rowBoundary₃)+
      3*d.rowDivisor₃+10)

noncomputable def fullVertexCost (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb)) : ℕ :=
  (copyCost x y + fullColumnCost d x + 1) +
  ((vertexRowCost d y+1) + rowClearCost (fullVertexRowBank d x y) +
    (orderBound order j (vertexLabel d y) d.rx
      d.stagePrefixRows false + 2)) +
  lookupCost
    (d.stagePrefixRows + (order j).val*d.rx + vertexLabel d y%d.rx)
    d.rawWidth ((x/d.uniform)/d.fullDivisor) d.rawBits.length +
  workLength (fullVertexPreLookup d x y order j) + 43

theorem full_vertex_bounded (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb))
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (hwidth : 0 < d.rx)
    (hj : j.val = vertexLabel d y / d.rx)
    (hcolumn : x / d.uniform < d.fullBoundary)
    (h₁ : d.rowBoundary₁ ≤ y)
    (h₂ : d.rowBoundary₂ ≤ y-d.rowBoundary₁)
    (hvertex : y-d.rowBoundary₁-d.rowBoundary₂ < d.rowBoundary₃) :
    ∃ t ≤ fullVertexCost d x y order j,
      run t (cfg (some start) initial (cellBank d x y [])) =
        cfg none initial
          (cellBank d x y
            [d.rawBits[(d.stagePrefixRows + (order j).val*d.rx +
              vertexLabel d y%d.rx)*d.rawWidth+
              ((x/d.uniform)/d.fullDivisor)]?.getD false]) := by
  have hprefix := full_prefix_bounded d x y hcolumn
  have hr := MatrixWeightedRowController.vertex_controller_run
    (fullCore d x y) y d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
    d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃
    h₁ h₂ hvertex
  simp only [fullCore] at hr
  rw [full_row_seed_frame d x y []] at hr
  have hinput := vertex_order_frame_full d order horder x y
  have hrowRun := ordered_row_to_lookup_bounded order j
    (fullCore d x y) (vertexRowResult d (fullCore d x y) y)
    (writerExtra x y []) (.column (.terminal false)) 2 false
    (vertexLabel d y) d.rx d.stagePrefixRows (vertexRowCost d y)
    (by decide) (by rfl) hwidth (by simpa using hj) hr hinput
  obtain ⟨h₀,h₁',h₂',h₃,h₄,hwork⟩ :=
    fullVertex_lookup_frame d x y order j
  have h := compose_bounded d x y
    (d.stagePrefixRows + (order j).val*d.rx + vertexLabel d y%d.rx)
    ((x/d.uniform)/d.fullDivisor)
    (.column (.terminal false)) (.order (.address false))
    (afterFullColumn d x y []) (fullVertexPreLookup d x y order j)
    (copyCost x y + fullColumnCost d x + 1)
    ((vertexRowCost d y+1) + rowClearCost (fullVertexRowBank d x y) +
      (orderBound order j (vertexLabel d y) d.rx
        d.stagePrefixRows false + 2))
    hprefix
    (by simpa only [afterFullColumn, fullCore, fullVertexRowBank,
        fullVertexPreLookup] using hrowRun)
    h₀ h₁' h₂' h₃ h₄ hwork
    (fullVertex_stable d x y order j horder)
  simpa only [fullVertexCost] using h

theorem ordered_suffix_bounded (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb)) (label : ℕ) (aux : Bool)
    (B : Stack → List Bool) (col : ℕ)
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (hwidth : B (lookupSlots 1) = List.replicate d.rawWidth true)
    (hcol : B (lookupSlots 2) = List.replicate col true)
    (hsource : B (lookupSlots 6) = d.rawBits)
    (hout : B (lookupSlots 7) = [])
    (hwork : ∀ k : Fin 10, k ≠ 0 → k ≠ 1 → k ≠ 2 →
      k ≠ 6 → k ≠ 7 → B (lookupSlots k) = [])
    (hB : ∀ k, (∀ i : Fin 41, workSlot i ≠ k) →
      B k = cellBank d x y [] k) :
    ∃ t ≤ lookupCost
        (d.stagePrefixRows + (order j).val*d.rx + label%d.rx)
        d.rawWidth col d.rawBits.length +
        workLength (orderPreLookup d order j label aux B) + 43,
      run t (cfg (some .lookupInit) (.order (.address false), none)
        (orderPreLookup d order j label aux B)) =
        cfg none initial
          (cellBank d x y
            [d.rawBits[(d.stagePrefixRows + (order j).val*d.rx +
              label%d.rx)*d.rawWidth+col]?.getD false]) := by
  obtain ⟨hr,hw,hc,hs,ho,hwork'⟩ := orderPreLookup_frame
    d order j label aux B col hwidth hcol hsource hout hwork
  exact lookup_and_clear_bounded d x y
    (d.stagePrefixRows + (order j).val*d.rx + label%d.rx)
    col (.order (.address false))
    (orderPreLookup d order j label aux B)
    hr hw hc hs ho hwork'
    (orderPreLookup_stable d x y order j label aux B horder hB)

theorem ordered_branch_bounded (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb)) (label col : ℕ) (aux : Bool)
    (S T : Fin 64 → List Bool) (v : State) (g : Fin 4)
    (prefixCost rowCost : ℕ)
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (hg : 2 ≤ g.val) (haux : aux = (g == 3))
    (hwidth : 0 < d.rx)
    (hj : j.val = label / d.rx + (if aux then d.nv else 0))
    (hprefix : ∃ t ≤ prefixCost,
      run t (cfg (some start) initial (cellBank d x y [])) =
        cfg (some .rowInit) (v,none)
          (Sum.elim S (writerExtra x y [])))
    (hrun : ∃ t ≤ rowCost,
      MatrixWeightedRowController.run t
        (MatrixWeightedRowController.cfg
          (some MatrixWeightedRowController.start)
          MatrixWeightedRowController.initial S) =
      MatrixWeightedRowController.cfg none (.chosen g) T)
    (hinput : ∀ k,
      MatrixWeightedRowOrderMachineRun.inputBank label d.rx d.nv
        d.stagePrefixRows (MatrixWeightedRowOrderLookup.orderWord order)
        [] k =
      afterRowClear (Sum.elim T (writerExtra x y [])) (orderSlots k))
    (hcol : (afterRowClear (Sum.elim T (writerExtra x y [])))
      (lookupSlots 2) = List.replicate col true)
    (hwork : ∀ k : Fin 10, k ≠ 0 → k ≠ 1 → k ≠ 2 →
      k ≠ 6 → k ≠ 7 →
      (afterRowClear (Sum.elim T (writerExtra x y [])))
        (lookupSlots k) = [])
    (hB : ∀ k, (∀ i : Fin 41, workSlot i ≠ k) →
      (afterRowClear (Sum.elim T (writerExtra x y []))) k =
        cellBank d x y [] k) :
    let B := afterRowClear (Sum.elim T (writerExtra x y []))
    let pre := orderPreLookup d order j label aux B
    ∃ t ≤ prefixCost +
        ((rowCost+1) + rowClearCost (Sum.elim T (writerExtra x y [])) +
          (orderBound order j label d.rx d.stagePrefixRows aux + 2)) +
        (lookupCost
          (d.stagePrefixRows + (order j).val*d.rx + label%d.rx)
          d.rawWidth col d.rawBits.length + workLength pre + 43),
      run t (cfg (some start) initial (cellBank d x y [])) =
        cfg none initial
          (cellBank d x y
            [d.rawBits[(d.stagePrefixRows + (order j).val*d.rx +
              label%d.rx)*d.rawWidth+col]?.getD false]) := by
  let B := afterRowClear (Sum.elim T (writerExtra x y []))
  let pre := orderPreLookup d order j label aux B
  have hrow := ordered_row_to_lookup_bounded order j S T
    (writerExtra x y []) v g aux label d.rx d.stagePrefixRows rowCost
    hg haux hwidth hj hrun hinput
  have hBwidth : B (lookupSlots 1) =
      List.replicate d.rawWidth true := by
    change afterRowClear (Sum.elim T (writerExtra x y []))
      (lookupSlots 1) = _
    rw [hB (lookupSlots 1) (by decide)]
    rfl
  have hBsource : B (lookupSlots 6) = d.rawBits := by
    change afterRowClear (Sum.elim T (writerExtra x y []))
      (lookupSlots 6) = _
    rw [hB (lookupSlots 6) (by decide)]
    rfl
  have hBout : B (lookupSlots 7) = [] := by
    change afterRowClear (Sum.elim T (writerExtra x y []))
      (lookupSlots 7) = _
    rw [hB (lookupSlots 7) (by decide)]
    rfl
  have hsuffix := ordered_suffix_bounded d x y order j label aux B col
    horder hBwidth hcol hBsource hBout hwork hB
  exact chain_three hprefix hrow hsuffix

noncomputable def fullAuxiliaryCost (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb)) : ℕ :=
  (copyCost x y + fullColumnCost d x + 1) +
  ((auxiliaryRowCost d y+1) +
    rowClearCost (fullAuxiliaryRowBank d x y) +
    (orderBound order j (auxiliaryLabel d y) d.rx
      d.stagePrefixRows true + 2)) +
  (lookupCost
    (d.stagePrefixRows + (order j).val*d.rx + auxiliaryLabel d y%d.rx)
    d.rawWidth ((x/d.uniform)/d.fullDivisor) d.rawBits.length +
    workLength (fullAuxiliaryPreLookup d x y order j) + 43)

theorem full_auxiliary_bounded (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb))
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (hwidth : 0 < d.rx)
    (hj : j.val = auxiliaryLabel d y / d.rx + d.nv)
    (hcolumn : x / d.uniform < d.fullBoundary)
    (h₁ : d.rowBoundary₁ ≤ y)
    (h₂ : d.rowBoundary₂ ≤ y-d.rowBoundary₁)
    (haux : d.rowBoundary₃ ≤ y-d.rowBoundary₁-d.rowBoundary₂) :
    let B := afterRowClear (fullAuxiliaryRowBank d x y)
    let pre := orderPreLookup d order j (auxiliaryLabel d y) true B
    ∃ t ≤ (copyCost x y + fullColumnCost d x + 1) +
        ((auxiliaryRowCost d y+1) +
          rowClearCost (fullAuxiliaryRowBank d x y) +
          (orderBound order j (auxiliaryLabel d y) d.rx
            d.stagePrefixRows true + 2)) +
        (lookupCost
          (d.stagePrefixRows + (order j).val*d.rx +
            auxiliaryLabel d y%d.rx)
          d.rawWidth ((x/d.uniform)/d.fullDivisor)
          d.rawBits.length + workLength pre + 43),
      run t (cfg (some start) initial (cellBank d x y [])) =
        cfg none initial
          (cellBank d x y
            [d.rawBits[(d.stagePrefixRows + (order j).val*d.rx +
              auxiliaryLabel d y%d.rx)*d.rawWidth+
              ((x/d.uniform)/d.fullDivisor)]?.getD false]) := by
  have hprefix := full_prefix_bounded d x y hcolumn
  have hr := MatrixWeightedRowController.auxiliary_controller_run
    (fullCore d x y) y d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
    d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃
    h₁ h₂ haux
  simp only [fullCore] at hr
  rw [full_row_seed_frame d x y []] at hr
  have hinput := auxiliary_order_frame_full d order horder x y
  let B := afterRowClear (fullAuxiliaryRowBank d x y)
  have hwork : ∀ k : Fin 10, k ≠ 0 → k ≠ 1 → k ≠ 2 →
      k ≠ 6 → k ≠ 7 → B (lookupSlots k) = [] := by
    intro k hk0 hk1 hk2 hk6 hk7
    fin_cases k <;> simp_all [lookupSlots] <;> rfl
  have hB : ∀ k, (∀ i : Fin 41, workSlot i ≠ k) →
      B k = cellBank d x y [] k := by
    intro k hk
    have hnot : ¬ ∃ i : Fin 41, workSlot i = k := by
      rintro ⟨i, hi⟩
      exact hk i hi
    cases k with
    | inl k =>
        fin_cases k <;> first | rfl | (exfalso; exact hnot (by decide))
    | inr k => fin_cases k <;> rfl
  have h := ordered_branch_bounded d x y order j
    (auxiliaryLabel d y) ((x/d.uniform)/d.fullDivisor) true
    (fullCore d x y) (auxiliaryRowResult d (fullCore d x y) y)
    (.column (.terminal false)) 3
    (copyCost x y + fullColumnCost d x + 1)
    (auxiliaryRowCost d y)
    horder (by decide) (by rfl) hwidth (by simpa using hj)
    (by simpa only [afterFullColumn, fullCore] using hprefix)
    hr hinput (by rfl) hwork hB
  exact h

theorem diagonal_vertex_bounded (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb))
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (hwidth : 0 < d.rx)
    (hj : j.val = vertexLabel d y / d.rx)
    (hcolumn : d.fullBoundary ≤ x / d.uniform)
    (h₁ : d.rowBoundary₁ ≤ y)
    (h₂ : d.rowBoundary₂ ≤ y-d.rowBoundary₁)
    (hvertex : y-d.rowBoundary₁-d.rowBoundary₂ < d.rowBoundary₃) :
    let B := afterRowClear (diagonalVertexRowBank d x y)
    let pre := orderPreLookup d order j (vertexLabel d y) false B
    ∃ t ≤ (copyCost x y + diagonalColumnCost d x +
          diagonalAddressCost d x) +
        ((vertexRowCost d y+1) +
          rowClearCost (diagonalVertexRowBank d x y) +
          (orderBound order j (vertexLabel d y) d.rx
            d.stagePrefixRows false + 2)) +
        (lookupCost
          (d.stagePrefixRows + (order j).val*d.rx +
            vertexLabel d y%d.rx)
          d.rawWidth (diagonalColumnValue d x)
          d.rawBits.length + workLength pre + 43),
      run t (cfg (some start) initial (cellBank d x y [])) =
        cfg none initial
          (cellBank d x y
            [d.rawBits[(d.stagePrefixRows + (order j).val*d.rx +
              vertexLabel d y%d.rx)*d.rawWidth+
              diagonalColumnValue d x]?.getD false]) := by
  have hprefix := diagonal_prefix_bounded d x y hcolumn
  have hr := MatrixWeightedRowController.vertex_controller_run
    (diagonalCore d x y) y d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
    d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃
    h₁ h₂ hvertex
  simp only [diagonalCore] at hr
  rw [diagonal_row_seed_frame d x y
    (MatrixWeightedDiagonalMachine.rawValue (diagonalCode d x)
      d.wordBase d.cy d.s d.binBase) []] at hr
  have hinput := vertex_order_frame_diagonal d order horder x y
  let B := afterRowClear (diagonalVertexRowBank d x y)
  have hwork : ∀ k : Fin 10, k ≠ 0 → k ≠ 1 → k ≠ 2 →
      k ≠ 6 → k ≠ 7 → B (lookupSlots k) = [] := by
    intro k hk0 hk1 hk2 hk6 hk7
    fin_cases k <;> simp_all [lookupSlots] <;> rfl
  have hB : ∀ k, (∀ i : Fin 41, workSlot i ≠ k) →
      B k = cellBank d x y [] k := by
    intro k hk
    have hnot : ¬ ∃ i : Fin 41, workSlot i = k := by
      rintro ⟨i, hi⟩
      exact hk i hi
    cases k with
    | inl k =>
        fin_cases k <;> first | rfl | (exfalso; exact hnot (by decide))
    | inr k => fin_cases k <;> rfl
  have h := ordered_branch_bounded d x y order j
    (vertexLabel d y) (diagonalColumnValue d x) false
    (diagonalCore d x y) (vertexRowResult d (diagonalCore d x y) y)
    (.diagonal .idle) 2
    (copyCost x y + diagonalColumnCost d x + diagonalAddressCost d x)
    (vertexRowCost d y)
    horder (by decide) (by rfl) hwidth (by simpa using hj)
    hprefix hr hinput (by rfl) hwork hB
  exact h

theorem diagonal_auxiliary_bounded (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb))
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (hwidth : 0 < d.rx)
    (hj : j.val = auxiliaryLabel d y / d.rx + d.nv)
    (hcolumn : d.fullBoundary ≤ x / d.uniform)
    (h₁ : d.rowBoundary₁ ≤ y)
    (h₂ : d.rowBoundary₂ ≤ y-d.rowBoundary₁)
    (haux : d.rowBoundary₃ ≤ y-d.rowBoundary₁-d.rowBoundary₂) :
    let B := afterRowClear (diagonalAuxiliaryRowBank d x y)
    let pre := orderPreLookup d order j (auxiliaryLabel d y) true B
    ∃ t ≤ (copyCost x y + diagonalColumnCost d x +
          diagonalAddressCost d x) +
        ((auxiliaryRowCost d y+1) +
          rowClearCost (diagonalAuxiliaryRowBank d x y) +
          (orderBound order j (auxiliaryLabel d y) d.rx
            d.stagePrefixRows true + 2)) +
        (lookupCost
          (d.stagePrefixRows + (order j).val*d.rx +
            auxiliaryLabel d y%d.rx)
          d.rawWidth (diagonalColumnValue d x)
          d.rawBits.length + workLength pre + 43),
      run t (cfg (some start) initial (cellBank d x y [])) =
        cfg none initial
          (cellBank d x y
            [d.rawBits[(d.stagePrefixRows + (order j).val*d.rx +
              auxiliaryLabel d y%d.rx)*d.rawWidth+
              diagonalColumnValue d x]?.getD false]) := by
  have hprefix := diagonal_prefix_bounded d x y hcolumn
  have hr := MatrixWeightedRowController.auxiliary_controller_run
    (diagonalCore d x y) y d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
    d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃
    h₁ h₂ haux
  simp only [diagonalCore] at hr
  rw [diagonal_row_seed_frame d x y
    (MatrixWeightedDiagonalMachine.rawValue (diagonalCode d x)
      d.wordBase d.cy d.s d.binBase) []] at hr
  have hinput := auxiliary_order_frame_diagonal d order horder x y
  let B := afterRowClear (diagonalAuxiliaryRowBank d x y)
  have hwork : ∀ k : Fin 10, k ≠ 0 → k ≠ 1 → k ≠ 2 →
      k ≠ 6 → k ≠ 7 → B (lookupSlots k) = [] := by
    intro k hk0 hk1 hk2 hk6 hk7
    fin_cases k <;> simp_all [lookupSlots] <;> rfl
  have hB : ∀ k, (∀ i : Fin 41, workSlot i ≠ k) →
      B k = cellBank d x y [] k := by
    intro k hk
    have hnot : ¬ ∃ i : Fin 41, workSlot i = k := by
      rintro ⟨i, hi⟩
      exact hk i hi
    cases k with
    | inl k =>
        fin_cases k <;> first | rfl | (exfalso; exact hnot (by decide))
    | inr k => fin_cases k <;> rfl
  have h := ordered_branch_bounded d x y order j
    (auxiliaryLabel d y) (diagonalColumnValue d x) true
    (diagonalCore d x y)
    (auxiliaryRowResult d (diagonalCore d x y) y)
    (.diagonal .idle) 3
    (copyCost x y + diagonalColumnCost d x + diagonalAddressCost d x)
    (auxiliaryRowCost d y)
    horder (by decide) (by rfl) hwidth (by simpa using hj)
    hprefix hr hinput (by rfl) hwork hB
  exact h

noncomputable def diagonalVertexCost (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb)) : ℕ :=
  (copyCost x y + diagonalColumnCost d x + diagonalAddressCost d x) +
  ((vertexRowCost d y+1) +
    rowClearCost (diagonalVertexRowBank d x y) +
    (orderBound order j (vertexLabel d y) d.rx
      d.stagePrefixRows false + 2)) +
  (lookupCost
    (d.stagePrefixRows + (order j).val*d.rx + vertexLabel d y%d.rx)
    d.rawWidth (diagonalColumnValue d x) d.rawBits.length +
    workLength (diagonalVertexPreLookup d x y order j) + 43)

noncomputable def diagonalAuxiliaryCost (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb)) : ℕ :=
  (copyCost x y + diagonalColumnCost d x + diagonalAddressCost d x) +
  ((auxiliaryRowCost d y+1) +
    rowClearCost (diagonalAuxiliaryRowBank d x y) +
    (orderBound order j (auxiliaryLabel d y) d.rx
      d.stagePrefixRows true + 2)) +
  (lookupCost
    (d.stagePrefixRows + (order j).val*d.rx + auxiliaryLabel d y%d.rx)
    d.rawWidth (diagonalColumnValue d x) d.rawBits.length +
    workLength (diagonalAuxiliaryPreLookup d x y order j) + 43)

noncomputable def directCaseCost (d : Input) (x y : ℕ) : ℕ :=
  max (max (fullFullCost d x y) (fullTemplateCost d x y))
    (max (diagonalFullCost d x y) (diagonalTemplateCost d x y))

noncomputable def orderedCaseCost (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb)) : ℕ :=
  max (max (fullVertexCost d x y order j)
        (fullAuxiliaryCost d x y order j))
      (max (diagonalVertexCost d x y order j)
        (diagonalAuxiliaryCost d x y order j))

/-- A maximum of explicit charged stage-sums, not of unknown halting times. -/
noncomputable def cellCost (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb) : ℕ :=
  max (directCaseCost d x y)
    (Finset.univ.sup (fun j : Fin (d.nv+d.nb) =>
      orderedCaseCost d x y order j))

noncomputable def commonCost (d : Input) (rows cols : ℕ)
    (order : Construction.ItemOrder d.nv d.nb) : ℕ :=
  Finset.univ.sup (fun x : Fin rows =>
    Finset.univ.sup (fun y : Fin cols =>
      cellCost d x.val y.val order))

theorem cellCost_le_common (d : Input) (rows cols : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (x : Fin rows) (y : Fin cols) :
    cellCost d x.val y.val order ≤ commonCost d rows cols order := by
  have hy : cellCost d x.val y.val order ≤
      Finset.univ.sup (fun z : Fin cols =>
        cellCost d x.val z.val order) :=
    Finset.le_sup (s := (Finset.univ : Finset (Fin cols)))
      (f := fun z => cellCost d x.val z.val order) (Finset.mem_univ y)
  have hx : Finset.univ.sup (fun z : Fin cols =>
      cellCost d x.val z.val order) ≤ commonCost d rows cols order :=
    Finset.le_sup (s := (Finset.univ : Finset (Fin rows)))
      (f := fun z => Finset.univ.sup (fun w : Fin cols =>
        cellCost d z.val w.val order)) (Finset.mem_univ x)
  exact hy.trans hx

theorem fullAuxiliaryCost_eq (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb)) :
    (let B := afterRowClear (fullAuxiliaryRowBank d x y)
     let pre := orderPreLookup d order j (auxiliaryLabel d y) true B
     (copyCost x y + fullColumnCost d x + 1) +
       ((auxiliaryRowCost d y+1) +
         rowClearCost (fullAuxiliaryRowBank d x y) +
         (orderBound order j (auxiliaryLabel d y) d.rx
           d.stagePrefixRows true + 2)) +
       (lookupCost
         (d.stagePrefixRows + (order j).val*d.rx +
           auxiliaryLabel d y%d.rx)
         d.rawWidth ((x/d.uniform)/d.fullDivisor)
         d.rawBits.length + workLength pre + 43)) =
       fullAuxiliaryCost d x y order j := by
  rfl

theorem diagonalVertexCost_eq (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb)) :
    (let B := afterRowClear (diagonalVertexRowBank d x y)
     let pre := orderPreLookup d order j (vertexLabel d y) false B
     (copyCost x y + diagonalColumnCost d x +
           diagonalAddressCost d x) +
       ((vertexRowCost d y+1) +
         rowClearCost (diagonalVertexRowBank d x y) +
         (orderBound order j (vertexLabel d y) d.rx
           d.stagePrefixRows false + 2)) +
       (lookupCost
         (d.stagePrefixRows + (order j).val*d.rx +
           vertexLabel d y%d.rx)
         d.rawWidth (diagonalColumnValue d x)
         d.rawBits.length + workLength pre + 43)) =
       diagonalVertexCost d x y order j := by
  rfl

theorem diagonalAuxiliaryCost_eq (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb)) :
    (let B := afterRowClear (diagonalAuxiliaryRowBank d x y)
     let pre := orderPreLookup d order j (auxiliaryLabel d y) true B
     (copyCost x y + diagonalColumnCost d x +
           diagonalAddressCost d x) +
       ((auxiliaryRowCost d y+1) +
         rowClearCost (diagonalAuxiliaryRowBank d x y) +
         (orderBound order j (auxiliaryLabel d y) d.rx
           d.stagePrefixRows true + 2)) +
       (lookupCost
         (d.stagePrefixRows + (order j).val*d.rx +
           auxiliaryLabel d y%d.rx)
         d.rawWidth (diagonalColumnValue d x)
         d.rawBits.length + workLength pre + 43)) =
       diagonalAuxiliaryCost d x y order j := by
  rfl

theorem full_auxiliary_cost_bounded (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb))
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (hwidth : 0 < d.rx)
    (hj : j.val = auxiliaryLabel d y / d.rx + d.nv)
    (hcolumn : x / d.uniform < d.fullBoundary)
    (h₁ : d.rowBoundary₁ ≤ y)
    (h₂ : d.rowBoundary₂ ≤ y-d.rowBoundary₁)
    (haux : d.rowBoundary₃ ≤ y-d.rowBoundary₁-d.rowBoundary₂) :
    ∃ t ≤ fullAuxiliaryCost d x y order j,
      run t (cfg (some start) initial (cellBank d x y [])) =
        cfg none initial
          (cellBank d x y
            [d.rawBits[(d.stagePrefixRows + (order j).val*d.rx +
              auxiliaryLabel d y%d.rx)*d.rawWidth+
              ((x/d.uniform)/d.fullDivisor)]?.getD false]) := by
  obtain ⟨t, ht, he⟩ := full_auxiliary_bounded d x y order j
    horder hwidth hj hcolumn h₁ h₂ haux
  refine ⟨t, ?_, he⟩
  simpa only [fullAuxiliaryCost_eq] using ht

theorem diagonal_vertex_cost_bounded (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb))
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (hwidth : 0 < d.rx)
    (hj : j.val = vertexLabel d y / d.rx)
    (hcolumn : d.fullBoundary ≤ x / d.uniform)
    (h₁ : d.rowBoundary₁ ≤ y)
    (h₂ : d.rowBoundary₂ ≤ y-d.rowBoundary₁)
    (hvertex : y-d.rowBoundary₁-d.rowBoundary₂ < d.rowBoundary₃) :
    ∃ t ≤ diagonalVertexCost d x y order j,
      run t (cfg (some start) initial (cellBank d x y [])) =
        cfg none initial
          (cellBank d x y
            [d.rawBits[(d.stagePrefixRows + (order j).val*d.rx +
              vertexLabel d y%d.rx)*d.rawWidth+
              diagonalColumnValue d x]?.getD false]) := by
  obtain ⟨t, ht, he⟩ := diagonal_vertex_bounded d x y order j
    horder hwidth hj hcolumn h₁ h₂ hvertex
  refine ⟨t, ?_, he⟩
  simpa only [diagonalVertexCost_eq] using ht

theorem diagonal_auxiliary_cost_bounded (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb))
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (hwidth : 0 < d.rx)
    (hj : j.val = auxiliaryLabel d y / d.rx + d.nv)
    (hcolumn : d.fullBoundary ≤ x / d.uniform)
    (h₁ : d.rowBoundary₁ ≤ y)
    (h₂ : d.rowBoundary₂ ≤ y-d.rowBoundary₁)
    (haux : d.rowBoundary₃ ≤ y-d.rowBoundary₁-d.rowBoundary₂) :
    ∃ t ≤ diagonalAuxiliaryCost d x y order j,
      run t (cfg (some start) initial (cellBank d x y [])) =
        cfg none initial
          (cellBank d x y
            [d.rawBits[(d.stagePrefixRows + (order j).val*d.rx +
              auxiliaryLabel d y%d.rx)*d.rawWidth+
              diagonalColumnValue d x]?.getD false]) := by
  obtain ⟨t, ht, he⟩ := diagonal_auxiliary_bounded d x y order j
    horder hwidth hj hcolumn h₁ h₂ haux
  refine ⟨t, ?_, he⟩
  simpa only [diagonalAuxiliaryCost_eq] using ht

end EthInapproximability.CurrentPaper.MatrixWeightedEntryCost
