import Paper2.NavJoin
import CurrentAdditive.CompactRationalRecursiveBase

/-! Physical navigation of arbitrary indexed rational base generator codes.
The existing level navigator is a fixed machine; its published entry lemmas
were specialized to the seed code.  Here its two top-level selectors are
bound directly to `recursiveCodes` with arbitrary base codes. -/

namespace Paper2.GenericCodeNavigation

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSource
open Paper2.GeneratorSerialization
open Paper2.NavJoin
open EthInapproximability.CurrentPaper.BitMachineRawSequence (leftLabel)

def codes (n s q₁ q₂ w Q : ℕ) (baseRow baseCol : Code) (k : ℕ) :
    Code × Code := recursiveCodes n s q₁ q₂ w Q baseRow baseCol k

theorem row_succ_eq (n s q₁ q₂ w Q : ℕ) (baseRow baseCol : Code)
    (hQ : 0 < Q) (k : ℕ) :
    (codes n s q₁ q₂ w Q baseRow baseCol (k + 1)).1 =
      .append
        (.append (.ticket w)
          (taggedCode q₁ q₂ s (codes n s q₁ q₂ w Q baseRow baseCol k).2))
        (copies (Q - 1)
          (.append (.ticket w)
            (taggedCode q₁ q₂ s (codes n s q₁ q₂ w Q baseRow baseCol k).2))) := by
  obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
  rfl

theorem col_succ_eq (n s q₁ q₂ w Q : ℕ) (baseRow baseCol : Code)
    (hw : 0 < w) (k : ℕ) :
    (codes n s q₁ q₂ w Q baseRow baseCol (k + 1)).2 =
      .append (.ticket Q)
        (.append (graphRowsCode (V := Fin n) q₁ q₂ s
          (codes n s q₁ q₂ w Q baseRow baseCol k).1)
          (copies (w - 1)
            (graphRowsCode (V := Fin n) q₁ q₂ s
              (codes n s q₁ q₂ w Q baseRow baseCol k).1))) := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  rfl

theorem entry_code_run (n s q₁ q₂ w Q : ℕ) (baseRow baseCol : Code)
    (hQ : 0 < Q) (k : ℕ) :
    let c := codes n s q₁ q₂ w Q baseRow baseCol k
    let E : Code := .append (.ticket w) (taggedCode q₁ q₂ s c.2)
    let row := (codes n s q₁ q₂ w Q baseRow baseCol (k + 1)).1
    ∃ t ≤ Paper2.LevelNav.leftBound E (copies (Q - 1) E),
      ((advance Paper2.LevelNav.leftProgram)^[t])
        (⟨some Paper2.LevelNav.leftStart, Paper2.LevelNav.leftCtl,
          Paper2.ChildNav.nb [] [] [] (encodeCode row) []⟩ :
          TM2.Cfg (fun _ : Paper2.ChildNav.Stack => Bool) _ _) =
        ⟨none, Paper2.LevelNav.leftCtl,
          Paper2.ChildNav.nb [] [] [] (encodeCode row) (encodeCode E)⟩ := by
  intro c E row
  have hr := row_succ_eq n s q₁ q₂ w Q baseRow baseCol hQ k
  have h : row = .append E (copies (Q - 1) E) := hr
  rw [h]
  exact Paper2.LevelNav.left_run E (copies (Q - 1) E)

theorem rawrow_code_run (n s q₁ q₂ w Q : ℕ) (baseRow baseCol : Code)
    (hw : 0 < w) (k : ℕ) :
    let c := codes n s q₁ q₂ w Q baseRow baseCol k
    let G : Code := graphRowsCode (V := Fin n) q₁ q₂ s c.1
    let col := (codes n s q₁ q₂ w Q baseRow baseCol (k + 1)).2
    ∃ t ≤ Paper2.LevelNav.midBound (.ticket Q) G (copies (w - 1) G),
      ((advance Paper2.LevelNav.midProgram)^[t])
        (⟨some Paper2.LevelNav.midStart, Paper2.LevelNav.midCtl,
          Paper2.ChildNav.nb [] [] [] (encodeCode col) []⟩ :
          TM2.Cfg (fun _ : Paper2.ChildNav.Stack => Bool) _ _) =
        ⟨none, Paper2.LevelNav.midCtl,
          Paper2.ChildNav.nb [] [] [] (encodeCode col) (encodeCode G)⟩ := by
  intro c G col
  have hc := col_succ_eq n s q₁ q₂ w Q baseRow baseCol hw k
  have h : col = .append (.ticket Q) (.append G (copies (w - 1) G)) := hc
  rw [h]
  exact Paper2.LevelNav.mid_run (.ticket Q) G (copies (w - 1) G)

def outVec (n s q₁ q₂ w Q : ℕ) (baseRow baseCol : Code)
    (k : ℕ) : Fin 9 → List Bool :=
  let c := codes n s q₁ q₂ w Q baseRow baseCol k
  let c' := codes n s q₁ q₂ w Q baseRow baseCol (k + 1)
  ![encodeCode c'.1, encodeCode c'.2,
    encodeCode (.append (.ticket w) (taggedCode q₁ q₂ s c.2)),
    encodeCode (graphRowsCode (V := Fin n) q₁ q₂ s c.1),
    encodeCode c.2, encodeCode c.1,
    encodeCode (copies (s + 1) c.2),
    encodeCode (outerCode q₁ q₂ s c.2),
    encodeCode (.append (.ticket q₁) c.1)]

def joinBound (n s q₁ q₂ w Q : ℕ) (baseRow baseCol : Code)
    (k : ℕ) : ℕ :=
  let c := codes n s q₁ q₂ w Q baseRow baseCol k
  let E : Code := .append (.ticket w) (taggedCode q₁ q₂ s c.2)
  let G : Code := graphRowsCode (V := Fin n) q₁ q₂ s c.1
  Paper2.LevelNav.leftBound E (copies (Q - 1) E) +
    Paper2.LevelNav.midBound (.ticket Q) G (copies (w - 1) G) +
    LevelNavCol.bound q₁ q₂ s w c.2 + LevelNavRow.bound n q₁ q₂ s c.1 +
    LevelNavCodes.cpsBound q₁ q₂ s w c.2 +
    LevelNavCodes.outerBound q₁ q₂ s w c.2 +
    LevelNavCodes.tentryBound n q₁ q₂ s c.1 + 6

/-- The same fixed physical navigator, now for arbitrary base generator
syntax. Every one of its seven output cells is computed and charged. -/
theorem join_run (n s q₁ q₂ w Q : ℕ) (baseRow baseCol : Code)
    (hQ : 0 < Q) (hw : 0 < w) (hs : 0 < s) (hq₂ : 0 < q₂)
    (k : ℕ) :
    ∃ t ≤ joinBound n s q₁ q₂ w Q baseRow baseCol k,
      ((advance Paper2.NavJoin.program)^[t])
        (⟨some Paper2.NavJoin.startLabel, Paper2.NavJoin.ctl,
          Paper2.NavJoin.jb
            (Paper2.NavJoin.inVec
              (encodeCode (codes n s q₁ q₂ w Q baseRow baseCol (k + 1)).1)
              (encodeCode (codes n s q₁ q₂ w Q baseRow baseCol (k + 1)).2))⟩ :
          TM2.Cfg (fun _ : Paper2.NavJoin.Stack => Bool) _ _) =
        ⟨none, Paper2.NavJoin.ctl,
          Paper2.NavJoin.jb (outVec n s q₁ q₂ w Q baseRow baseCol k)⟩ := by
  let c := codes n s q₁ q₂ w Q baseRow baseCol k
  let c' := codes n s q₁ q₂ w Q baseRow baseCol (k + 1)
  let R := encodeCode c'.1
  let C := encodeCode c'.2
  let E : Code := .append (.ticket w) (taggedCode q₁ q₂ s c.2)
  let G : Code := graphRowsCode (V := Fin n) q₁ q₂ s c.1
  let eE := encodeCode E
  let eG := encodeCode G
  let eCol := encodeCode c.2
  let eRow := encodeCode c.1
  let eCps := encodeCode (copies (s + 1) c.2)
  let eOut := encodeCode (outerCode q₁ q₂ s c.2)
  let eTe := encodeCode (.append (.ticket q₁) c.1)
  let v0 : Fin 9 → List Bool := ![R, C, [], [], [], [], [], [], []]
  let v1 : Fin 9 → List Bool := ![R, C, eE, [], [], [], [], [], []]
  let v2 : Fin 9 → List Bool := ![R, C, eE, eG, [], [], [], [], []]
  let v3 : Fin 9 → List Bool := ![R, C, eE, eG, eCol, [], [], [], []]
  let v4 : Fin 9 → List Bool := ![R, C, eE, eG, eCol, eRow, [], [], []]
  let v5 : Fin 9 → List Bool := ![R, C, eE, eG, eCol, eRow, eCps, [], []]
  let v6 : Fin 9 → List Bool := ![R, C, eE, eG, eCol, eRow, eCps, eOut, []]
  let v7 : Fin 9 → List Bool := ![R, C, eE, eG, eCol, eRow, eCps, eOut, eTe]
  obtain ⟨t1, ht1, p1⟩ := entry_code_run n s q₁ q₂ w Q baseRow baseCol hQ k
  obtain ⟨t2, ht2, p2⟩ := rawrow_code_run n s q₁ q₂ w Q baseRow baseCol hw k
  obtain ⟨t3, ht3, p3⟩ := LevelNavCol.col_run q₁ q₂ s w c.2
  obtain ⟨t4, ht4, p4⟩ := LevelNavRow.row_run n q₁ q₂ s c.1
  obtain ⟨t5, ht5, p5⟩ := LevelNavCodes.cps_run q₁ q₂ s w c.2
  obtain ⟨t6, ht6, p6⟩ := LevelNavCodes.outer_run q₁ q₂ s w hs c.2
  obtain ⟨t7, ht7, p7⟩ := LevelNavCodes.tentry_run n q₁ q₂ s hq₂ c.1
  have l1 := Paper2.NavJoin.lift_run LevelNav.leftProgram 0 2 h02 _ _ _ t1
    R eE v0 v1 rfl rfl (by funext i; fin_cases i <;> rfl) p1
  have l2 := Paper2.NavJoin.lift_run LevelNav.midProgram 1 3 h13 _ _ _ t2
    C eG v1 v2 rfl rfl (by funext i; fin_cases i <;> rfl) p2
  have l3 := Paper2.NavJoin.lift_run LevelNavCol.program 2 4 h24 _ _ _ t3
    eE eCol v2 v3 rfl rfl (by funext i; fin_cases i <;> rfl) p3
  have l4 := Paper2.NavJoin.lift_run LevelNavRow.program 3 5 h35 _ _ _ t4
    eG eRow v3 v4 rfl rfl (by funext i; fin_cases i <;> rfl) p4
  have l5 := Paper2.NavJoin.lift_run LevelNavCodes.cpsProgram 2 6 h26 _ _ _ t5
    eE eCps v4 v5 rfl rfl (by funext i; fin_cases i <;> rfl) p5
  have l6 := Paper2.NavJoin.lift_run LevelNavCodes.outerProgram 2 7 h27 _ _ _ t6
    eE eOut v5 v6 rfl rfl (by funext i; fin_cases i <;> rfl) p6
  have l7 := Paper2.NavJoin.lift_run LevelNavCodes.tentryProgram 3 8 h38 _ _ _ t7
    eG eTe v6 v7 rfl rfl (by funext i; fin_cases i <;> rfl) p7
  obtain ⟨s2, hs2, q2⟩ := BitMachineRawSequence.runs navE navG LevelNav.leftStart
    LevelNav.midStart LevelNav.leftCtl LevelNav.leftCtl LevelNav.midCtl LevelNav.midCtl
    _ _ _ _ _ l1 l2
  obtain ⟨s3, hs3, q3⟩ := BitMachineRawSequence.runs j2 navCol
    (leftLabel LevelNav.leftStart) LevelNavCol.startLabel
    ctl2 ctl2 LevelNavCol.ctl LevelNavCol.ctl _ _ _ _ _ q2 l3
  obtain ⟨s4, hs4, q4⟩ := BitMachineRawSequence.runs j3 navRow
    (leftLabel (leftLabel LevelNav.leftStart)) LevelNavRow.startLabel
    ctl3 ctl3 LevelNavRow.ctl LevelNavRow.ctl _ _ _ _ _ q3 l4
  obtain ⟨s5, hs5, q5⟩ := BitMachineRawSequence.runs j4 navCps
    (leftLabel (leftLabel (leftLabel LevelNav.leftStart)))
    LevelNavCodes.cpsStart ctl4 ctl4 LevelNavCodes.cpsCtl LevelNavCodes.cpsCtl
    _ _ _ _ _ q4 l5
  obtain ⟨s6, hs6, q6⟩ := BitMachineRawSequence.runs j5 navOuter
    (leftLabel (leftLabel (leftLabel (leftLabel LevelNav.leftStart))))
    LevelNavCodes.outerStart ctl5 ctl5 LevelNavCodes.outerCtl LevelNavCodes.outerCtl
    _ _ _ _ _ q5 l6
  obtain ⟨s7, hs7, q7⟩ := BitMachineRawSequence.runs j6 navTentry
    (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel LevelNav.leftStart)))))
    LevelNavCodes.tentryStart ctl6 ctl6 LevelNavCodes.tentryCtl LevelNavCodes.tentryCtl
    _ _ _ _ _ q6 l7
  refine ⟨s7, ?_, q7⟩
  have ht3' : t3 ≤ LevelNavCol.bound q₁ q₂ s w
      (codes n s q₁ q₂ w Q baseRow baseCol k).2 := ht3
  have ht4' : t4 ≤ LevelNavRow.bound n q₁ q₂ s
      (codes n s q₁ q₂ w Q baseRow baseCol k).1 := ht4
  have ht5' : t5 ≤ LevelNavCodes.cpsBound q₁ q₂ s w
      (codes n s q₁ q₂ w Q baseRow baseCol k).2 := ht5
  have ht6' : t6 ≤ LevelNavCodes.outerBound q₁ q₂ s w
      (codes n s q₁ q₂ w Q baseRow baseCol k).2 := ht6
  have ht7' : t7 ≤ LevelNavCodes.tentryBound n q₁ q₂ s
      (codes n s q₁ q₂ w Q baseRow baseCol k).1 := ht7
  simp only [joinBound]
  omega

#print axioms row_succ_eq
#print axioms col_succ_eq
#print axioms entry_code_run
#print axioms rawrow_code_run
#print axioms join_run

end Paper2.GenericCodeNavigation
