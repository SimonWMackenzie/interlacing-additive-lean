import Paper2.LevelNavCodes

/-! Unit 3, segment (1), second half: ONE fixed program on ONE bank that
produces, from the serialized level-`k+1` codes `row_{k+1}` and `col_{k+1}`,
every sub-code the level-`k` request phases consume:

| cell | content at exit | producer (frozen / this lane) |
|---|---|---|
| 0 | `row_{k+1}` (retained) | input |
| 1 | `col_{k+1}` (retained) | input |
| 2 | `E_k = append (ticket w) (taggedCode col_k)` | `LevelNav.leftProgram` on cell 0 |
| 3 | `G_k = graphRowsCode row_k` | `LevelNav.midProgram` on cell 1 |
| 4 | `col_k` | `LevelNavCol.program` on cell 2 |
| 5 | `row_k` | `LevelNavRow.program` on cell 3 |
| 6 | `copies (s+1) col_k` | `LevelNavCodes.cpsProgram` on cell 2 |
| 7 | `outerCode col_k` | `LevelNavCodes.outerProgram` on cell 2 |
| 8 | `append (ticket q₁) row_k` | `LevelNavCodes.tentryProgram` on cell 3 |

Bank: the `ChildNav` extraction scratch `CE` (blank at entry and exit)
beside nine named cells. Each navigation is the frozen program run through
the production pure stack embedding (`BitMachineStackEmbedding.stackStmt`)
whose `inp` is the source cell and whose `outp` is the target cell; the
seven phases are sequenced by the production `BitMachineRawSequence`.
`join_run_embedded` transports the whole run into ANY ambient bank through
ANY injective relabelling, so the consumer cells of the later one-bank
request join can be chosen as the targets directly (no further copy). -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Paper2.NavJoin

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource
open ChildNav (nb)
open BitMachineRawSequence (leftLabel)

abbrev Stack := ChildNav.CE ⊕ Fin 9

/-- The join bank: blank extraction scratch beside nine named cells. -/
def jb (v : Fin 9 → List Bool) : Stack → List Bool := Sum.elim (fun _ => []) v

theorem jb_update (v : Fin 9 → List Bool) (b : Fin 9) (x : List Bool) :
    jb (Function.update v b x) = Function.update (jb v) (.inr b) x := by
  funext j
  rcases j with j | j
  · simp [jb]
  · simp [jb, Function.update_apply]

/-- Navigation embedding: scratch to scratch, `inp ↦ a`, `outp ↦ b`. -/
def nav (a b : Fin 9) (h : a ≠ b) : ChildNav.Stack ↪ Stack :=
  ⟨Sum.map id ![a, b], by
    intro x y hxy
    rcases x with x | x <;> rcases y with y | y
    · simpa using hxy
    · simp at hxy
    · simp at hxy
    · have hxy' : ![a, b] x = ![a, b] y := by simpa using hxy
      fin_cases x <;> fin_cases y <;> simp_all [eq_comm]⟩

def lift {L V : Type*} (ι : ChildNav.Stack ↪ Stack)
    (P : L → TM2.Stmt (fun _ : ChildNav.Stack => Bool) L V) :
    L → TM2.Stmt (fun _ : Stack => Bool) L V :=
  fun l => stackStmt ι (P l)

theorem nb_ce (inp out : List Bool) (c : ChildNav.CE) :
    nb [] [] [] inp out (.inl c) = [] := by
  rcases c with (x | x) | x <;> fin_cases x <;> rfl

/-- A checked `ChildNav` navigation run, transported to the join bank. -/
theorem lift_run {L V : Type*} (P : L → TM2.Stmt (fun _ : ChildNav.Stack => Bool) L V)
    (a b : Fin 9) (h : a ≠ b) (l : L) (c c' : V) (t : ℕ) (inp out : List Bool)
    (v v' : Fin 9 → List Bool) (ha : v a = inp) (hb : v b = [])
    (hv' : Function.update v b out = v')
    (hrun : ((advance P)^[t]) (⟨some l, c, nb [] [] [] inp []⟩ :
        TM2.Cfg (fun _ : ChildNav.Stack => Bool) L V) =
      ⟨none, c', nb [] [] [] inp out⟩) :
    ((advance (lift (nav a b h) P))^[t]) (⟨some l, c, jb v⟩ :
        TM2.Cfg (fun _ : Stack => Bool) L V) =
      ⟨none, c', jb v'⟩ := by
  have hs := BitMachineStackRun.run (nav a b h) (jb v) P
    (⟨some l, c, nb [] [] [] inp []⟩ : TM2.Cfg (fun _ : ChildNav.Stack => Bool) L V) t
  rw [hrun] at hs
  have hstart : bank (nav a b h) (jb v) (nb [] [] [] inp []) = jb v := by
    apply bank_eq_self
    intro k
    rcases k with k | k
    · rw [nb_ce]; rfl
    · fin_cases k
      · exact ha.symm
      · exact hb.symm
  have hx : nb [] [] [] inp out = Function.update (nb [] [] [] inp []) ChildNav.outpC out :=
    (ChildNav.up_outp [] [] [] inp [] out).symm
  have hend : bank (nav a b h) (jb v) (nb [] [] [] inp out) = jb v' := by
    rw [hx, bank_update, hstart, ← hv', jb_update]
    rfl
  simp only [stackCfg] at hs
  rw [hstart, hend] at hs
  exact hs

/-! ### The seven lifted navigations and their sequence -/

theorem h02 : (0 : Fin 9) ≠ 2 := by decide
theorem h13 : (1 : Fin 9) ≠ 3 := by decide
theorem h24 : (2 : Fin 9) ≠ 4 := by decide
theorem h35 : (3 : Fin 9) ≠ 5 := by decide
theorem h26 : (2 : Fin 9) ≠ 6 := by decide
theorem h27 : (2 : Fin 9) ≠ 7 := by decide
theorem h38 : (3 : Fin 9) ≠ 8 := by decide

def navE := lift (nav 0 2 h02) LevelNav.leftProgram
def navG := lift (nav 1 3 h13) LevelNav.midProgram
def navCol := lift (nav 2 4 h24) LevelNavCol.program
def navRow := lift (nav 3 5 h35) LevelNavRow.program
def navCps := lift (nav 2 6 h26) LevelNavCodes.cpsProgram
def navOuter := lift (nav 2 7 h27) LevelNavCodes.outerProgram
def navTentry := lift (nav 3 8 h38) LevelNavCodes.tentryProgram

def ctl2 := (LevelNav.leftCtl, LevelNav.midCtl)
def ctl3 := (ctl2, LevelNavCol.ctl)
def ctl4 := (ctl3, LevelNavRow.ctl)
def ctl5 := (ctl4, LevelNavCodes.cpsCtl)
def ctl6 := (ctl5, LevelNavCodes.outerCtl)
def ctl := (ctl6, LevelNavCodes.tentryCtl)

def j2 := BitMachineRawSequence.program navE navG LevelNav.midStart LevelNav.leftCtl
  LevelNav.midCtl
def j3 := BitMachineRawSequence.program j2 navCol LevelNavCol.startLabel ctl2 LevelNavCol.ctl
def j4 := BitMachineRawSequence.program j3 navRow LevelNavRow.startLabel ctl3 LevelNavRow.ctl
def j5 := BitMachineRawSequence.program j4 navCps LevelNavCodes.cpsStart ctl4
  LevelNavCodes.cpsCtl
def j6 := BitMachineRawSequence.program j5 navOuter LevelNavCodes.outerStart ctl5
  LevelNavCodes.outerCtl
/-- The join: ONE fixed program (no parameter enters its labels or statements). -/
def program := BitMachineRawSequence.program j6 navTentry LevelNavCodes.tentryStart ctl6
  LevelNavCodes.tentryCtl

def startLabel := ChildNav.labelOf program
  (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel LevelNav.leftStart))))))

/-- Entry vector: the two serialized level-`k+1` codes, all else blank. -/
def inVec (R C : List Bool) : Fin 9 → List Bool := ![R, C, [], [], [], [], [], [], []]

/-- Exit vector at the actual codes. -/
def outVec (n p s q₁ q₂ w Q k : ℕ) : Fin 9 → List Bool :=
  let c := seedRecursiveCodes n p s q₁ q₂ w Q k
  let c' := seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)
  ![encodeCode c'.1, encodeCode c'.2,
    encodeCode (.append (.ticket w) (taggedCode q₁ q₂ s c.2)),
    encodeCode (graphRowsCode (V := Fin n) q₁ q₂ s c.1),
    encodeCode c.2, encodeCode c.1,
    encodeCode (copies (s + 1) c.2), encodeCode (outerCode q₁ q₂ s c.2),
    encodeCode (.append (.ticket q₁) c.1)]

def joinBound (n p s q₁ q₂ w Q k : ℕ) : ℕ :=
  let c := seedRecursiveCodes n p s q₁ q₂ w Q k
  let E : Code := .append (.ticket w) (taggedCode q₁ q₂ s c.2)
  let G : Code := graphRowsCode (V := Fin n) q₁ q₂ s c.1
  LevelNav.leftBound E (copies (Q - 1) E) + LevelNav.midBound (.ticket Q) G (copies (w - 1) G) +
    LevelNavCol.bound q₁ q₂ s w c.2 + LevelNavRow.bound n q₁ q₂ s c.1 +
    LevelNavCodes.cpsBound q₁ q₂ s w c.2 + LevelNavCodes.outerBound q₁ q₂ s w c.2 +
    LevelNavCodes.tentryBound n q₁ q₂ s c.1 + 6

/-- Segment (1): the level-`k` sub-codes from the level-`k+1` codes, one fixed
program, exact exit bank. Premises: positivity of `Q`, `w`, `s`, `q₂` only. -/
theorem join_run {n p s q₁ q₂ w Q : ℕ} (hQ : 0 < Q) (hw : 0 < w) (hs : 0 < s)
    (hq₂ : 0 < q₂) (k : ℕ) :
    ∃ t ≤ joinBound n p s q₁ q₂ w Q k,
      ((advance program)^[t])
        (⟨some startLabel, ctl,
          jb (inVec (encodeCode (seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)).1)
            (encodeCode (seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)).2))⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, ctl, jb (outVec n p s q₁ q₂ w Q k)⟩ := by
  let c := seedRecursiveCodes n p s q₁ q₂ w Q k
  let c' := seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)
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
  obtain ⟨t1, ht1, p1⟩ := LevelNav.entry_code_run (n := n) (p := p) (s := s) (q₁ := q₁)
    (q₂ := q₂) (w := w) hQ k
  obtain ⟨t2, ht2, p2⟩ := LevelNav.rawrow_code_run (n := n) (p := p) (s := s) (q₁ := q₁)
    (q₂ := q₂) (Q := Q) hw k
  obtain ⟨t3, ht3, p3⟩ := LevelNavCol.col_run q₁ q₂ s w c.2
  obtain ⟨t4, ht4, p4⟩ := LevelNavRow.row_run n q₁ q₂ s c.1
  obtain ⟨t5, ht5, p5⟩ := LevelNavCodes.cps_run q₁ q₂ s w c.2
  obtain ⟨t6, ht6, p6⟩ := LevelNavCodes.outer_run q₁ q₂ s w hs c.2
  obtain ⟨t7, ht7, p7⟩ := LevelNavCodes.tentry_run n q₁ q₂ s hq₂ c.1
  have l1 := lift_run LevelNav.leftProgram 0 2 h02 _ _ _ t1 R eE v0 v1 rfl rfl
    (by funext i; fin_cases i <;> rfl) p1
  have l2 := lift_run LevelNav.midProgram 1 3 h13 _ _ _ t2 C eG v1 v2 rfl rfl
    (by funext i; fin_cases i <;> rfl) p2
  have l3 := lift_run LevelNavCol.program 2 4 h24 _ _ _ t3 eE eCol v2 v3 rfl rfl
    (by funext i; fin_cases i <;> rfl) p3
  have l4 := lift_run LevelNavRow.program 3 5 h35 _ _ _ t4 eG eRow v3 v4 rfl rfl
    (by funext i; fin_cases i <;> rfl) p4
  have l5 := lift_run LevelNavCodes.cpsProgram 2 6 h26 _ _ _ t5 eE eCps v4 v5 rfl rfl
    (by funext i; fin_cases i <;> rfl) p5
  have l6 := lift_run LevelNavCodes.outerProgram 2 7 h27 _ _ _ t6 eE eOut v5 v6 rfl rfl
    (by funext i; fin_cases i <;> rfl) p6
  have l7 := lift_run LevelNavCodes.tentryProgram 3 8 h38 _ _ _ t7 eG eTe v6 v7 rfl rfl
    (by funext i; fin_cases i <;> rfl) p7
  obtain ⟨s2, hs2, q2⟩ := BitMachineRawSequence.runs navE navG LevelNav.leftStart
    LevelNav.midStart LevelNav.leftCtl LevelNav.leftCtl LevelNav.midCtl LevelNav.midCtl
    _ _ _ _ _ l1 l2
  obtain ⟨s3, hs3, q3⟩ := BitMachineRawSequence.runs j2 navCol (leftLabel LevelNav.leftStart)
    LevelNavCol.startLabel ctl2 ctl2 LevelNavCol.ctl LevelNavCol.ctl _ _ _ _ _ q2 l3
  obtain ⟨s4, hs4, q4⟩ := BitMachineRawSequence.runs j3 navRow
    (leftLabel (leftLabel LevelNav.leftStart))
    LevelNavRow.startLabel ctl3 ctl3 LevelNavRow.ctl LevelNavRow.ctl _ _ _ _ _ q3 l4
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
  have ht3' : t3 ≤ LevelNavCol.bound q₁ q₂ s w (seedRecursiveCodes n p s q₁ q₂ w Q k).2 := ht3
  have ht4' : t4 ≤ LevelNavRow.bound n q₁ q₂ s (seedRecursiveCodes n p s q₁ q₂ w Q k).1 := ht4
  have ht5' : t5 ≤ LevelNavCodes.cpsBound q₁ q₂ s w (seedRecursiveCodes n p s q₁ q₂ w Q k).2 :=
    ht5
  have ht6' : t6 ≤ LevelNavCodes.outerBound q₁ q₂ s w (seedRecursiveCodes n p s q₁ q₂ w Q k).2 :=
    ht6
  have ht7' : t7 ≤ LevelNavCodes.tentryBound n q₁ q₂ s (seedRecursiveCodes n p s q₁ q₂ w Q k).1 :=
    ht7
  simp only [joinBound]
  omega

/-- The same run in ANY ambient bank, through ANY injective relabelling `ι` of
the join bank (the later one-bank join chooses `ι` so that cells 2–8 are the
consumer cells). Exit bank exact: `bank ι W (jb (outVec …))` agrees with `W`
off the image of `ι` and with the exit vector on it. -/
theorem join_run_embedded {J : Type*} [DecidableEq J] {n p s q₁ q₂ w Q : ℕ}
    (hQ : 0 < Q) (hw : 0 < w) (hs : 0 < s) (hq₂ : 0 < q₂) (k : ℕ)
    (ι : Stack ↪ J) (W : J → List Bool)
    (hW : ∀ x, W (ι x) = jb (inVec (encodeCode (seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)).1)
      (encodeCode (seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)).2)) x) :
    ∃ t ≤ joinBound n p s q₁ q₂ w Q k,
      ((advance (fun l => stackStmt ι (program l)))^[t])
        (⟨some startLabel, ctl, W⟩ : TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, ctl, bank ι W (jb (outVec n p s q₁ q₂ w Q k))⟩ := by
  obtain ⟨t, ht, hr⟩ := join_run (n := n) (p := p) hQ hw hs hq₂ k
  refine ⟨t, ht, ?_⟩
  have hs' := BitMachineStackRun.run ι W program
    (⟨some startLabel, ctl,
      jb (inVec (encodeCode (seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)).1)
        (encodeCode (seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)).2))⟩ :
      TM2.Cfg (fun _ : Stack => Bool) _ _) t
  rw [hr] at hs'
  have hb : bank ι W (jb (inVec (encodeCode (seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)).1)
      (encodeCode (seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)).2))) = W :=
    bank_eq_self ι W _ (fun x => (hW x).symm)
  simp only [stackCfg] at hs'
  rw [hb] at hs'
  exact hs'

end

#print axioms lift_run
#print axioms join_run
#print axioms join_run_embedded

end Paper2.NavJoin
