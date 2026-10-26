import Paper2.LevelNavRow

/-! Unit 3, segment (1): physical production, on the checked `ChildNav` bank,
of the three sub-codes that the read-back of `a-success-table-owner-2`
(AUDIT §4) found supplied and produced by no checked theorem:

* `copies (s+1) col_k` (consumed by `LocateUniform`, cell `cc`): the first
  child of `rawCode col_k = append (copies (s+1) col_k) (copies s (outerCode col_k))`,
  reached from the serialized row entry `E_k = append (ticket w) (taggedCode col_k)`
  along the frozen prefix `LevelNavCol.c9` (drop the `append` header, the
  `ticket w` child, the `branch3` header with its unary fields `256, 254, 255`,
  the first alternative's header and `emit [false]` child, the `rawCode`
  header), then `takeChild`;
* `outerCode col_k` (consumed by `LocateUniform`, cell `rc`): same prefix,
  then drop the child `copies (s+1) col_k`, drop the header of
  `copies s (outerCode col_k)` (`0 < s`), take the first child;
* `append (ticket q₁) row_k` (consumed by `TemplateLookup`, cell `E`): from
  `G_k = graphRowsCode row_k = branch3 512 510 511 A B C` along the frozen
  prefix `LevelNavRow.r4` (header and the three unary fields), then drop the
  header of `A = append (emit [false]) (templateRowCode row_k)`, drop the
  `emit` child, drop the header of `templateRowCode = append (ticket s)
  (templateCode row_k)`, drop the `ticket s` child, drop the header of
  `templateCode = copies q₂ (append (ticket q₁) row_k)` (`0 < q₂`), take the
  first child.

Each is ONE fixed program; input retained in `inp`, result in `outp`, every
other cell blank at entry and exit (exact exit bank). The frozen predecessor
programs `LevelNavCol.c9` and `LevelNavRow.r4` are reused by name. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Paper2.LevelNavCodes

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open GeneratorCode GeneratorSerialization GeneratorSource
open ChildNav (nb)
open LevelNav (oc drop3 d3start)
open LevelNavCol (dk3)
open BitMachineRawSequence (leftLabel)

/-! ### Shared prefix on `E_k`: the frozen `LevelNavCol.c9` -/

def colPrefixBound (q₁ q₂ s w : ℕ) (col : Code) : ℕ :=
  (2 * (encodeCode (.append (.ticket w) (taggedCode q₁ q₂ s col))).length + 2) + 4 +
    ChildNav.dropBound (.ticket w) (encodeCode (taggedCode q₁ q₂ s col)) + 4 +
    (256 + 1) + (254 + 1) + (255 + 1) + 4 +
    ChildNav.dropBound (.emit [false]) (encodeCode (rawCode q₁ q₂ s col) ++ LevelNavCol.R1 q₁ q₂ s col) +
    4 + 9

theorem col_prefix_run (q₁ q₂ s w : ℕ) (col : Code) :
    let E : Code := .append (.ticket w) (taggedCode q₁ q₂ s col)
    ∃ t ≤ colPrefixBound q₁ q₂ s w col, ∃ v,
      ((advance LevelNavCol.c9)^[t])
        (⟨some (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel
          (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan))))))))),
          LevelNavCol.k9, nb [] [] [] (encodeCode E) []⟩ :
          TM2.Cfg (fun _ : ChildNav.Stack => Bool) _ _) =
        ⟨none, v, nb (encodeCode (copies (s + 1) col) ++ LevelNavCol.R2 q₁ q₂ s col) [] []
          (encodeCode E) []⟩ := by
  intro E
  let inp := encodeCode E
  let T := encodeCode (taggedCode q₁ q₂ s col)
  let encA := encodeCode (.append (.emit [false]) (rawCode q₁ q₂ s col))
  let r1 := LevelNavCol.R1 q₁ q₂ s col
  let R0 := encA ++ r1
  let encRaw := encodeCode (rawCode q₁ q₂ s col)
  have h01 : inp = [false, true, true] ++ (encodeCode (.ticket w) ++ T) := by
    simp [inp, E, T, encodeCode]
  have h23 : T = [true, false, false] ++
      (unary 256 ++ (unary 254 ++ (unary 255 ++ R0))) := by
    simp [T, R0, encA, r1, LevelNavCol.R1, taggedCode, encodeCode]
  have h67 : R0 = [false, true, true] ++ (encodeCode (.emit [false]) ++ (encRaw ++ r1)) := by
    simp [R0, encA, encRaw, encodeCode]
  have h89 : encRaw ++ r1 = [false, true, true] ++
      (encodeCode (copies (s + 1) col) ++ LevelNavCol.R2 q₁ q₂ s col) := by
    simp [encRaw, r1, LevelNavCol.R2, rawCode, encodeCode]
  have p0 := ChildNav.copyIn_run inp []
  have p1 := dk3 [false, true, true] (encodeCode (.ticket w) ++ T) [] [] inp [] rfl
  rw [← h01] at p1
  obtain ⟨t2, ht2, p2⟩ := ChildNav.dropChild_run (.ticket w) T inp []
  have p3 := dk3 [true, false, false] (unary 256 ++ (unary 254 ++ (unary 255 ++ R0)))
    [] [] inp [] rfl
  rw [← h23] at p3
  have p4 := ChildNav.dropUnary_run 256 (unary 254 ++ (unary 255 ++ R0)) [] [] inp [] oc
  have p5 := ChildNav.dropUnary_run 254 (unary 255 ++ R0) [] [] inp [] oc
  have p6 := ChildNav.dropUnary_run 255 R0 [] [] inp [] oc
  have p7 := dk3 [false, true, true] (encodeCode (.emit [false]) ++ (encRaw ++ r1))
    [] [] inp [] rfl
  rw [← h67] at p7
  obtain ⟨t8, ht8, p8⟩ := ChildNav.dropChild_run (.emit [false]) (encRaw ++ r1) inp []
  have p9 := dk3 [false, true, true]
    (encodeCode (copies (s + 1) col) ++ LevelNavCol.R2 q₁ q₂ s col) [] [] inp [] rfl
  rw [← h89] at p9
  obtain ⟨r1', hr1, q1⟩ := BitMachineRawSequence.runs ChildNav.copyIn drop3 .scan d3start
    oc oc () () _ _ _ _ _ p0 p1
  obtain ⟨r2, hr2, q2⟩ := BitMachineRawSequence.runs LevelNavCol.c1 ChildNav.dropChild
    (leftLabel .scan) ChildNav.dropStart
    LevelNavCol.k1 LevelNavCol.k1 ChildNav.dropCtl ChildNav.dropCtl _ _ _ _ _ q1 p2
  obtain ⟨r3, hr3, q3⟩ := BitMachineRawSequence.runs LevelNavCol.c2 drop3
    (leftLabel (leftLabel .scan)) d3start
    LevelNavCol.k2 LevelNavCol.k2 () () _ _ _ _ _ q2 p3
  obtain ⟨r4, hr4, q4⟩ := BitMachineRawSequence.runs LevelNavCol.c3 ChildNav.dropUnary
    (leftLabel (leftLabel (leftLabel .scan))) ()
    LevelNavCol.k3 LevelNavCol.k3 oc (some false) _ _ _ _ _ q3 p4
  obtain ⟨r5, hr5, q5⟩ := BitMachineRawSequence.runs LevelNavCol.c4 ChildNav.dropUnary
    (leftLabel (leftLabel (leftLabel (leftLabel .scan)))) ()
    LevelNavCol.k4 (LevelNavCol.k3, some false) oc (some false) _ _ _ _ _ q4 p5
  obtain ⟨r6, hr6, q6⟩ := BitMachineRawSequence.runs LevelNavCol.c5 ChildNav.dropUnary
    (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel .scan))))) ()
    LevelNavCol.k5 (LevelNavCol.k4, some false) oc (some false) _ _ _ _ _ q5 p6
  obtain ⟨r7, hr7, q7⟩ := BitMachineRawSequence.runs LevelNavCol.c6 drop3
    (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel .scan)))))) d3start
    LevelNavCol.k6 (LevelNavCol.k5, some false) () () _ _ _ _ _ q6 p7
  obtain ⟨r8, hr8, q8⟩ := BitMachineRawSequence.runs LevelNavCol.c7 ChildNav.dropChild
    (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel .scan)))))))
    ChildNav.dropStart
    LevelNavCol.k7 LevelNavCol.k7 ChildNav.dropCtl ChildNav.dropCtl _ _ _ _ _ q7 p8
  obtain ⟨r9, hr9, q9⟩ := BitMachineRawSequence.runs LevelNavCol.c8 drop3
    (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel
      (leftLabel .scan))))))))
    d3start LevelNavCol.k8 LevelNavCol.k8 () () _ _ _ _ _ q8 p9
  refine ⟨r9, ?_, _, q9⟩
  have hinp : inp.length =
      (encodeCode (.append (.ticket w) (taggedCode q₁ q₂ s col))).length := rfl
  have ht2' : t2 ≤ ChildNav.dropBound (.ticket w) (encodeCode (taggedCode q₁ q₂ s col)) := ht2
  have ht8' : t8 ≤ ChildNav.dropBound (.emit [false])
      (encodeCode (rawCode q₁ q₂ s col) ++ LevelNavCol.R1 q₁ q₂ s col) := ht8
  simp only [colPrefixBound]
  omega

/-! ### (a) `copies (s+1) col` -/

def cpsProgram := BitMachineRawSequence.program LevelNavCol.c9 ChildNav.takeChild
  ChildNav.takeStart LevelNavCol.k9 ChildNav.takeCtl

def cpsStart := ChildNav.labelOf cpsProgram
  (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel
    (leftLabel (leftLabel BitMachineCopy.Label.scan))))))))))
def cpsCtl := (LevelNavCol.k9, ChildNav.takeCtl)

def cpsBound (q₁ q₂ s w : ℕ) (col : Code) : ℕ :=
  colPrefixBound q₁ q₂ s w col + ChildNav.takeBound (copies (s + 1) col)
    (LevelNavCol.R2 q₁ q₂ s col) + 1

theorem cps_run (q₁ q₂ s w : ℕ) (col : Code) :
    let E : Code := .append (.ticket w) (taggedCode q₁ q₂ s col)
    ∃ t ≤ cpsBound q₁ q₂ s w col,
      ((advance cpsProgram)^[t])
        (⟨some cpsStart, cpsCtl, nb [] [] [] (encodeCode E) []⟩ :
          TM2.Cfg (fun _ : ChildNav.Stack => Bool) _ _) =
        ⟨none, cpsCtl, nb [] [] [] (encodeCode E) (encodeCode (copies (s + 1) col))⟩ := by
  intro E
  obtain ⟨t1, ht1, v, p1⟩ := col_prefix_run q₁ q₂ s w col
  obtain ⟨t2, ht2, p2⟩ := ChildNav.takeChild_run (copies (s + 1) col)
    (LevelNavCol.R2 q₁ q₂ s col) (encodeCode E)
  obtain ⟨u, hu, q⟩ := BitMachineRawSequence.runs LevelNavCol.c9 ChildNav.takeChild
    _ ChildNav.takeStart LevelNavCol.k9 v ChildNav.takeCtl ChildNav.takeCtl _ _ _ _ _ p1 p2
  refine ⟨u, ?_, q⟩
  simp only [cpsBound]
  omega

/-! ### (b) `outerCode col` -/

def o1 := BitMachineRawSequence.program LevelNavCol.c9 ChildNav.dropChild ChildNav.dropStart
  LevelNavCol.k9 ChildNav.dropCtl
def o2 := BitMachineRawSequence.program o1 drop3 d3start (LevelNavCol.k9, ChildNav.dropCtl) ()
def outerProgram := BitMachineRawSequence.program o2 ChildNav.takeChild ChildNav.takeStart
  ((LevelNavCol.k9, ChildNav.dropCtl), ()) ChildNav.takeCtl

def outerStart := ChildNav.labelOf outerProgram
  (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel
    (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan))))))))))))
def outerCtl := (((LevelNavCol.k9, ChildNav.dropCtl), ()), ChildNav.takeCtl)

def outerBound (q₁ q₂ s w : ℕ) (col : Code) : ℕ :=
  colPrefixBound q₁ q₂ s w col +
    ChildNav.dropBound (copies (s + 1) col) (LevelNavCol.R2 q₁ q₂ s col) + 4 +
    ChildNav.takeBound (outerCode q₁ q₂ s col)
      (encodeCode (copies (s - 1) (outerCode q₁ q₂ s col)) ++ LevelNavCol.R1 q₁ q₂ s col) + 3

theorem outer_run (q₁ q₂ s w : ℕ) (hs : 0 < s) (col : Code) :
    let E : Code := .append (.ticket w) (taggedCode q₁ q₂ s col)
    ∃ t ≤ outerBound q₁ q₂ s w col,
      ((advance outerProgram)^[t])
        (⟨some outerStart, outerCtl, nb [] [] [] (encodeCode E) []⟩ :
          TM2.Cfg (fun _ : ChildNav.Stack => Bool) _ _) =
        ⟨none, outerCtl, nb [] [] [] (encodeCode E) (encodeCode (outerCode q₁ q₂ s col))⟩ := by
  intro E
  let O := outerCode q₁ q₂ s col
  let rest := encodeCode (copies (s - 1) O) ++ LevelNavCol.R1 q₁ q₂ s col
  have hR2 : LevelNavCol.R2 q₁ q₂ s col = [false, true, true] ++ (encodeCode O ++ rest) := by
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    simp [LevelNavCol.R2, rest, O, copies, encodeCode]
  obtain ⟨t1, ht1, v, p1⟩ := col_prefix_run q₁ q₂ s w col
  obtain ⟨t2, ht2, p2⟩ := ChildNav.dropChild_run (copies (s + 1) col)
    (LevelNavCol.R2 q₁ q₂ s col) (encodeCode E) []
  have p3 := dk3 [false, true, true] (encodeCode O ++ rest) [] [] (encodeCode E) [] rfl
  rw [← hR2] at p3
  obtain ⟨t4, ht4, p4⟩ := ChildNav.takeChild_run O rest (encodeCode E)
  obtain ⟨u1, hu1, q1⟩ := BitMachineRawSequence.runs LevelNavCol.c9 ChildNav.dropChild
    _ ChildNav.dropStart LevelNavCol.k9 v ChildNav.dropCtl ChildNav.dropCtl _ _ _ _ _ p1 p2
  obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs o1 drop3
    _ d3start (LevelNavCol.k9, ChildNav.dropCtl) _ () () _ _ _ _ _ q1 p3
  obtain ⟨u3, hu3, q3⟩ := BitMachineRawSequence.runs o2 ChildNav.takeChild
    _ ChildNav.takeStart ((LevelNavCol.k9, ChildNav.dropCtl), ()) _
    ChildNav.takeCtl ChildNav.takeCtl _ _ _ _ _ q2 p4
  refine ⟨u3, ?_, q3⟩
  have ht4' : t4 ≤ ChildNav.takeBound (outerCode q₁ q₂ s col)
      (encodeCode (copies (s - 1) (outerCode q₁ q₂ s col)) ++ LevelNavCol.R1 q₁ q₂ s col) := ht4
  simp only [outerBound]
  omega

/-! ### (c) `append (ticket q₁) row` from `graphRowsCode row` -/

def g1 := (LevelNavRow.j4, ())
def g2 := (g1, ChildNav.dropCtl)
def g3 := (g2, ())
def g4 := (g3, ChildNav.dropCtl)
def g5 := (g4, ())

def t5 := BitMachineRawSequence.program LevelNavRow.r4 drop3 d3start LevelNavRow.j4 ()
def t6 := BitMachineRawSequence.program t5 ChildNav.dropChild ChildNav.dropStart g1
  ChildNav.dropCtl
def t7 := BitMachineRawSequence.program t6 drop3 d3start g2 ()
def t8 := BitMachineRawSequence.program t7 ChildNav.dropChild ChildNav.dropStart g3
  ChildNav.dropCtl
def t9 := BitMachineRawSequence.program t8 drop3 d3start g4 ()
def tentryProgram := BitMachineRawSequence.program t9 ChildNav.takeChild ChildNav.takeStart g5
  ChildNav.takeCtl

def tentryStart := ChildNav.labelOf tentryProgram
  (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel
    (leftLabel (leftLabel BitMachineCopy.Label.scan))))))))))
def tentryCtl := (g5, ChildNav.takeCtl)

/-- The words after the template alternative (public, determined by the code). -/
def rB (n s : ℕ) (row : Code) : List Bool := LevelNavRow.encB n s row ++ LevelNavRow.encC s row

def tentryBound (n q₁ q₂ s : ℕ) (row : Code) : ℕ :=
  (2 * (encodeCode (graphRowsCode (V := Fin n) q₁ q₂ s row)).length + 2) + 4 +
    (512 + 1) + (510 + 1) + (511 + 1) + 4 +
    ChildNav.dropBound (.emit [false]) (encodeCode (templateRowCode q₁ q₂ s row) ++ rB n s row) +
    4 + ChildNav.dropBound (.ticket s) (encodeCode (templateCode q₁ q₂ row) ++ rB n s row) + 4 +
    ChildNav.takeBound (.append (.ticket q₁) row)
      (encodeCode (copies (q₂ - 1) (.append (.ticket q₁) row)) ++ rB n s row) + 10

theorem tentry_run (n q₁ q₂ s : ℕ) (hq₂ : 0 < q₂) (row : Code) :
    let G : Code := graphRowsCode (V := Fin n) q₁ q₂ s row
    ∃ t ≤ tentryBound n q₁ q₂ s row,
      ((advance tentryProgram)^[t])
        (⟨some tentryStart, tentryCtl, nb [] [] [] (encodeCode G) []⟩ :
          TM2.Cfg (fun _ : ChildNav.Stack => Bool) _ _) =
        ⟨none, tentryCtl, nb [] [] [] (encodeCode G) (encodeCode (.append (.ticket q₁) row))⟩ := by
  intro G
  let inp := encodeCode G
  let TR : Code := templateRowCode q₁ q₂ s row
  let TC : Code := templateCode q₁ q₂ row
  let TE : Code := .append (.ticket q₁) row
  let A : Code := .append (.emit [false]) TR
  let rb := rB n s row
  let rest := encodeCode (copies (q₂ - 1) TE) ++ rb
  have h01 : inp = [true, false, false] ++
      (unary 512 ++ (unary 510 ++ (unary 511 ++ (encodeCode A ++ rb)))) := by
    simp [inp, G, A, TR, rb, rB, LevelNavRow.encB, LevelNavRow.encC, graphRowsCode, rowsCode,
      encodeCode]
  have h5 : encodeCode A ++ rb =
      [false, true, true] ++ (encodeCode (.emit [false]) ++ (encodeCode TR ++ rb)) := by
    simp [A, encodeCode]
  have h7 : encodeCode TR ++ rb =
      [false, true, true] ++ (encodeCode (.ticket s) ++ (encodeCode TC ++ rb)) := by
    simp [TR, TC, templateRowCode, encodeCode]
  have h9 : encodeCode TC ++ rb = [false, true, true] ++ (encodeCode TE ++ rest) := by
    obtain ⟨q', rfl⟩ : ∃ q', q₂ = q' + 1 := ⟨q₂ - 1, by omega⟩
    simp [TC, TE, rest, templateCode, copies, encodeCode]
  have p0 := ChildNav.copyIn_run inp []
  have p1 := dk3 [true, false, false]
    (unary 512 ++ (unary 510 ++ (unary 511 ++ (encodeCode A ++ rb)))) [] [] inp [] rfl
  rw [← h01] at p1
  have p2 := ChildNav.dropUnary_run 512 (unary 510 ++ (unary 511 ++ (encodeCode A ++ rb)))
    [] [] inp [] oc
  have p3 := ChildNav.dropUnary_run 510 (unary 511 ++ (encodeCode A ++ rb)) [] [] inp [] oc
  have p4 := ChildNav.dropUnary_run 511 (encodeCode A ++ rb) [] [] inp [] oc
  have p5 := dk3 [false, true, true] (encodeCode (.emit [false]) ++ (encodeCode TR ++ rb))
    [] [] inp [] rfl
  rw [← h5] at p5
  obtain ⟨t6', ht6, p6⟩ := ChildNav.dropChild_run (.emit [false]) (encodeCode TR ++ rb) inp []
  have p7 := dk3 [false, true, true] (encodeCode (.ticket s) ++ (encodeCode TC ++ rb))
    [] [] inp [] rfl
  rw [← h7] at p7
  obtain ⟨t8', ht8, p8⟩ := ChildNav.dropChild_run (.ticket s) (encodeCode TC ++ rb) inp []
  have p9 := dk3 [false, true, true] (encodeCode TE ++ rest) [] [] inp [] rfl
  rw [← h9] at p9
  obtain ⟨t10, ht10, p10⟩ := ChildNav.takeChild_run TE rest inp
  obtain ⟨u1, hu1, q1⟩ := BitMachineRawSequence.runs ChildNav.copyIn drop3 .scan d3start
    oc oc () () _ _ _ _ _ p0 p1
  obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs LevelNavRow.r1 ChildNav.dropUnary
    (leftLabel .scan) ()
    LevelNavRow.j1 LevelNavRow.j1 oc (some false) _ _ _ _ _ q1 p2
  obtain ⟨u3, hu3, q3⟩ := BitMachineRawSequence.runs LevelNavRow.r2 ChildNav.dropUnary
    (leftLabel (leftLabel .scan)) ()
    LevelNavRow.j2 (LevelNavRow.j1, some false) oc (some false) _ _ _ _ _ q2 p3
  obtain ⟨u4, hu4, q4⟩ := BitMachineRawSequence.runs LevelNavRow.r3 ChildNav.dropUnary
    (leftLabel (leftLabel (leftLabel .scan))) ()
    LevelNavRow.j3 (LevelNavRow.j2, some false) oc (some false) _ _ _ _ _ q3 p4
  obtain ⟨u5, hu5, q5⟩ := BitMachineRawSequence.runs LevelNavRow.r4 drop3
    (leftLabel (leftLabel (leftLabel (leftLabel .scan)))) d3start
    LevelNavRow.j4 (LevelNavRow.j3, some false) () () _ _ _ _ _ q4 p5
  obtain ⟨u6, hu6, q6⟩ := BitMachineRawSequence.runs t5 ChildNav.dropChild
    (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel .scan))))) ChildNav.dropStart
    g1 g1 ChildNav.dropCtl ChildNav.dropCtl _ _ _ _ _ q5 p6
  obtain ⟨u7, hu7, q7⟩ := BitMachineRawSequence.runs t6 drop3
    (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel .scan)))))) d3start
    g2 g2 () () _ _ _ _ _ q6 p7
  obtain ⟨u8, hu8, q8⟩ := BitMachineRawSequence.runs t7 ChildNav.dropChild
    (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel .scan)))))))
    ChildNav.dropStart g3 g3 ChildNav.dropCtl ChildNav.dropCtl _ _ _ _ _ q7 p8
  obtain ⟨u9, hu9, q9⟩ := BitMachineRawSequence.runs t8 drop3
    (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel
      (leftLabel .scan)))))))) d3start g4 g4 () () _ _ _ _ _ q8 p9
  obtain ⟨u10, hu10, q10⟩ := BitMachineRawSequence.runs t9 ChildNav.takeChild
    (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel
      (leftLabel (leftLabel .scan)))))))))
    ChildNav.takeStart g5 g5 ChildNav.takeCtl ChildNav.takeCtl _ _ _ _ _ q9 p10
  refine ⟨u10, ?_, q10⟩
  have hinp : inp.length = (encodeCode (graphRowsCode (V := Fin n) q₁ q₂ s row)).length := rfl
  have ht6' : t6' ≤ ChildNav.dropBound (.emit [false])
      (encodeCode (templateRowCode q₁ q₂ s row) ++ rB n s row) := ht6
  have ht8' : t8' ≤ ChildNav.dropBound (.ticket s)
      (encodeCode (templateCode q₁ q₂ row) ++ rB n s row) := ht8
  have ht10' : t10 ≤ ChildNav.takeBound (.append (.ticket q₁) row)
      (encodeCode (copies (q₂ - 1) (.append (.ticket q₁) row)) ++ rB n s row) := ht10
  simp only [tentryBound]
  omega

end

#print axioms col_prefix_run
#print axioms cps_run
#print axioms outer_run
#print axioms tentry_run

end Paper2.LevelNavCodes
