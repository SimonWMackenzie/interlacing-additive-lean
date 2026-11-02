import EthInapproximability.CurrentPaper.EntryDispatch
import EthInapproximability.CurrentPaper.EntryUnaryCompare
import EthInapproximability.CurrentPaper.FamilyRowGeneric

/-!
# Segment 2 building block: the physical template/item row dispatch

Lane owner:b-stage4-entry-program-3 (Paper B, unit 2, map item 3).

ONE fixed controller on an arbitrary bank `K` with six distinct named cells
(`xc` the unary row ordinal, `tc` the unary threshold `s*L`, scratch `a1`,
`a2`, `tmp`, and the verdict cell `flag`): two charged source-preserving
copies, the checked unary comparator (`EntryUnaryCompare`, verdict `x < thr`
pushed on `flag`), and then `EntryDispatch.program`, which pops that verdict
and runs the literally inlined template program `A` (verdict `true`) or item
program `B` (verdict `false`). The branch starts on EXACTLY the bank the
dispatch started on (both operands retained, all scratch blank again). No
branch choice is supplied.
-/

namespace EthInapproximability.CurrentPaper.EntryRowVerdict

open Turing BitMachineEncoding
open MatrixStage4ScalarPreparationOps

variable {K LA LB VA VB : Type*} [DecidableEq K]

section
variable (xc tc a1 a2 tmp flag : K)

def sx (h1 : xc ≠ a1) (h2 : xc ≠ tmp) (h3 : a1 ≠ tmp) : Fin 3 ↪ K :=
  ⟨![xc, a1, tmp], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩

def st (h1 : tc ≠ a2) (h2 : tc ≠ tmp) (h3 : a2 ≠ tmp) : Fin 3 ↪ K :=
  ⟨![tc, a2, tmp], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩
end

/-- The verdict controller: two copies and the comparator. -/
def verdictProgram (xc tc a1 a2 tmp flag : K)
    (hxa : xc ≠ a1) (hxt : xc ≠ tmp) (hat : a1 ≠ tmp)
    (hta : tc ≠ a2) (htt : tc ≠ tmp) (h2t : a2 ≠ tmp) :=
  BitMachineRawSequence.program (copyProgram (sx xc a1 tmp hxa hxt hat))
    (BitMachineRawSequence.program (copyProgram (st tc a2 tmp hta htt h2t))
      (EntryUnaryCompare.program a1 a2 flag true false false)
      EntryUnaryCompare.CL.loop (none : Option Bool) ((none, none) : EntryUnaryCompare.CV))
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) (none : Option Bool)
    ((none : Option Bool), ((none, none) : EntryUnaryCompare.CV))

def verdictInit : Option Bool × (Option Bool × EntryUnaryCompare.CV) :=
  (none, (none, (none, none)))

theorem verdict_run (xc tc a1 a2 tmp flag : K)
    (hxa : xc ≠ a1) (hxt : xc ≠ tmp) (hat : a1 ≠ tmp)
    (hta : tc ≠ a2) (htt : tc ≠ tmp) (h2t : a2 ≠ tmp)
    (hxf : xc ≠ flag) (htf : tc ≠ flag) (h1f : a1 ≠ flag) (h2f : a2 ≠ flag)
    (hff : tmp ≠ flag) (h12 : a1 ≠ a2) (hxt2 : xc ≠ a2) (htx1 : tc ≠ a1)
    (S : K → List Bool) (n m : ℕ)
    (hx : S xc = List.replicate n true) (ht : S tc = List.replicate m true)
    (ha1 : S a1 = []) (ha2 : S a2 = []) (htm : S tmp = []) (hfl : S flag = []) :
    ∃ T ≤ (2 * n + 2) + (2 * m + 2) + (max n m + 2) + 2, ∃ v,
      ((advance (verdictProgram xc tc a1 a2 tmp flag hxa hxt hat hta htt h2t))^[T])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan), verdictInit, S⟩ :
          TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, v, Function.update S flag [decide (n < m)]⟩ := by
  -- copy x into a1
  have c1 := FamilyRowGeneric.copy_blank (sx xc a1 tmp hxa hxt hat) S htm ha1
  have e1 : S ((sx xc a1 tmp hxa hxt hat) 0) = List.replicate n true := hx
  rw [e1, List.length_replicate] at c1
  let S1 := Function.update S a1 (List.replicate n true)
  have c1' : ((advance (copyProgram (sx xc a1 tmp hxa hxt hat)))^[2 * n + 2])
      (⟨some BitMachineCopy.Label.scan, none, S⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
      ⟨none, none, S1⟩ := c1
  -- copy thr into a2
  have c2 := FamilyRowGeneric.copy_blank (st tc a2 tmp hta htt h2t) S1
    (by show Function.update S a1 _ tmp = []; rw [Function.update_of_ne hat.symm]; exact htm)
    (by show Function.update S a1 _ a2 = []; rw [Function.update_of_ne h12.symm]; exact ha2)
  have e2 : S1 ((st tc a2 tmp hta htt h2t) 0) = List.replicate m true := by
    show Function.update S a1 _ tc = _
    rw [Function.update_of_ne htx1]; exact ht
  rw [e2, List.length_replicate] at c2
  let S2 := Function.update S1 a2 (List.replicate m true)
  have c2' : ((advance (copyProgram (st tc a2 tmp hta htt h2t)))^[2 * m + 2])
      (⟨some BitMachineCopy.Label.scan, none, S1⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
      ⟨none, none, S2⟩ := c2
  -- compare
  obtain ⟨tc3, htc3, w3, c3⟩ := EntryUnaryCompare.compare_run a1 a2 flag h12 h1f h2f
    true false false S2 (none, none) n m
    (by show Function.update S1 a2 _ a1 = _
        rw [Function.update_of_ne h12]
        show Function.update S a1 _ a1 = _
        rw [Function.update_self])
    (by show Function.update S1 a2 _ a2 = _; rw [Function.update_self])
  have hfinal : Function.update (Function.update (Function.update S2 a1 []) a2 [])
      flag (EntryUnaryCompare.verdict true false false n m :: S2 flag) =
      Function.update S flag [decide (n < m)] := by
    have hS2f : S2 flag = [] := by
      show Function.update (Function.update S a1 _) a2 _ flag = []
      rw [Function.update_of_ne h2f.symm, Function.update_of_ne h1f.symm]; exact hfl
    have hv : EntryUnaryCompare.verdict true false false n m = decide (n < m) := by
      unfold EntryUnaryCompare.verdict
      by_cases h : n < m
      · simp [h]
      · by_cases h' : n = m <;> simp [h, h']
    rw [hS2f, hv]
    funext k
    by_cases kf : k = flag
    · subst kf; simp
    · rw [Function.update_of_ne kf, Function.update_of_ne kf]
      by_cases k2 : k = a2
      · subst k2; rw [Function.update_self]; exact ha2.symm
      · rw [Function.update_of_ne k2]
        by_cases k1 : k = a1
        · subst k1; rw [Function.update_self]; exact ha1.symm
        · rw [Function.update_of_ne k1]
          show Function.update (Function.update S a1 _) a2 _ k = S k
          rw [Function.update_of_ne k2, Function.update_of_ne k1]
  rw [hfinal] at c3
  obtain ⟨u2, hu2, r2⟩ := BitMachineRawSequence.runs (copyProgram (st tc a2 tmp hta htt h2t))
    (EntryUnaryCompare.program a1 a2 flag true false false) BitMachineCopy.Label.scan
    EntryUnaryCompare.CL.loop none none (none, none) w3 S1 S2
    (Function.update S flag [decide (n < m)]) (2 * m + 2) tc3 c2' c3
  obtain ⟨u1, hu1, r1⟩ := BitMachineRawSequence.runs (copyProgram (sx xc a1 tmp hxa hxt hat))
    (BitMachineRawSequence.program (copyProgram (st tc a2 tmp hta htt h2t))
      (EntryUnaryCompare.program a1 a2 flag true false false)
      EntryUnaryCompare.CL.loop (none : Option Bool) ((none, none) : EntryUnaryCompare.CV))
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none none (none, (none, none)) (none, w3) S S1
    (Function.update S flag [decide (n < m)]) (2 * n + 2) u2 c1' r2
  refine ⟨u1, by omega, _, r1⟩

/-- Verdict, then dispatch: ONE fixed controller. -/
def rowDispatch (xc tc a1 a2 tmp flag : K)
    (hxa : xc ≠ a1) (hxt : xc ≠ tmp) (hat : a1 ≠ tmp)
    (hta : tc ≠ a2) (htt : tc ≠ tmp) (h2t : a2 ≠ tmp)
    (A : LA → TM2.Stmt (fun _ : K => Bool) LA VA)
    (B : LB → TM2.Stmt (fun _ : K => Bool) LB VB) (a₀ : LA) (b₀ : LB) (v₀ : VA) (w₀ : VB) :=
  BitMachineRawSequence.program (verdictProgram xc tc a1 a2 tmp flag hxa hxt hat hta htt h2t)
    (EntryDispatch.program flag A B a₀ b₀ v₀ w₀) (Sum.inl ()) verdictInit
    (((v₀, w₀), none) : EntryDispatch.Control VA VB)

theorem row_template (xc tc a1 a2 tmp flag : K)
    (hxa : xc ≠ a1) (hxt : xc ≠ tmp) (hat : a1 ≠ tmp)
    (hta : tc ≠ a2) (htt : tc ≠ tmp) (h2t : a2 ≠ tmp)
    (hxf : xc ≠ flag) (htf : tc ≠ flag) (h1f : a1 ≠ flag) (h2f : a2 ≠ flag)
    (hff : tmp ≠ flag) (h12 : a1 ≠ a2) (hxt2 : xc ≠ a2) (htx1 : tc ≠ a1)
    (A : LA → TM2.Stmt (fun _ : K => Bool) LA VA)
    (B : LB → TM2.Stmt (fun _ : K => Bool) LB VB) (a₀ : LA) (b₀ : LB) (v₀ : VA) (w₀ : VB)
    (S : K → List Bool) (n m : ℕ)
    (hx : S xc = List.replicate n true) (ht : S tc = List.replicate m true)
    (ha1 : S a1 = []) (ha2 : S a2 = []) (htm : S tmp = []) (hfl : S flag = [])
    (hlt : n < m) (v₁ : VA) (T : K → List Bool) (ta : ℕ)
    (ha : ((advance A)^[ta]) (⟨some a₀, v₀, S⟩ : TM2.Cfg (fun _ : K => Bool) LA VA) =
      ⟨none, v₁, T⟩) :
    ∃ t ≤ (2 * n + 2) + (2 * m + 2) + (max n m + 2) + 2 + (ta + 1) + 1, ∃ v,
      ((advance (rowDispatch xc tc a1 a2 tmp flag hxa hxt hat hta htt h2t A B a₀ b₀ v₀ w₀))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
          (verdictInit, ((v₀, w₀), none)), S⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, v, T⟩ := by
  obtain ⟨T1, hT1, v1, h1⟩ := verdict_run xc tc a1 a2 tmp flag hxa hxt hat hta htt h2t
    hxf htf h1f h2f hff h12 hxt2 htx1 S n m hx ht ha1 ha2 htm hfl
  have hflag : Function.update S flag [decide (n < m)] flag = true :: [] := by
    rw [Function.update_self]; simp [hlt]
  have hback : Function.update (Function.update S flag [decide (n < m)]) flag [] = S := by
    rw [Function.update_idem]; exact Function.update_eq_self_iff.mpr hfl.symm
  have ha' : ((advance A)^[ta])
      (⟨some a₀, v₀, Function.update (Function.update S flag [decide (n < m)]) flag []⟩ :
        TM2.Cfg (fun _ : K => Bool) LA VA) = ⟨none, v₁, T⟩ := by
    rw [hback]; exact ha
  obtain ⟨t2, ht2, h2⟩ := EntryDispatch.run_left flag A B a₀ b₀ v₀ w₀ ((v₀, w₀), none)
    (Function.update S flag [decide (n < m)]) [] hflag v₁ T ta ha'
  obtain ⟨u, hu, r⟩ := BitMachineRawSequence.runs
    (verdictProgram xc tc a1 a2 tmp flag hxa hxt hat hta htt h2t)
    (EntryDispatch.program flag A B a₀ b₀ v₀ w₀)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) (Sum.inl ())
    verdictInit v1 ((v₀, w₀), none) ((v₁, w₀), none) S
    (Function.update S flag [decide (n < m)]) T T1 t2 h1 h2
  exact ⟨u, by omega, _, r⟩

theorem row_item (xc tc a1 a2 tmp flag : K)
    (hxa : xc ≠ a1) (hxt : xc ≠ tmp) (hat : a1 ≠ tmp)
    (hta : tc ≠ a2) (htt : tc ≠ tmp) (h2t : a2 ≠ tmp)
    (hxf : xc ≠ flag) (htf : tc ≠ flag) (h1f : a1 ≠ flag) (h2f : a2 ≠ flag)
    (hff : tmp ≠ flag) (h12 : a1 ≠ a2) (hxt2 : xc ≠ a2) (htx1 : tc ≠ a1)
    (A : LA → TM2.Stmt (fun _ : K => Bool) LA VA)
    (B : LB → TM2.Stmt (fun _ : K => Bool) LB VB) (a₀ : LA) (b₀ : LB) (v₀ : VA) (w₀ : VB)
    (S : K → List Bool) (n m : ℕ)
    (hx : S xc = List.replicate n true) (ht : S tc = List.replicate m true)
    (ha1 : S a1 = []) (ha2 : S a2 = []) (htm : S tmp = []) (hfl : S flag = [])
    (hle : m ≤ n) (w₁ : VB) (T : K → List Bool) (tb : ℕ)
    (hb : ((advance B)^[tb]) (⟨some b₀, w₀, S⟩ : TM2.Cfg (fun _ : K => Bool) LB VB) =
      ⟨none, w₁, T⟩) :
    ∃ t ≤ (2 * n + 2) + (2 * m + 2) + (max n m + 2) + 2 + (tb + 1) + 1, ∃ v,
      ((advance (rowDispatch xc tc a1 a2 tmp flag hxa hxt hat hta htt h2t A B a₀ b₀ v₀ w₀))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
          (verdictInit, ((v₀, w₀), none)), S⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, v, T⟩ := by
  obtain ⟨T1, hT1, v1, h1⟩ := verdict_run xc tc a1 a2 tmp flag hxa hxt hat hta htt h2t
    hxf htf h1f h2f hff h12 hxt2 htx1 S n m hx ht ha1 ha2 htm hfl
  have hflag : Function.update S flag [decide (n < m)] flag = false :: [] := by
    rw [Function.update_self]; simp; omega
  have hback : Function.update (Function.update S flag [decide (n < m)]) flag [] = S := by
    rw [Function.update_idem]; exact Function.update_eq_self_iff.mpr hfl.symm
  have hb' : ((advance B)^[tb])
      (⟨some b₀, w₀, Function.update (Function.update S flag [decide (n < m)]) flag []⟩ :
        TM2.Cfg (fun _ : K => Bool) LB VB) = ⟨none, w₁, T⟩ := by
    rw [hback]; exact hb
  obtain ⟨t2, ht2, h2⟩ := EntryDispatch.run_right flag A B a₀ b₀ v₀ w₀ ((v₀, w₀), none)
    (Function.update S flag [decide (n < m)]) [] hflag w₁ T tb hb'
  obtain ⟨u, hu, r⟩ := BitMachineRawSequence.runs
    (verdictProgram xc tc a1 a2 tmp flag hxa hxt hat hta htt h2t)
    (EntryDispatch.program flag A B a₀ b₀ v₀ w₀)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) (Sum.inl ())
    verdictInit v1 ((v₀, w₀), none) ((v₀, w₁), none) S
    (Function.update S flag [decide (n < m)]) T T1 t2 h1 h2
  exact ⟨u, by omega, _, r⟩

#print axioms verdict_run
#print axioms row_template
#print axioms row_item

end EthInapproximability.CurrentPaper.EntryRowVerdict
