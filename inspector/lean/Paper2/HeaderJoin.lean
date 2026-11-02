import Paper2.HeaderOut
import Paper2.CopyAll
import EthInapproximability.CurrentPaper.MatrixTableWriter

/-! Unit 3, segment (5): binding of `HeaderA`'s four entry cells to the cells of the
admitted row-major writer's bank (`MatrixTableWriter.Stack K`): unary `rows` = the
writer's `rows` cell, unary `cols` = its `cols` cell, the table word = its `output`
cell (the header stage is placed with its output cell ON the writer's output cell),
unary threshold = one retained cell. ONE fixed program `hjProg` = `CopyAll` of the
three unary cells into the header's fuel cells ; `HeaderA.prog` placed by `ιH`.
Every writer cell other than `output` is returned unchanged; the header's own
counter/binary/source/temp cells are named scratch (existential). -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.HeaderJoin

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.EncodedCommunication

variable {K : ℕ}

abbrev WS (K : ℕ) := MatrixTableWriter.Stack K
abbrev JH (K : ℕ) := WS K ⊕ (HeaderA.HB ⊕ Fin 2)

def wOut : JH K := .inl (.inr .output)
def wRows : JH K := .inl (.inr .rows)
def wCols : JH K := .inl (.inr .cols)
def thrM : JH K := .inr (.inr 0)
def scrH : JH K := .inr (.inr 1)
def hb (x : HeaderA.HB) : JH K := .inr (.inl x)

def ιHf (x : HeaderA.HB) : JH K := if x = HeaderA.outH then wOut else hb x

theorem ιHf_injective : Function.Injective (ιHf (K := K)) := by
  intro a b h
  unfold ιHf at h
  split_ifs at h with h1 h2 h2 <;> simp_all [wOut, hb]

def ιH : HeaderA.HB ↪ JH K := ⟨ιHf, ιHf_injective⟩

def cp3 (a b : JH K) (hab : a ≠ b) (ha : a ≠ scrH) (hbs : b ≠ scrH) : Fin 3 ↪ JH K :=
  ⟨![a, b, scrH], by
    intro u v h
    fin_cases u <;> fin_cases v <;> simp_all⟩

def cpH : Fin 3 → (Fin 3 ↪ JH K) :=
  ![cp3 wRows (hb (HeaderA.fuel 0)) (by simp [wRows, hb]) (by simp [wRows, scrH]) (by simp [hb, scrH]),
    cp3 wCols (hb (HeaderA.fuel 1)) (by simp [wCols, hb]) (by simp [wCols, scrH]) (by simp [hb, scrH]),
    cp3 thrM (hb (HeaderA.fuel 2)) (by simp [thrM, hb]) (by simp [thrM, scrH]) (by simp [hb, scrH])]

def hdrL := fun l => stackStmt (ιH (K := K)) (HeaderA.prog l)

/-- The header join: ONE fixed program (for each writer bank size `K`). -/
def hjProg (K : ℕ) := BitMachineRawSequence.program (CopyAll.prog (cpH (K := K))) (hdrL (K := K))
  HeaderA.progStart (none : Option Bool) HeaderA.progCtl

theorem liftG {J' Kk L V : Type*} [DecidableEq J'] [DecidableEq Kk] (ι : Kk ↪ J')
    (P : L → TM2.Stmt (fun _ : Kk => Bool) L V)
    (W : J' → List Bool) (S T : Kk → List Bool) (hS : ∀ k, S k = W (ι k)) (l : L) (v v' : V)
    (t : ℕ)
    (hrun : ((advance P)^[t]) (⟨some l, v, S⟩ : TM2.Cfg (fun _ : Kk => Bool) L V) =
      ⟨none, v', T⟩) :
    ((advance (fun l => stackStmt ι (P l)))^[t])
        (⟨some l, v, W⟩ : TM2.Cfg (fun _ : J' => Bool) L V) =
      ⟨none, v', bank ι W T⟩ := by
  have hs := BitMachineStackRun.run ι W P (⟨some l, v, S⟩ : TM2.Cfg (fun _ : Kk => Bool) L V) t
  rw [hrun] at hs
  simp only [stackCfg] at hs
  rwa [bank_eq_self ι W S hS] at hs

/-- The entry bank of the join: the writer bank, a blank header region, unary threshold. -/
def hjIn (WB : WS K → List Bool) (thr : ℕ) : JH K → List Bool :=
  Sum.elim WB (Sum.elim (fun _ => []) ![List.replicate thr true, []])

theorem header_join (WB : WS K → List Bool) (rows cols thr : ℕ) (table suffix : List Bool)
    (hr : WB (.inr .rows) = List.replicate rows true)
    (hc : WB (.inr .cols) = List.replicate cols true)
    (ho : WB (.inr .output) = table ++ suffix) :
    ∃ t ≤ 3 * (2 * (rows + cols + thr) + 3) + 1 +
        (UnaryBinaryEncoding.coefficient * (rows + 1) ^ 2 +
          UnaryBinaryEncoding.coefficient * (cols + 1) ^ 2 +
          UnaryBinaryEncoding.coefficient * (thr + 1) ^ 2 +
          (2 * (natField rows ++ natField cols ++ natField thr).length + 2) + 3) + 1,
      ∃ v, ∃ F : JH K → List Bool,
      ((advance (hjProg K))^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩)),
          ((none : Option Bool), HeaderA.progCtl), hjIn WB thr⟩ :
          TM2.Cfg (fun _ : JH K => Bool) _ _) = ⟨none, v, F⟩ ∧
      F wOut = natField rows ++ natField cols ++ natField thr ++ table ++ suffix ∧
      ∀ a : WS K, a ≠ .inr .output → F (.inl a) = WB a := by
  set W0 := hjIn WB thr with hW0
  have hdd : ∀ i j, (cpH (K := K)) i 1 = (cpH (K := K)) j 1 → i = j := by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all [cpH, cp3, hb, HeaderA.fuel]
  obtain ⟨t1, ht1, v1, r1⟩ := CopyAll.all_run (cpH (K := K))
    (by intro i j; fin_cases i <;> fin_cases j <;> simp [cpH, cp3, wRows, wCols, thrM, hb])
    (by intro i j; fin_cases i <;> fin_cases j <;> simp [cpH, cp3, scrH, hb])
    hdd W0 (fun i => by fin_cases i <;> rfl) (rows + cols + thr)
    (by
      intro i; fin_cases i
      · show (WB (.inr .rows)).length ≤ _; rw [hr]; simp; omega
      · show (WB (.inr .cols)).length ≤ _; rw [hc]; simp; omega
      · show (List.replicate thr true).length ≤ _; simp)
    none
  set B1 := CopyAll.done (cpH (K := K)) 3 W0 with hB1
  have hS : ∀ x : HeaderA.HB, HeaderA.Hin rows cols thr table suffix x = B1 (ιH x) := by
    intro x
    rcases x with x | j
    · show [] = B1 (hb (.inl x))
      rw [hB1, CopyAll.done_off _ W0 _ (by
        intro j; fin_cases j <;> simp [cpH, cp3, hb, HeaderA.fuel]) 3]
      rfl
    · fin_cases j
      · show List.replicate rows true = B1 ((cpH (K := K)) 0 1)
        rw [hB1, CopyAll.done_dst _ hdd W0 0]
        show _ = WB (.inr .rows) ++ []
        rw [hr, List.append_nil]
      · show List.replicate cols true = B1 ((cpH (K := K)) 1 1)
        rw [hB1, CopyAll.done_dst _ hdd W0 1]
        show _ = WB (.inr .cols) ++ []
        rw [hc, List.append_nil]
      · show List.replicate thr true = B1 ((cpH (K := K)) 2 1)
        rw [hB1, CopyAll.done_dst _ hdd W0 2]
        exact (List.append_nil _).symm
      · show [] = B1 (hb (.inr 3))
        rw [hB1, CopyAll.done_off _ W0 _ (by
          intro j; fin_cases j <;> simp [cpH, cp3, hb, HeaderA.fuel]) 3]
        rfl
      · show [] = B1 (hb (.inr 4))
        rw [hB1, CopyAll.done_off _ W0 _ (by
          intro j; fin_cases j <;> simp [cpH, cp3, hb, HeaderA.fuel]) 3]
        rfl
      · show table ++ suffix = B1 wOut
        rw [hB1, CopyAll.done_off _ W0 _ (by
          intro j; fin_cases j <;> simp [cpH, cp3, hb, wOut]) 3]
        exact ho.symm
  obtain ⟨t2, ht2, v2, F, r2, hF⟩ := HeaderA.header_run rows cols thr table suffix
  have r2L := liftG (ιH (K := K)) HeaderA.prog B1 _ _ hS _ _ _ _ r2
  obtain ⟨u, hu, hrun⟩ := BitMachineRawSequence.runs (CopyAll.prog (cpH (K := K))) (hdrL (K := K))
    (.inl ⟨0, by omega⟩) HeaderA.progStart none v1 HeaderA.progCtl v2 W0 B1 _ t1 t2 r1 r2L
  refine ⟨u, by omega, _, _, hrun, ?_, ?_⟩
  · show bank ιH B1 F (ιH HeaderA.outH) = _
    rw [bank_at, hF]
  · intro a ha
    rw [bank_outside ιH B1 F (.inl a) (by
      rintro ⟨x, hx⟩
      change ιHf x = _ at hx
      unfold ιHf at hx
      split_ifs at hx with h1
      · exact ha (by simpa [wOut] using hx.symm)
      · simp [hb] at hx), hB1,
      CopyAll.done_off _ W0 _ (by intro j; fin_cases j <;> simp [cpH, cp3, hb]) 3]
    rfl

/-- Consumer form: if the writer cells hold the selected instance's unary rows and
columns and its table word (named interface: these are the success writer's exit
cells once the success bank is assembled), the join delivers
`EncodedSelectedOutput.outputBits` on the writer's output cell. -/
theorem header_join_outputBits {n m : ℕ} (hn : 0 < n) (edge : Fin m → Bool → Fin n) (Δ : ℕ)
    (γ : ℚ) (k : ℕ) (tp : (TotalFiniteConstructorScratch.select hn edge Δ γ k).Tape)
    (WB : WS K → List Bool) (suffix : List Bool)
    (hr : WB (.inr .rows) =
      List.replicate (EncodedSelectedOutput.selectedInstance hn edge Δ γ k tp).rows true)
    (hc : WB (.inr .cols) =
      List.replicate (EncodedSelectedOutput.selectedInstance hn edge Δ γ k tp).cols true)
    (ho : WB (.inr .output) =
      (EncodedSelectedOutput.selectedInstance hn edge Δ γ k tp).table ++ suffix) :
    let i := EncodedSelectedOutput.selectedInstance hn edge Δ γ k tp
    ∃ t, ∃ v, ∃ F : JH K → List Bool,
      ((advance (hjProg K))^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩)),
          ((none : Option Bool), HeaderA.progCtl), hjIn WB i.threshold⟩ :
          TM2.Cfg (fun _ : JH K => Bool) _ _) = ⟨none, v, F⟩ ∧
      F wOut = EncodedSelectedOutput.outputBits hn edge Δ γ k tp ++ suffix ∧
      ∀ a : WS K, a ≠ .inr .output → F (.inl a) = WB a := by
  intro i
  obtain ⟨t, -, v, F, hrun, hF, hfr⟩ :=
    header_join WB i.rows i.cols i.threshold i.table suffix hr hc ho
  refine ⟨t, v, F, hrun, ?_, hfr⟩
  rw [hF]
  show _ = encodeInstance i ++ suffix
  simp [encodeInstance, List.append_assoc]

end

#print axioms ιHf_injective
#print axioms header_join
#print axioms header_join_outputBits

end Paper2.HeaderJoin
