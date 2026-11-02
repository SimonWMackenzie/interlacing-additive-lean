import EthInapproximability.CurrentPaper.MatrixTemplateAddressSetup
import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.FlatTemplateMatrix

/-!
# Template entries with physical address and counter preparation

Source: locked v8 `eq:exact-H-template` and `thm:paper-materialization`.
The finite controller computes both flat-array addresses, physically copies
the two word-length counters, and executes the actual sampled-array query.
Only the selected coordinates and preserved parameter words are supplied;
neither an address, sampled word, decoded label, nor answer is supplied.
-/

namespace EthInapproximability.CurrentPaper.MatrixTemplateEntry

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Label := MatrixTemplateAddressSetup.Label ⊕
  ((Fin 2 × BitMachineCopy.Label) ⊕ FlatTemplateMatrix.Label)
abbrev Control := Bool × Option Bool × FlatTemplateMatrix.Control
abbrev Config := TM2.Cfg (fun _ : Fin 23 => Bool) Label Control

def baseFlat : FlatTemplateMatrix.Control :=
  (FlatTemplateMatrix.baseF, FlatTemplateMatrix.baseF, FlatTemplateMatrix.baseP)

def base : Control := (false, none, baseFlat)

def start : Label := .inl (0, .outer)

def addressSlots : Fin 12 ↪ Fin 23 where
  toFun i := ⟨i.val, by omega⟩
  inj' := by intro i j h; apply Fin.ext; exact congrArg (fun x : Fin 23 => x.val) h

def copySlots (p : Fin 2) : Fin 3 ↪ Fin 23 where
  toFun := ![![12, 13, 20], ![5, 14, 20]] p
  inj' := by fin_cases p <;> decide

def flatSlots : Fin 14 ↪ Fin 23 where
  toFun := ![9, 7, 8, 15, 20, 21, 22, 13, 17, 11, 16, 14, 18, 19]
  inj' := by decide

def flatStart : Label := .inr (.inr (.inl (.inr .test)))

def copyNext (p : Fin 2) : Option Label :=
  if p = 0 then some (.inr (.inl (1, .scan))) else some flatStart

def program : Label → TM2.Stmt (fun _ : Fin 23 => Bool) Label Control
  | .inl l => stmt addressSlots Sum.inl (fun b => (b, none, baseFlat)) Prod.fst
      (some (.inr (.inl (0, .scan)))) (MatrixTemplateAddressSetup.program l)
  | .inr (.inl (p, l)) => stmt (copySlots p) (fun k => .inr (.inl (p, k)))
      (fun b => (false, b, baseFlat)) (fun s => s.2.1) (copyNext p) (BitMachineCopy.program l)
  | .inr (.inr l) => stmt flatSlots (fun k => .inr (.inr k))
      (fun v => (false, none, v)) (fun s => s.2.2) none (FlatTemplateMatrix.program l)

def contents (ell width1 z d alpha a q : ℕ) (first second out : List Bool)
    (addr1 mid addr2 count1 count2 pref bits : List Bool) : Fin 23 → List Bool :=
  fun k => match k.val with
    | 0 => List.replicate ell true
    | 1 => List.replicate width1 true
    | 2 => List.replicate z true
    | 3 => List.replicate d true
    | 4 => List.replicate alpha true
    | 5 => List.replicate a true
    | 9 => addr1
    | 10 => mid
    | 11 => addr2
    | 12 => List.replicate q true
    | 13 => count1
    | 14 => count2
    | 15 => first
    | 16 => second
    | 17 => pref
    | 18 => bits
    | 19 => out
    | _ => []

def cfg (l : Option Label) (v : Control) (S : Fin 23 → List Bool) : Config := ⟨l, v, S⟩
def run (n : ℕ) (c : Config) := ((advance program)^[n]) c

private theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem address_cfg (l : Option MatrixTemplateAddressSetup.Label) (v : Bool)
    (ell width1 z d alpha a q : ℕ) (first second out addr1 mid addr2 : List Bool) :
    BitMachineStackEmbedding.cfg addressSlots
      (contents ell width1 z d alpha a q first second out [] [] [] [] [] [] [])
      Sum.inl (fun b => (b, none, baseFlat)) (some (.inr (.inl (0, .scan))))
      (MatrixTemplateAddressSetup.cfg l v
        (MatrixTemplateAddressSetup.contents ell width1 z d alpha a addr1 mid addr2)) =
      cfg (l.elim (some (.inr (.inl (0, .scan)))) (fun k => some (.inl k)))
        (v, none, baseFlat)
        (contents ell width1 z d alpha a q first second out addr1 mid addr2 [] [] [] []) := by
  have hs : bank addressSlots
      (contents ell width1 z d alpha a q first second out [] [] [] [] [] [] [])
      (MatrixTemplateAddressSetup.contents ell width1 z d alpha a addr1 mid addr2) =
      contents ell width1 z d alpha a q first second out addr1 mid addr2 [] [] [] [] := by
    funext j
    fin_cases j
    · exact bank_at addressSlots _ _ 0
    · exact bank_at addressSlots _ _ 1
    · exact bank_at addressSlots _ _ 2
    · exact bank_at addressSlots _ _ 3
    · exact bank_at addressSlots _ _ 4
    · exact bank_at addressSlots _ _ 5
    · exact bank_at addressSlots _ _ 6
    · exact bank_at addressSlots _ _ 7
    · exact bank_at addressSlots _ _ 8
    · exact bank_at addressSlots _ _ 9
    · exact bank_at addressSlots _ _ 10
    · exact bank_at addressSlots _ _ 11
    all_goals
      unfold bank
      split_ifs with h
      · obtain ⟨i, hi⟩ := h
        have hv := congrArg (fun j : Fin 23 => j.val) hi
        have hil := i.isLt
        dsimp [addressSlots] at hv
        omega
      · simp [contents]
  cases l <;> exact congrArg (fun S => (⟨_, (v, none, baseFlat), S⟩ : Config)) hs

theorem copy_run (p : Fin 2) (S : Fin 23 → List Bool)
    (hwork : S (copySlots p 2) = []) :
    ∃ t ≤ 2 * (S (copySlots p 0)).length + 2,
      run t (cfg (some (.inr (.inl (p, .scan)))) base S) =
        cfg (copyNext p) base (Function.update S (copySlots p 1)
          (S (copySlots p 0) ++ S (copySlots p 1))) := by
  let input := BitMachineCopy.cfg (some .scan) none
    (S (copySlots p 0)) (S (copySlots p 1)) []
  let output := BitMachineCopy.cfg none none (S (copySlots p 0))
    (S (copySlots p 0) ++ S (copySlots p 1)) []
  have hr : ((advance BitMachineCopy.program)^[2 * (S (copySlots p 0)).length + 2])
      input = output := BitMachineCopy.run_correct none _ _
  have hh : (((advance BitMachineCopy.program)^[2 * (S (copySlots p 0)).length + 2])
      input).l = none := by rw [hr]; rfl
  obtain ⟨t, ht, he⟩ := outputs (copySlots p) S (fun k => .inr (.inl (p, k)))
    (fun b => (false, b, baseFlat)) (fun s => s.2.1) (fun _ => rfl) (copyNext p)
    BitMachineCopy.program program (fun _ => rfl) input
    (2 * (S (copySlots p 0)).length + 2) hh
  rw [hr] at he
  have hbank : bank (copySlots p) S input.stk = S := by
    apply bank_eq_self
    intro k
    fin_cases k
    · rfl
    · rfl
    · exact hwork.symm
  have ho : output.stk = Function.update input.stk 1
      (S (copySlots p 0) ++ S (copySlots p 1)) := by
    funext k; fin_cases k <;> rfl
  have hi : BitMachineStackEmbedding.cfg (copySlots p) S (fun k => .inr (.inl (p, k)))
      (fun b => (false, b, baseFlat)) (copyNext p) input =
      cfg (some (.inr (.inl (p, .scan)))) base S := by
    change (⟨_, _, bank (copySlots p) S input.stk⟩ : Config) = _
    rw [hbank]
    rfl
  have ho' : BitMachineStackEmbedding.cfg (copySlots p) S (fun k => .inr (.inl (p, k)))
      (fun b => (false, b, baseFlat)) (copyNext p) output =
      cfg (copyNext p) base (Function.update S (copySlots p 1)
        (S (copySlots p 0) ++ S (copySlots p 1))) := by
    change (⟨_, _, bank (copySlots p) S output.stk⟩ : Config) = _
    rw [ho, bank_update, hbank]
    rfl
  exact ⟨t, ht, by simpa only [run, hi, ho'] using he⟩

private theorem flat_cfg (l : Option FlatTemplateMatrix.Label)
    (ell width1 z d alpha a q : ℕ) (first second mid : List Bool)
    (oldout old1 old2 oldc1 oldc2 out addr1 addr2 count1 count2 pref bits : List Bool) :
    BitMachineStackEmbedding.cfg flatSlots
      (contents ell width1 z d alpha a q first second oldout old1 mid old2 oldc1 oldc2 [] [])
      (fun k => .inr (.inr k)) (fun v => (false, none, v)) none
      (FlatTemplateMatrix.cfg l addr1 first pref count1 addr2 second bits count2 out) =
      cfg (l.map fun k => .inr (.inr k)) base
        (contents ell width1 z d alpha a q first second out
          addr1 mid addr2 count1 count2 pref bits) := by
  have hs : bank flatSlots
      (contents ell width1 z d alpha a q first second oldout old1 mid old2 oldc1 oldc2 [] [])
      (FlatTemplateMatrix.cfg l addr1 first pref count1 addr2 second bits count2 out).stk =
      contents ell width1 z d alpha a q first second out
        addr1 mid addr2 count1 count2 pref bits := by
    funext j
    fin_cases j
    all_goals first
      | exact bank_at flatSlots _ _ 0
      | exact bank_at flatSlots _ _ 1
      | exact bank_at flatSlots _ _ 2
      | exact bank_at flatSlots _ _ 3
      | exact bank_at flatSlots _ _ 4
      | exact bank_at flatSlots _ _ 5
      | exact bank_at flatSlots _ _ 6
      | exact bank_at flatSlots _ _ 7
      | exact bank_at flatSlots _ _ 8
      | exact bank_at flatSlots _ _ 9
      | exact bank_at flatSlots _ _ 10
      | exact bank_at flatSlots _ _ 11
      | exact bank_at flatSlots _ _ 12
      | exact bank_at flatSlots _ _ 13
      | (unfold bank; split_ifs with h
         · obtain ⟨i, hi⟩ := h
           have hv := congrArg (fun j : Fin 23 => j.val) hi
           fin_cases i <;> norm_num [flatSlots] at hv
         · simp [contents])
  cases l <;> exact congrArg (fun S => (⟨_, base, S⟩ : Config)) hs

def preparationBound (ell width1 z d alpha a q : ℕ) : ℕ :=
  MatrixTemplateAddressSetup.bound ell width1 z d alpha a + 2 * q + 2 * a + 4

/-- The two flat-array addresses and two consuming counters are physically
prepared, with all original parameter words and both arrays preserved. -/
theorem prepare_run (ell width1 z d alpha a q : ℕ) (first second out : List Bool) :
    ∃ t ≤ preparationBound ell width1 z d alpha a q,
      run t (cfg (some (.inl (0, .outer))) base
        (contents ell width1 z d alpha a q first second out [] [] [] [] [] [] [])) =
      cfg (some flatStart) base (contents ell width1 z d alpha a q first second out
        (List.replicate (ell * width1) true) (List.replicate (z * d + alpha) true)
        (List.replicate ((z * d + alpha) * a) true)
        (List.replicate q true) (List.replicate a true) [] []) := by
  let S₀ := contents ell width1 z d alpha a q first second out [] [] [] [] [] [] []
  let S₁ := contents ell width1 z d alpha a q first second out
    (List.replicate (ell * width1) true) (List.replicate (z * d + alpha) true)
    (List.replicate ((z * d + alpha) * a) true) [] [] [] []
  let S₂ := contents ell width1 z d alpha a q first second out
    (List.replicate (ell * width1) true) (List.replicate (z * d + alpha) true)
    (List.replicate ((z * d + alpha) * a) true) (List.replicate q true) [] [] []
  let S₃ := contents ell width1 z d alpha a q first second out
    (List.replicate (ell * width1) true) (List.replicate (z * d + alpha) true)
    (List.replicate ((z * d + alpha) * a) true)
    (List.replicate q true) (List.replicate a true) [] []
  let input := MatrixTemplateAddressSetup.cfg (some (0, .outer)) false
    (MatrixTemplateAddressSetup.contents ell width1 z d alpha a [] [] [])
  obtain ⟨ka, hka, hra⟩ := MatrixTemplateAddressSetup.setup_run ell width1 z d alpha a false [] []
  have hha : (((advance MatrixTemplateAddressSetup.program)^[ka]) input).l = none := by
    change (MatrixTemplateAddressSetup.run ka _).l = none
    rw [hra]
    rfl
  obtain ⟨ta, hta, hea⟩ := outputs addressSlots S₀ Sum.inl
    (fun b => (b, none, baseFlat)) Prod.fst (fun _ => rfl)
    (some (.inr (.inl (0, .scan)))) MatrixTemplateAddressSetup.program program (fun _ => rfl)
    input ka hha
  change (((advance MatrixTemplateAddressSetup.program)^[ka]) _) = _ at hra
  rw [hra] at hea
  change (((advance program)^[ta])
    (BitMachineStackEmbedding.cfg addressSlots
      (contents ell width1 z d alpha a q first second out [] [] [] [] [] [] [])
      Sum.inl (fun b => (b, none, baseFlat)) (some (.inr (.inl (0, .scan))))
      (MatrixTemplateAddressSetup.cfg (some (0, .outer)) false
        (MatrixTemplateAddressSetup.contents ell width1 z d alpha a [] [] [])))) = _ at hea
  rw [address_cfg, address_cfg] at hea
  have ha : run ta (cfg (some (.inl (0, .outer))) base S₀) =
      cfg (some (.inr (.inl (0, .scan)))) base S₁ := by
    simpa only [run, S₀, S₁, base, List.append_nil] using hea
  obtain ⟨tq, htq, hq⟩ := copy_run 0 S₁ rfl
  have eq₁ : Function.update S₁ (copySlots 0 1)
      (S₁ (copySlots 0 0) ++ S₁ (copySlots 0 1)) = S₂ := by
    funext k; fin_cases k <;> simp [S₁, S₂, contents, copySlots, Function.update]
  rw [eq₁] at hq
  obtain ⟨tb, htb, hb⟩ := copy_run 1 S₂ rfl
  have eq₂ : Function.update S₂ (copySlots 1 1)
      (S₂ (copySlots 1 0) ++ S₂ (copySlots 1 1)) = S₃ := by
    funext k; fin_cases k <;> simp [S₂, S₃, contents, copySlots, Function.update]
  rw [eq₂] at hb
  refine ⟨ta + tq + tb, ?_, (run_add ((run_add ha tq).trans hq) tb).trans hb⟩
  change tq ≤ 2 * (List.replicate q true).length + 2 at htq
  change tb ≤ 2 * (List.replicate a true).length + 2 at htb
  simp only [List.length_replicate] at htq htb
  unfold preparationBound
  omega

def bound (ell width1 z d alpha a q size1 size2 : ℕ) : ℕ :=
  preparationBound ell width1 z d alpha a q +
    (FlatTemplateMatrix.readBound q (ell * width1) size1 +
      FlatTemplateMatrix.readBound a ((z * d + alpha) * a) size2 +
      (8 * 2 ^ a + 3 * a + 10))

/-- The template matrix value is produced from the flat sampled arrays and
selected unary coordinates, without preloaded addresses or sampled words. -/
theorem template_run {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (C₁ : ExactConstruction.FirstFamily a N₁) (C₂ : ExactConstruction.SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool) (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (p : Fin 4) (z : Fin N₂) (c : ExactConstruction.Columns d N₁) (out : List Bool) :
    let q := ExactConstruction.prefixLength a
    let ell := (c.2 p).2.val
    let alpha := (c.2 p).1.val
    let data := MatrixMaterialization.storeBits C₁ C₂ v
    ∃ t ≤ bound ell (q + 3) z.val d alpha a q data.first.length data.second.length,
      run t (cfg (some (.inl (0, .outer))) base
        (contents ell (q + 3) z.val d alpha a q data.first data.second out
          [] [] [] [] [] [] [])) =
      cfg none base (contents ell (q + 3) z.val d alpha a q data.first data.second
        (ExactConstruction.matrix ha C₁ C₂ v cap (.inl (p, z)) c :: out)
        (List.replicate (ell * (q + 3) + q) true)
        (List.replicate (z.val * d + alpha) true)
        (List.replicate ((z.val * d + alpha) * a + a) true) [] [] [] []) := by
  dsimp only
  let q := ExactConstruction.prefixLength a
  let ell := (c.2 p).2.val
  let alpha := (c.2 p).1.val
  let s₁ := ell * (q + 3)
  let mid := z.val * d + alpha
  let s₂ := mid * a
  let data := MatrixMaterialization.storeBits C₁ C₂ v
  let S := contents ell (q + 3) z.val d alpha a q data.first data.second out
    (List.replicate s₁ true) (List.replicate mid true) (List.replicate s₂ true)
    (List.replicate q true) (List.replicate a true) [] []
  obtain ⟨tp, htp, hp⟩ := prepare_run ell (q + 3) z.val d alpha a q data.first data.second out
  obtain ⟨k, hk, hr⟩ := FlatTemplateMatrix.template_run ha C₁ C₂ v cap p z c out
  let input := FlatTemplateMatrix.cfg (some (.inl (.inr .test)))
    (List.replicate s₁ true) data.first [] (List.replicate q true)
    (List.replicate s₂ true) data.second [] (List.replicate a true) out
  have hh : (((advance FlatTemplateMatrix.program)^[k]) input).l = none := by
    change (FlatTemplateMatrix.run k _).l = none
    rw [hr]
    rfl
  obtain ⟨tq, htq, he⟩ := outputs flatSlots S (fun l => .inr (.inr l))
    (fun w => (false, none, w)) (fun w => w.2.2) (fun _ => rfl) none
    FlatTemplateMatrix.program program (fun _ => rfl) input k hh
  change (((advance FlatTemplateMatrix.program)^[k]) _) = _ at hr
  rw [hr] at he
  change (((advance program)^[tq])
    (BitMachineStackEmbedding.cfg flatSlots
      (contents ell (q + 3) z.val d alpha a q data.first data.second out
        (List.replicate s₁ true) (List.replicate mid true) (List.replicate s₂ true)
        (List.replicate q true) (List.replicate a true) [] [])
      (fun l => .inr (.inr l)) (fun w => (false, none, w)) none
      (FlatTemplateMatrix.cfg (some (.inl (.inr .test)))
        (List.replicate s₁ true) data.first [] (List.replicate q true)
        (List.replicate s₂ true) data.second [] (List.replicate a true) out))) = _ at he
  rw [flat_cfg, flat_cfg] at he
  refine ⟨tp + tq, Nat.add_le_add htp (htq.trans hk), ?_⟩
  exact (run_add hp tq).trans he

end EthInapproximability.CurrentPaper.MatrixTemplateEntry
