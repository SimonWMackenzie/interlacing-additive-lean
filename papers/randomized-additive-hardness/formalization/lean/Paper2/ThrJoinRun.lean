import Paper2.ThrJoin

/-! Unit 3, segment (5): the run of `ThrJoin.thrJoin` (produce the unary threshold from the
admitted raw public counts and install it in the header threshold cell). -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.ThrJoin

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.HeaderJoin (JH hjIn wOut thrM scrH)
open Paper2.SuccessXfer (OS JT)
open Paper2.SuccessGraph (JT2 preJHm)
open Paper2.ThrProducer (TK thrC ctrC scrC xC srcI outI T0 thrProg thrStart thrCtl Xv thrBd)

/-- The JT2 bank before the threshold: success start bank, parameter-, `m`- and
threshold-free writer bank, blank side region. -/
def X0 (n p s q₁ q₂ w Q k mX mY : ℕ) (word : List Bool) (g : EncodedGraph.Graph) (r : ℕ)
    (output : List Bool) : JT2 → List Bool :=
  Sum.elim (Sum.elim (SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word)
    (Sum.elim (preJHm g r 0 output) (fun _ => []))) (fun _ => [])

def X1 (n p s q₁ q₂ w Q k mX mY : ℕ) (word : List Bool) (g : EncodedGraph.Graph) (r : ℕ)
    (output : List Bool) (thr : ℕ) : JT2 → List Bool :=
  Sum.elim (Sum.elim (SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word)
    (Sum.elim (Function.update (preJHm g r 0 output) thrM (List.replicate thr true))
      (fun _ => []))) (fun _ => [])

def vv (p s q₂ w Q : ℕ) : Fin 5 → ℕ := ![p, s, q₂, w, Q]
def valT (p s q₂ w Q k : ℕ) : Fin 6 → ℕ := ![p, s, q₂, w, Q, k]

theorem cpT_src (i : Fin 6) : cpT i 0 = srcJ (sT i) := rfl
theorem cpT_dst (i : Fin 6) : cpT i 1 = .inr (dT i) := rfl
theorem cpT_scr (i : Fin 6) : cpT i 2 = scrJ := rfl

def joinBd (p s q₂ w Q k : ℕ) : ℕ :=
  6 * (2 * (p + s + q₂ + w + Q + k) + 3) + 1 + thrBd k (vv p s q₂ w Q) + 1 +
    (1 * (2 * (k * Xv (vv p s q₂ w Q) + (Nat.clog 2 p + 1)) + 3) + 1) + 1

theorem preJHm_thr0 (g : EncodedGraph.Graph) (r : ℕ) (output : List Bool) :
    preJHm g r 0 output thrM = [] := by
  unfold preJHm
  rw [Function.update_of_ne (by simp [thrM, SuccessInstall.mC, SuccessXfer.wAux])]
  rfl

theorem thr_join_run (n p s q₁ q₂ w Q k mX mY : ℕ) (word : List Bool) (g : EncodedGraph.Graph)
    (r : ℕ) (output : List Bool) :
    ∃ t ≤ joinBd p s q₂ w Q k, ∃ v, ∃ F : TK → List Bool,
      ((advance thrJoin)^[t])
          (⟨some (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
              (.inl ⟨0, by omega⟩))),
            (((none : Option Bool), thrCtl), (none : Option Bool)),
            Sum.elim (X0 n p s q₁ q₂ w Q k mX mY word g r output) (fun _ => [])⟩ :
            TM2.Cfg (fun _ : JT3 => Bool) _ _) =
        ⟨none, (((none : Option Bool), thrCtl), v),
          Sum.elim (X1 n p s q₁ q₂ w Q k mX mY word g r output
            (k * Xv (vv p s q₂ w Q) + (Nat.clog 2 p + 1))) F⟩ ∧
      F thrC = List.replicate (k * Xv (vv p s q₂ w Q) + (Nat.clog 2 p + 1)) true ∧
      F ctrC = [] ∧ F scrC = [] := by
  let T : JT3 → List Bool := Sum.elim (X0 n p s q₁ q₂ w Q k mX mY word g r output) (fun _ => [])
  have hval : ∀ i : Fin 6, T (cpT i 0) = List.replicate (valT p s q₂ w Q k i) true := by
    intro i
    refine (SamplerParameterJoin.nrSrc_value n p s q₁ q₂ w Q k mX mY word (sT i)).trans ?_
    fin_cases i <;> rfl
  have hsd : ∀ i j, cpT i 0 ≠ cpT j 1 := by
    intro i j h
    rw [cpT_src, cpT_dst] at h
    simp [srcJ] at h
  have hzd : ∀ i j, cpT i 2 ≠ cpT j 1 := by
    intro i j h
    rw [cpT_scr, cpT_dst] at h
    simp only [scrJ, Sum.inr.injEq] at h
    fin_cases j <;> simp [dT, srcI, ctrC, scrC] at h
  have hdd : ∀ i j, cpT i 1 = cpT j 1 → i = j := by
    intro i j h
    rw [cpT_dst, cpT_dst] at h
    exact dT_inj i j (Sum.inr_injective h)
  obtain ⟨tA, htA, vA, rA⟩ := CopyAll.all_run cpT hsd hzd hdd T (fun i => rfl)
    (p + s + q₂ + w + Q + k)
    (by
      intro i
      rw [hval, List.length_replicate]
      fin_cases i <;> simp [valT] <;> omega) none
  have hA : CopyAll.done cpT 6 T =
      Sum.elim (X0 n p s q₁ q₂ w Q k mX mY word g r output) (T0 k (vv p s q₂ w Q)) := by
    funext z
    by_cases hz' : ∃ j, cpT j 1 = z
    · obtain ⟨j, rfl⟩ := hz'
      rw [CopyAll.done_dst cpT hdd T j, hval j, cpT_dst]
      change _ ++ [] = T0 k (vv p s q₂ w Q) (dT j)
      rw [List.append_nil]
      fin_cases j <;> rfl
    · rw [CopyAll.done_off cpT T z (fun j h => hz' ⟨j, h⟩)]
      rcases z with z | y
      · rfl
      · change [] = T0 k (vv p s q₂ w Q) y
        rcases y with a | ⟨i, x⟩
        · fin_cases a
          · rfl
          · rfl
          · exact absurd ⟨5, rfl⟩ hz'
          · rfl
        · by_cases hx : x = .inl 0
          · subst hx
            fin_cases i
            · exact absurd ⟨0, rfl⟩ hz'
            · exact absurd ⟨1, rfl⟩ hz'
            · exact absurd ⟨2, rfl⟩ hz'
            · exact absurd ⟨3, rfl⟩ hz'
            · exact absurd ⟨4, rfl⟩ hz'
          · show [] = (if x = .inl 0 then _ else [])
            rw [if_neg hx]
  rw [hA] at rA
  -- (2) the threshold producer, lifted
  obtain ⟨tB, htB, vc, F, rB, hFt, hFx, hFc, hFz, hFo, hFs⟩ :=
    ThrProducer.thr_run k (vv p s q₂ w Q)
  have rB' := BitMachineStackRun.run ιT
    (Sum.elim (X0 n p s q₁ q₂ w Q k mX mY word g r output) (T0 k (vv p s q₂ w Q))) thrProg
    (⟨some thrStart, thrCtl, T0 k (vv p s q₂ w Q)⟩ : TM2.Cfg (fun _ : TK => Bool) _ _) tB
  rw [rB] at rB'
  simp only [stackCfg] at rB'
  rw [bank_T, bank_T] at rB'
  obtain ⟨a1, ha1, R1⟩ := BitMachineRawSequence.runs (CopyAll.prog cpT) thrL
    (.inl ⟨0, by omega⟩) thrStart (none : Option Bool) vA thrCtl vc _ _ _ tA tB rA rB'
  -- (3) install the threshold
  obtain ⟨tC, htC, vC, rC⟩ := CopyAll.all_run cpM
    (by intro i j h; fin_cases i; fin_cases j; simp [cpM, thrJ] at h)
    (by intro i j h; fin_cases i; fin_cases j; simp [cpM, thrJ, scrJ] at h)
    (by intro i j _; fin_cases i; fin_cases j; rfl)
    (Sum.elim (X0 n p s q₁ q₂ w Q k mX mY word g r output) F)
    (by intro i; fin_cases i; exact hFz)
    (k * Xv (vv p s q₂ w Q) + (Nat.clog 2 p + 1))
    (by
      intro i
      fin_cases i
      change (F thrC).length ≤ _
      rw [hFt]
      show (List.replicate _ true).length ≤ _
      rw [List.length_replicate]
      exact le_refl _) none
  have hC : CopyAll.done cpM 1 (Sum.elim (X0 n p s q₁ q₂ w Q k mX mY word g r output) F) =
      Sum.elim (X1 n p s q₁ q₂ w Q k mX mY word g r output
        (k * Xv (vv p s q₂ w Q) + (Nat.clog 2 p + 1))) F := by
    funext z
    by_cases hz' : z = thrJ
    · subst hz'
      change CopyAll.done cpM 1 _ (cpM 0 1) = _
      rw [CopyAll.done_dst cpM (by intro i j _; fin_cases i; fin_cases j; rfl) _ 0]
      change F thrC ++ preJHm g r 0 output thrM =
        Function.update (preJHm g r 0 output) thrM _ thrM
      rw [preJHm_thr0, List.append_nil, Function.update_self, hFt]
      rfl
    · rw [CopyAll.done_off cpM _ z (by intro j h; fin_cases j; exact hz' h.symm)]
      rcases z with ((z | (z | z)) | z) | z
      · rfl
      · change preJHm g r 0 output z = Function.update (preJHm g r 0 output) thrM _ z
        rw [Function.update_of_ne]
        intro h
        exact hz' (by rw [h]; rfl)
      · rfl
      · rfl
      · rfl
  rw [hC] at rC
  obtain ⟨a2, ha2, R2⟩ := BitMachineRawSequence.runs j1 (CopyAll.prog cpM)
    (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩)) (.inl ⟨0, by omega⟩)
    ((none : Option Bool), thrCtl) _ (none : Option Bool) _ _ _ _ a1 tC R1 rC
  refine ⟨a2, ?_, vC, F, R2, hFt, hFc, hFz⟩
  unfold joinBd
  omega

end

#print axioms preJHm_thr0
#print axioms thr_join_run

end Paper2.ThrJoin
