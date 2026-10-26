import CurrentAdditive.YaoCutScanBody
import EthInapproximability.CurrentPaper.FuelLoop

/-! A unary-fuel scan of all positive cut candidates. The body contains a
literal tester; the parameterized theorem records precisely the independent
tester run needed for later concrete instantiation. -/

namespace CurrentAdditive.SmallBias.YaoCutScanLoop

open Turing EthInapproximability.CurrentPaper
open BitMachineEncoding
open YaoCutScanBody

variable {LT VT : Type*}

def count (g : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | j + 1 => count g j + if g (j + 1) then 1 else 0

def scanState (S0 : Fin 16 → List Bool) (m : ℕ) (g : ℕ → Bool)
    (j : ℕ) : Fin 16 → List Bool :=
  Function.update
    (Function.update
      (Function.update S0 5 (List.replicate (m - j) true))
      4 (List.replicate j true))
    3 (List.replicate (count g j) true)

theorem scanState_5 (S0 : Fin 16 → List Bool) (m : ℕ)
    (g : ℕ → Bool) (j : ℕ) :
    scanState S0 m g j 5 = List.replicate (m - j) true := by
  simp [scanState]

theorem scanState_4 (S0 : Fin 16 → List Bool) (m : ℕ)
    (g : ℕ → Bool) (j : ℕ) :
    scanState S0 m g j 4 = List.replicate j true := by
  simp [scanState]

theorem scanState_3 (S0 : Fin 16 → List Bool) (m : ℕ)
    (g : ℕ → Bool) (j : ℕ) :
    scanState S0 m g j 3 = List.replicate (count g j) true := by
  simp [scanState]

theorem scanState_other (S0 : Fin 16 → List Bool) (m : ℕ)
    (g : ℕ → Bool) (j : ℕ) (z : Fin 16)
    (hz3 : z ≠ 3) (hz4 : z ≠ 4) (hz5 : z ≠ 5) :
    scanState S0 m g j z = S0 z := by
  simp [scanState, hz3, hz4, hz5]

theorem scanState_start (S0 : Fin 16 → List Bool) (m : ℕ)
    (g : ℕ → Bool)
    (hf : S0 5 = List.replicate m true)
    (hx : S0 4 = []) (hc : S0 3 = []) :
    scanState S0 m g 0 = S0 := by
  funext z
  by_cases h3 : z = 3
  · subst z; simp [scanState_3, count, hc]
  by_cases h4 : z = 4
  · subst z; simp [scanState_4, hx]
  by_cases h5 : z = 5
  · subst z; simp [scanState_5, hf]
  exact scanState_other S0 m g 0 z h3 h4 h5

theorem scanState_pop (S0 : Fin 16 → List Bool) (m : ℕ)
    (g : ℕ → Bool) (j : ℕ) (hj : j < m) :
    Function.update (scanState S0 m g j) 5
      ((scanState S0 m g j 5).tail) =
    Function.update (Function.update
      (Function.update S0 5 (List.replicate (m - (j + 1)) true))
      4 (List.replicate j true))
      3 (List.replicate (count g j) true) := by
  have hsub : m - j = (m - (j + 1)) + 1 := by omega
  funext z
  by_cases h3 : z = 3 <;> by_cases h4 : z = 4 <;>
    by_cases h5 : z = 5 <;>
    simp_all [scanState, List.tail_replicate,
      Function.update_apply]

def scanProgram (P : LT → TM2.Stmt (fun _ : Fin 16 => Bool) LT VT)
    (l₀ : LT) (v₀ : VT) :=
  FuelLoop.program (body P l₀ v₀) bodyStart (bodyControl v₀) (5 : Fin 16)

def scanBound (B : ℕ → ℕ) (m : ℕ) : ℕ :=
  Finset.sum (Finset.range m) (fun j => B (j + 1) + 4)

theorem scan_run (P : LT → TM2.Stmt (fun _ : Fin 16 => Bool) LT VT)
    (l₀ : LT) (v₀ : VT) (B : ℕ → ℕ)
    (g : ℕ → Bool) (R m : ℕ)
    (hTester : ∀ (S : Fin 16 → List Bool) (j : ℕ),
      S 4 = List.replicate j true →
      S 6 = List.replicate R true → S 12 = [] → scratchEmpty S →
      ∃ u ≤ B j,
        ((advance P)^[u])
          (⟨some l₀, v₀, S⟩ : TM2.Cfg (fun _ : Fin 16 => Bool) LT VT) =
        ⟨none, v₀, Function.update S 12 [g j]⟩)
    (S0 : Fin 16 → List Bool)
    (hf : S0 5 = List.replicate m true)
    (hx : S0 4 = []) (hc : S0 3 = [])
    (hR : S0 6 = List.replicate R true) (hO : S0 12 = [])
    (hScratch : scratchEmpty S0) :
    ∃ u ≤ m * (scanBound B m + 1) + 1,
      ((advance (scanProgram P l₀ v₀))^[u])
        (⟨some (.inl ()), (none, bodyControl v₀), S0⟩ :
          TM2.Cfg (fun _ : Fin 16 => Bool) _ _) =
      ⟨none, (none, bodyControl v₀),
        scanState S0 m g m⟩ := by
  let Sq := scanState S0 m g
  have hne : ∀ j < m, Sq j 5 ≠ [] := by
    intro j hj
    rw [show Sq j 5 = List.replicate (m - j) true by
      exact scanState_5 S0 m g j]
    intro h
    have := congrArg List.length h
    simp at this
    omega
  have hend : Sq m 5 = [] := by
    rw [show Sq m 5 = List.replicate (m - m) true by
      exact scanState_5 S0 m g m]
    simp
  have hbody : ∀ j < m, ∃ u ≤ scanBound B m,
      ((advance (body P l₀ v₀))^[u])
        (⟨some bodyStart, bodyControl v₀,
          Function.update (Sq j) 5 (Sq j 5).tail⟩ :
          TM2.Cfg (fun _ : Fin 16 => Bool) _ _) =
        ⟨none, bodyControl v₀, Sq (j + 1)⟩ := by
    intro j hj
    let Sp := Function.update (Sq j) 5 (Sq j 5).tail
    have hx' : Sp 4 = List.replicate j true := by
      simp [Sp, Sq, scanState_4]
    have hR' : Sp 6 = List.replicate R true := by
      simp [Sp, Sq, scanState_other S0 m g j 6 (by decide)
        (by decide) (by decide), hR]
    have hO' : Sp 12 = [] := by
      simp [Sp, Sq, scanState_other S0 m g j 12 (by decide)
        (by decide) (by decide), hO]
    have hScratch' : scratchEmpty Sp := by
      intro z hz hz12
      have hz3 : z ≠ 3 := by intro he; subst z; norm_num at hz
      have hz4 : z ≠ 4 := by intro he; subst z; norm_num at hz
      have hz5 : z ≠ 5 := by intro he; subst z; norm_num at hz
      simpa [Sp, Sq, scanState, Function.update_apply,
        hz3, hz4, hz5, hz3.symm, hz4.symm, hz5.symm]
        using hScratch z hz hz12
    obtain ⟨u, hu, hr⟩ := body_run P l₀ v₀ B g R hTester Sp j hx' hR' hO' hScratch'
    have he : Function.update
        (Function.update Sp 4 (List.replicate (j + 1) true)) 3
          (if g (j + 1) then true :: Sp 3 else Sp 3) =
        Sq (j + 1) := by
      have hcnt : Sp 3 = List.replicate (count g j) true := by
        simp [Sp, Sq, scanState_3]
      rw [hcnt]
      have hcnext :
          (if g (j + 1) then true :: List.replicate (count g j) true
           else List.replicate (count g j) true) =
          List.replicate (count g (j + 1)) true := by
        simp only [count]
        cases h : g (j + 1) <;> simp [List.replicate_succ]
      rw [hcnext]
      rw [show Sp = Function.update (Function.update
        (Function.update S0 5 (List.replicate (m - (j + 1)) true))
        4 (List.replicate j true)) 3 (List.replicate (count g j) true) from
          scanState_pop S0 m g j hj]
      funext z
      by_cases h3 : z = 3 <;> by_cases h4 : z = 4 <;>
        by_cases h5 : z = 5 <;>
        simp_all [Sq, scanState, Function.update_apply]
    rw [he] at hr
    refine ⟨u, le_trans hu ?_, hr⟩
    simpa only [scanBound] using
      (Finset.single_le_sum (f := fun j => B (j + 1) + 4)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj))
  obtain ⟨u, hu, hr⟩ := FuelLoop.loop_run (body P l₀ v₀) bodyStart
    (bodyControl v₀) (5 : Fin 16) (scanBound B m) m Sq hne hend hbody
  exact ⟨u, hu, by
    simpa only [scanProgram, Sq, scanState_start S0 m g hf hx hc] using hr⟩

#print axioms scan_run

end CurrentAdditive.SmallBias.YaoCutScanLoop
