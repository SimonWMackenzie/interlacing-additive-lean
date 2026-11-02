import CurrentAdditive.YaoCutCounting
import EthInapproximability.CurrentPaper.G5fLevelFull
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! A physical scan round: increment the unary candidate, execute a supplied
literal tester, consume its bit, and tally a passing candidate. The supplied
tester's run theorem concerns its own program and its full ambient bank; no
conclusion about the counting loop is assumed. -/

namespace CurrentAdditive.SmallBias.YaoCutScanBody

open Turing EthInapproximability.CurrentPaper
open BitMachineEncoding

variable {LT VT : Type*}

def scratchEmpty (S : Fin 16 → List Bool) : Prop :=
  ∀ z : Fin 16, 7 ≤ z.val → z ≠ 12 → S z = []

def tallyP : Unit → TM2.Stmt (fun _ : Fin 16 => Bool) Unit (Option Bool) :=
  fun _ => .pop 12 (fun _ b => b)
    (.branch (fun v => v == some true)
      (.push 3 (fun _ => true) (.load (fun _ => none) .halt))
      (.load (fun _ => none) .halt))

theorem tally_run (S : Fin 16 → List Bool) (v : Bool)
    (h : S 12 = [v]) :
    ((advance tallyP)^[1])
      (⟨some (), none, S⟩ : TM2.Cfg (fun _ : Fin 16 => Bool) Unit (Option Bool)) =
    ⟨none, none, Function.update (Function.update S 12 []) 3
      (if v then true :: S 3 else S 3)⟩ := by
  cases v <;>
    simp [advance, TM2.step, tallyP, TM2.stepAux, h,
      Function.update_of_ne]

def body (P : LT → TM2.Stmt (fun _ : Fin 16 => Bool) LT VT)
    (l₀ : LT) (v₀ : VT) :=
  BitMachineRawSequence.program (G5fLevelFull.pushP (4 : Fin 16))
    (BitMachineRawSequence.program P tallyP () v₀ none)
    (BitMachineRawSequence.leftLabel l₀) () (v₀, none)

def bodyStart : BitMachineRawSequence.Label Unit
    (BitMachineRawSequence.Label LT Unit) :=
  BitMachineRawSequence.leftLabel ()

def bodyControl (v₀ : VT) := ((), (v₀, (none : Option Bool)))

theorem body_run (P : LT → TM2.Stmt (fun _ : Fin 16 => Bool) LT VT)
    (l₀ : LT) (v₀ : VT) (B : ℕ → ℕ)
    (g : ℕ → Bool) (R : ℕ)
    (hTester : ∀ (S : Fin 16 → List Bool) (j : ℕ),
      S 4 = List.replicate j true →
      S 6 = List.replicate R true → S 12 = [] → scratchEmpty S →
      ∃ u ≤ B j,
        ((advance P)^[u])
          (⟨some l₀, v₀, S⟩ : TM2.Cfg (fun _ : Fin 16 => Bool) LT VT) =
        ⟨none, v₀, Function.update S 12 [g j]⟩)
    (S : Fin 16 → List Bool) (j : ℕ)
    (hj : S 4 = List.replicate j true)
    (hR : S 6 = List.replicate R true) (hO : S 12 = [])
    (hScratch : scratchEmpty S) :
    ∃ u ≤ B (j + 1) + 4,
      ((advance (body P l₀ v₀))^[u])
        (⟨some bodyStart, bodyControl v₀, S⟩ :
          TM2.Cfg (fun _ : Fin 16 => Bool) _ _) =
      ⟨none, bodyControl v₀,
        Function.update (Function.update S 4 (List.replicate (j + 1) true)) 3
          (if g (j + 1) then true :: S 3 else S 3)⟩ := by
  let S1 := Function.update S (4 : Fin 16) (true :: S 4)
  have s1 := G5fLevelFull.push_run (4 : Fin 16) S
  have h4 : S1 4 = List.replicate (j + 1) true := by
    simp [S1, hj, List.replicate_succ]
  have h6 : S1 6 = List.replicate R true := by
    simp [S1, hR]
  have h12 : S1 12 = [] := by
    simp [S1, hO]
  have hScratch1 : scratchEmpty S1 := by
    intro z hz hz12
    have hz4 : z ≠ 4 := by
      intro he
      subst z
      norm_num at hz
    simpa [S1, Function.update_apply, hz4, hz4.symm] using hScratch z hz hz12
  obtain ⟨u2, hu2, s2⟩ := hTester S1 (j + 1) h4 h6 h12 hScratch1
  have s3 := tally_run (Function.update S1 12 [g (j + 1)]) (g (j + 1))
    (Function.update_self _ _ _)
  have hfin : Function.update
      (Function.update (Function.update S1 12 [g (j + 1)]) 12 []) 3
        (if g (j + 1) then
          true :: (Function.update S1 12 [g (j + 1)]) 3
         else (Function.update S1 12 [g (j + 1)]) 3) =
      Function.update (Function.update S 4 (List.replicate (j + 1) true)) 3
        (if g (j + 1) then true :: S 3 else S 3) := by
    have h3 : (Function.update S1 12 [g (j + 1)]) 3 = S 3 := by
      simp [S1]
    rw [h3, Function.update_idem]
    have hc : Function.update S1 12 [] = S1 :=
      Function.update_eq_self_iff.mpr h12.symm
    rw [hc]
    simp only [S1, hj, List.replicate_succ]
  rw [hfin] at s3
  obtain ⟨r2, hr2, q2⟩ := BitMachineRawSequence.runs P tallyP l₀ () v₀ v₀ none none
    S1 (Function.update S1 12 [g (j + 1)]) _ u2 1 s2 s3
  obtain ⟨r1, hr1, q1⟩ := BitMachineRawSequence.runs
    (G5fLevelFull.pushP (4 : Fin 16))
    (BitMachineRawSequence.program P tallyP () v₀ none)
    () (BitMachineRawSequence.leftLabel l₀) () () (v₀, none) (v₀, none)
    S S1 _ 1 r2 s1 q2
  exact ⟨r1, by omega, q1⟩

#print axioms tally_run
#print axioms body_run

end CurrentAdditive.SmallBias.YaoCutScanBody
