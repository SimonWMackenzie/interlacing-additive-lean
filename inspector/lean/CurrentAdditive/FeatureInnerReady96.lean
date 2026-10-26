import CurrentAdditive.FeatureInnerPrep96

/-! The five physically copied words are exactly the real inner scanner's
initial bank. This discharges the preparation equality rather than supplying
the desired feature packet as an assumed callback result. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace CurrentAdditive.FeatureInnerReady96
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.FeatureBoundedLift96
open CurrentAdditive.FeatureBoundedAlphabet64
open CurrentAdditive.FeatureInnerAlphabetRun64
open CurrentAdditive.Wide64ContextListScheduler

def values (j : Nat) (c : List (Nat × Nat)) (ys : List Nat)
    (body : List Bool) : Fin 5 → List Bool :=
  ![SourceListEncoding.encode (labelWords ys),body,j.bits,
    List.replicate ys.length true,CylinderFeatureCodec.encodeFeature c]

def innerBank (j : Nat) (c : List (Nat × Nat)) (ys : List Nat)
    (body : List Bool) : Fin 64 → List Bool :=
  fun k => if k=8 then SourceListEncoding.encode (labelWords ys)
    else if k=9 then body else if k=12 then j.bits
    else if k=13 then List.replicate ys.length true
    else if k=15 then CylinderFeatureCodec.encodeFeature c else []

theorem initial_bank (j : Nat) (c : List (Nat × Nat)) (ys : List Nat)
    (body : List Bool) :
    (innerStart j c ys body).stk = innerBank j c ys body := by
  funext k
  change (Wide64ContextPreservingScan.frame
    (foreignBank body j.bits (original ys).length (extra c))
    (CylinderContextScanStep.initial
      (SourceListEncoding.encode (original ys)) 0)).stk k = _
  by_cases hi : ∃ i : Fin 12, Wide64ContextPreservingScan.locate i = k
  · obtain ⟨i,rfl⟩ := hi
    rw [Wide64ContextPreservingScan.frame_bank]
    fin_cases i <;>
      simp [CylinderContextScanStep.initial,CylinderContextScanStep.initialBank,
        Wide64ContextPreservingScan.locate,innerBank,original]
  · rw [Wide64ContextPreservingScan.frame_foreign _ _ k hi]
    have h8 : k ≠ 8 := by
      intro he
      exact hi ⟨8,by simpa [Wide64ContextPreservingScan.locate] using he.symm⟩
    by_cases h9 : k=9 <;> by_cases h12 : k=12 <;> by_cases h13 : k=13 <;>
      simp_all [foreignBank,FeatureInnerAlphabetRun64.extra,innerBank,
        Function.update_apply,original,labelWords]

theorem copied_bank (S : Fin 96 → List Bool) (j : Nat)
    (c : List (Nat × Nat)) (ys : List Nat) (body : List Bool)
    (hhigh : ∀ k : Fin 96, 32 ≤ k.val → S k = []) :
    FeatureInnerPrep96.after S (values j c ys body) =
      (liftedStart S j c ys body).stk := by
  funext k
  change FeatureInnerPrep96.after S (values j c ys body) k =
    BitMachineStackEmbedding.bank slot S (innerStart j c ys body).stk k
  rw [initial_bank]
  by_cases hi : ∃ i : Fin 64, slot i = k
  · obtain ⟨i,rfl⟩ := hi
    rw [BitMachineStackEmbedding.bank_at]
    by_cases h8 : i=8
    · subst i; simp [FeatureInnerPrep96.after,values,slot,innerBank]
    by_cases h9 : i=9
    · subst i; simp [FeatureInnerPrep96.after,values,slot,innerBank]
    by_cases h12 : i=12
    · subst i; simp [FeatureInnerPrep96.after,values,slot,innerBank]
    by_cases h13 : i=13
    · subst i; simp [FeatureInnerPrep96.after,values,slot,innerBank]
    by_cases h15 : i=15
    · subst i; simp [FeatureInnerPrep96.after,values,slot,innerBank]
    have hn (n : Nat) (hi : i.val ≠ n) : (32+i.val : Nat) ≠ 32+n := by omega
    have h40 : slot i ≠ 40 := by intro he; have hv:=congrArg Fin.val he; simp [slot] at hv; apply h8; apply Fin.ext; omega
    have h41 : slot i ≠ 41 := by intro he; have hv:=congrArg Fin.val he; simp [slot] at hv; apply h9; apply Fin.ext; omega
    have h44 : slot i ≠ 44 := by intro he; have hv:=congrArg Fin.val he; simp [slot] at hv; apply h12; apply Fin.ext; omega
    have h45 : slot i ≠ 45 := by intro he; have hv:=congrArg Fin.val he; simp [slot] at hv; apply h13; apply Fin.ext; omega
    have h47 : slot i ≠ 47 := by intro he; have hv:=congrArg Fin.val he; simp [slot] at hv; apply h15; apply Fin.ext; omega
    simp only [FeatureInnerPrep96.after,Function.update_of_ne h47,
      Function.update_of_ne h45,Function.update_of_ne h44,
      Function.update_of_ne h41,Function.update_of_ne h40]
    rw [hhigh (slot i) (by simp [slot])]
    simp [innerBank,h8,h9,h12,h13,h15]
  · rw [BitMachineStackEmbedding.bank_outside _ _ _ k hi]
    have h40 : k ≠ 40 := by intro he; exact hi ⟨8,by simpa [slot] using he.symm⟩
    have h41 : k ≠ 41 := by intro he; exact hi ⟨9,by simpa [slot] using he.symm⟩
    have h44 : k ≠ 44 := by intro he; exact hi ⟨12,by simpa [slot] using he.symm⟩
    have h45 : k ≠ 45 := by intro he; exact hi ⟨13,by simpa [slot] using he.symm⟩
    have h47 : k ≠ 47 := by intro he; exact hi ⟨15,by simpa [slot] using he.symm⟩
    simp [FeatureInnerPrep96.after,h40,h41,h44,h45,h47]

def innerControl := (innerStart 0 [] [] []).var

theorem start_fixed (S : Fin 96 → List Bool) (j : Nat)
    (c : List (Nat × Nat)) (ys : List Nat) (body : List Bool)
    (hhigh : ∀ k : Fin 96, 32 ≤ k.val → S k = []) :
    liftedStart S j c ys body =
      ⟨some (.inr (.inr .check)),innerControl,
        FeatureInnerPrep96.after S (values j c ys body)⟩ := by
  have hb := copied_bank S j c ys body hhigh
  unfold liftedStart BitMachineStackEmbedding.cfg
    BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  congr 1
  exact hb.symm

#print axioms initial_bank
#print axioms copied_bank
#print axioms start_fixed
end CurrentAdditive.FeatureInnerReady96
