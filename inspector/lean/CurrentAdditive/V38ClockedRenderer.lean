import CurrentAdditive.V38RendererMachine
import CurrentAdditive.GeneralPolynomialClockBound

/-! A uniform clock on every bit word, agreeing with the physical renderer
on every valid source code. The source-compiler composition below uses only
this established renderer and a polynomial source-code compiler. -/

noncomputable section
namespace CurrentAdditive.V38PhysicalRenderer

open EthInapproximability.CurrentPaper
open BitMachineComposition EncodedCommunication
open Paper2.YaoSourceCodec Paper2.YaoClockPoly
open CurrentAdditive.V39SourceAddressResource

private theorem nat_le_two_pow (c : ℕ) : c ≤ 2^c := by
  induction c with
  | zero => simp
  | succ c ih =>
    have hp : 1 ≤ 2^c := Nat.one_le_pow _ _ (by decide)
    calc c+1 ≤ 2^c+2^c := by omega
      _ = 2^(c+1) := by rw [pow_succ]; omega

private theorem budget_le_fuel (c k n : ℕ) :
    c*(n+1)^k ≤ (n+2)^(c+k+1) := by
  have hc : c ≤ (n+2)^c :=
    (nat_le_two_pow c).trans (Nat.pow_le_pow_left (by omega : 2≤n+2) c)
  have hk : (n+1)^k ≤ (n+2)^k := Nat.pow_le_pow_left (by omega) k
  calc c*(n+1)^k ≤ (n+2)^c*(n+2)^k := Nat.mul_le_mul hc hk
    _ = (n+2)^(c+k) := by rw [pow_add]
    _ ≤ (n+2)^(c+k+1) := Nat.pow_le_pow_right (by omega) (by omega)

/-- One fixed total polynomial-time function for fixed t. Its correctness
on source codes is proved by the literal source-to-table physical program;
malformed bit words also terminate within the uniform polynomial clock. -/
theorem clocked_polytime (t : ℕ) (ht : 4 ≤ t) :
    ∃ f : List Bool → List Bool, BitMachine.Polytime f ∧
      ∀ x : YaoSource t, f (encode x) = word x := by
  obtain ⟨c,k,hclock⟩ := clock_poly t ht
  let degree := c+k
  let M := machine t
  let f := GeneralPolynomialClock.result degree M
  refine ⟨f,GeneralPolynomialClock.polytime degree M,?_⟩
  intro x
  have hrun := outputs t ht x
  have hbudget : clock x ≤
      GeneralPolynomialFuelPrefix.clockLength (degree:=degree) (encode x) := by
    calc clock x ≤ c*((encode x).length+1)^k := hclock x
      _ ≤ ((encode x).length+2)^(c+k+1) := budget_le_fuel c k (encode x).length
      _ = _ := rfl
  have hvalid := GeneralPolynomialClock.outputs_valid degree M (encode x) (word x)
    (BitMachine.outputsWithin_mono M hrun hbudget)
  have hall := GeneralPolynomialClock.outputs_all degree M (encode x)
  exact BitMachine.outputsWithin_unique (GeneralPolynomialClock.machine degree M) hall hvalid

theorem word_eq_sourceInstance {t : ℕ} (x : YaoSource t) :
    word x = encodeInstance (V39SourceRenderer.sourceInstance x) := by
  simp only [word,V39SourceRenderer.sourceInstance,V39SourceRenderer.selectedModulus,
    V38ReadyScalars.b,V38ReadyScalars.d,edgeBits_eq_paddedEdgeBits]

/-- Any already-constructed polynomial source compiler may be followed by
the actual selected renderer. No table-printer runtime is a premise. -/
theorem source_map_polytime {t : ℕ} (ht : 4 ≤ t)
    (F : List Bool → YaoSource t)
    (hsource : BitMachine.Polytime (fun input => encode (F input))) :
    BitMachine.Polytime (fun input => encodeInstance (V39SourceRenderer.sourceInstance (F input))) := by
  obtain ⟨f,hf,hagree⟩ := clocked_polytime t ht
  have hp := BitMachineComposition.polytime_comp hsource hf
  have heq : (f ∘ (fun input => encode (F input))) =
      (fun input => encodeInstance (V39SourceRenderer.sourceInstance (F input))) := by
    funext input
    exact (hagree (F input)).trans (word_eq_sourceInstance _)
  rw [heq] at hp
  exact hp

theorem selected_encoded_instance_polytime {t : ℕ} (ht : 4 ≤ t)
    (G : V38Source.GLSourceInput t) :
    BitMachine.Polytime (fun input => encodeInstance
      (V39SourceRenderer.sourceInstance (V38Source.selectedSource G input))) :=
  source_map_polytime ht (V38Source.selectedSource G) (V38Machine.source_polytime G)

#print axioms clocked_polytime
#print axioms word_eq_sourceInstance
#print axioms source_map_polytime
#print axioms selected_encoded_instance_polytime
end CurrentAdditive.V38PhysicalRenderer
