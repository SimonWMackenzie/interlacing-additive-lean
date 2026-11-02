import CurrentAdditive.V42GraphRuntime

namespace CurrentAdditive.V42GraphRuntime
open Paper2 EthInapproximability.CurrentPaper V42Schedule
noncomputable section
set_option maxHeartbeats 8000000

theorem base_le_dyadic (Δ k₀ : ℕ) (g : EncodedGraph.Graph) (hg : g.Valid)
    (hk₀ : 2≤k₀) (hdegree : 2*g.edges.length≤Δ*g.vertices) :
    V42RuntimePrefix.base k₀ g ≤ (8*Δ+6)*(V42RuntimePrefix.N k₀ g)^2 := by
  let N:=V42RuntimePrefix.N k₀ g
  have hk:=selected_ge_two k₀ hk₀ g
  have hN : 2≤N := by
    have h:=Nat.pow_le_pow_right (by decide : 1≤2) (show 1≤4*V42RuntimePrefix.selected k₀ g by omega)
    simpa only [pow_one] using h
  have hn : g.vertices≤N := by
    simpa only [V42PublicSchedule.generatedN_exact] using
      (V42PublicCutoff.generatedExponent_spec g.vertices k₀).2
  have hm : g.edges.length≤Δ*N := by have h:=Nat.mul_le_mul_left Δ hn;omega
  have ht : g.edges.length*(4*g.vertices+4)≤(Δ*N)*(8*N) :=
    Nat.mul_le_mul hm (by omega)
  have hbytes:=EncodedGraph.encode_length_upper g hg
  change N+(EncodedGraph.encode g).length+2≤(8*Δ+6)*N^2
  nlinarith

def dyadicExponent (Δ k₀ : ℕ) (T : BitMachine.Machine) (ct dt : ℕ) :=
  ((8*Δ+6+2)*exponent k₀ T ct dt+1040)

theorem dyadic_outputs_with_tail (Δ k₀ : ℕ) (T : BitMachine.Machine) (ct dt : ℕ)
    (g : EncodedGraph.Graph) (hg : g.Valid) (K : ℕ) (hk₀ : 2≤k₀) (hn : 0<g.vertices)
    (hdegree : 2*g.edges.length≤Δ*g.vertices) (hcut : 2*Δ≤k₀)
    (Y : List Bool)
    (hT : T.OutputsWithin
      (V42RuntimeWords.word g hg (V42RuntimePrefix.selected k₀ g) K (selected_ge_two k₀ hk₀ g) hn
        (selected_width Δ k₀ g hdegree hcut) K) Y
      (ct*((V42RuntimeWords.word g hg (V42RuntimePrefix.selected k₀ g) K (selected_ge_two k₀ hk₀ g) hn
        (selected_width Δ k₀ g hdegree hcut) K).length+1)^dt)) :
    (pipeline k₀ T).OutputsWithin (V42RuntimePrefix.input (EncodedGraph.encode g) K) Y
      ((V42RuntimePrefix.N k₀ g)^(dyadicExponent Δ k₀ T ct dt*(amplification k₀)^K)) ∧
    Y.length≤(V42RuntimePrefix.N k₀ g)^(dyadicExponent Δ k₀ T ct dt*(amplification k₀)^K) := by
  have h:=outputs_with_tail k₀ T ct dt g hg K (selected_ge_two k₀ hk₀ g) hn
    (selected_width Δ k₀ g hdegree hcut) Y hT
  have hN : 2≤V42RuntimePrefix.N k₀ g := by
    have hk:=selected_ge_two k₀ hk₀ g
    change 2^1≤2^(4*V42RuntimePrefix.selected k₀ g)
    exact Nat.pow_le_pow_right (by decide : 0<2) (by omega)
  have hb:=V40GraphConstructorInputBounds.dyadic_clock_bound
    (V42RuntimePrefix.base k₀ g) (V42RuntimePrefix.N k₀ g) _ (8*Δ+6)
    (exponent k₀ T ct dt) (amplification k₀) K hN (base_le_dyadic Δ k₀ g hg hk₀ hdegree) h.2
  have ht:=V40GraphConstructorInputBounds.dyadic_clock_bound
    (V42RuntimePrefix.base k₀ g) (V42RuntimePrefix.N k₀ g)
    ((V42RuntimePrefix.base k₀ g)^(exponent k₀ T ct dt*(amplification k₀)^K)) (8*Δ+6)
    (exponent k₀ T ct dt) (amplification k₀) K hN (base_le_dyadic Δ k₀ g hg hk₀ hdegree) le_rfl
  exact ⟨BitMachine.outputsWithin_mono _ h.1 ht,hb⟩

#print axioms base_le_dyadic
#print axioms dyadic_outputs_with_tail
end
end CurrentAdditive.V42GraphRuntime
