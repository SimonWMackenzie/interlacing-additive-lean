import CurrentAdditive.V40PhysicalEstimatorConsumer
import Paper2.E4Law

set_option autoImplicit false

/-! The physical reservoir has N consecutive blocks, each of b bits. Its
literal concatenation is a bijection onto b*N fair bits, in the actual machine
order. The all-event identities also retain an independent suffix tape. -/

namespace CurrentAdditive.V40BlockTapeLaw
noncomputable section
open Paper2 Paper2.FiniteLaw
open Paper2.Unit4Shell.Definitions (uniformTape)
open EthInapproximability.CurrentPaper
open RoundedDraw RoundedCodeLoop
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768

theorem tapeWord_injective (b N : ℕ) : Function.Injective (tapeWord b N) := by
  induction N with
  | zero => intro a c _; cases a; cases c; rfl
  | succ N ih =>
    intro a c h
    rcases a with ⟨a,as⟩
    rcases c with ⟨c,cs⟩
    change Paper2.CappedTicketMachine.ticketWord a ++ tapeWord b N as =
      Paper2.CappedTicketMachine.ticketWord c ++ tapeWord b N cs at h
    obtain ⟨h₁,h₂⟩:=List.append_inj h (by simp [Paper2.CappedTicketMachine.ticketWord])
    have hhead : a=c:=List.ofFn_injective h₁
    have htail : as=cs:=ih h₂
    cases hhead
    cases htail
    rfl

def flatten (b N : ℕ) (bits : BitBlocks b N) : Fin (b*N) → Bool :=
  fun i => (tapeWord b N bits)[i.val]'(by rw [tapeWord_length]; exact i.isLt)

theorem ofFn_flatten (b N : ℕ) (bits : BitBlocks b N) :
    List.ofFn (flatten b N bits)=tapeWord b N bits := by
  apply List.ext_getElem
  · simp [tapeWord_length]
  · intro i hi hj
    simp only [List.getElem_ofFn,flatten]

theorem flatten_injective (b N : ℕ) : Function.Injective (flatten b N) := by
  intro a c h
  apply tapeWord_injective b N
  rw [←ofFn_flatten b N a,←ofFn_flatten b N c,h]

theorem blocks_card (b N : ℕ) : Fintype.card (BitBlocks b N)=2^(b*N) := by
  induction N with
  | zero => simp [BitBlocks]
  | succ N ih =>
    change Fintype.card ((Fin b → Bool) × BitBlocks b N)=_
    rw [Fintype.card_prod,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,ih]
    rw [Nat.mul_succ,pow_add]
    ring

def blocksEquiv (b N : ℕ) : BitBlocks b N ≃ (Fin (b*N) → Bool) :=
  Equiv.ofBijective (flatten b N)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨flatten_injective b N,by simp [blocks_card]⟩)

theorem blocksEquiv_ofFn (b N : ℕ) (bits : BitBlocks b N) :
    List.ofFn (blocksEquiv b N bits)=tapeWord b N bits := ofFn_flatten b N bits

theorem blocksEquiv_symm_word (b N : ℕ) (t : Fin (b*N) → Bool) :
    tapeWord b N ((blocksEquiv b N).symm t)=List.ofFn t := by
  rw [←blocksEquiv_ofFn,(blocksEquiv b N).apply_symm_apply]

theorem bitBlocks_weight (b N : ℕ) (bits : BitBlocks b N) :
    (bitBlocksLaw b N).weight bits=(1/2:ℝ)^(b*N) := by
  induction N with
  | zero => simp [bitBlocksLaw]
  | succ N ih =>
    change (Paper2.CappedSampler.fairBits b).weight bits.1 *
      (bitBlocksLaw b N).weight bits.2=_
    rw [Paper2.CappedSampler.fairBits_weight,ih]
    simp only [Nat.mul_succ,pow_add,one_div,inv_pow]
    ring

theorem blocks_probability (b N : ℕ) (E : (Fin (b*N) → Bool) → Prop) :
    (bitBlocksLaw b N).prob (fun bits => E (blocksEquiv b N bits))=
      (uniformTape (b*N)).prob E := by
  apply AModel.prob_equiv
  intro bits
  rw [AModel.uniformTape_weight,bitBlocks_weight]

/-- Every event of all reserved block bits has the exact uniform tape law. -/
theorem uniform_blocks_probability (b N : ℕ) (E : BitBlocks b N → Prop) :
    (uniformTape (b*N)).prob (fun t => E ((blocksEquiv b N).symm t))=
      (bitBlocksLaw b N).prob E := by
  rw [←blocks_probability b N]
  simp only [Equiv.symm_apply_apply]

theorem tapeWord_probability (b N : ℕ) (E : List Bool → Prop) :
    (bitBlocksLaw b N).prob (fun bits => E (tapeWord b N bits))=
      (uniformTape (b*N)).prob (fun t => E (List.ofFn t)) := by
  have h:=blocks_probability b N (fun t => E (List.ofFn t))
  simpa only [blocksEquiv_ofFn] using h

theorem product_tapeWord_probability {α : Type*} [Fintype α] (b N : ℕ)
    (ν : FiniteLaw α) (E : List Bool → α → Prop) :
    ((bitBlocksLaw b N).prod ν).prob (fun z => E (tapeWord b N z.1) z.2)=
      ((uniformTape (b*N)).prod ν).prob (fun z => E (List.ofFn z.1) z.2) := by
  have h:=AModel.prob_equiv ((bitBlocksLaw b N).prod ν)
    ((uniformTape (b*N)).prod ν) (Equiv.prodCongr (blocksEquiv b N) (Equiv.refl α))
    (by intro z; simp only [FiniteLaw.prod,Equiv.prodCongr_apply,Prod.map,
      Equiv.refl_apply,
      AModel.uniformTape_weight,bitBlocks_weight])
    (fun z => E (List.ofFn z.1) z.2)
  simpa only [Equiv.prodCongr_apply,Prod.map,Equiv.refl_apply,blocksEquiv_ofFn] using h

/-- Literal prefix/suffix order, retaining all unused suffix bits. -/
theorem uniform_prefix_suffix (b N s : ℕ) (E : List Bool → List Bool → Prop) :
    (uniformTape (b*N+s)).prob
      (fun t => E ((List.ofFn t).take (b*N)) ((List.ofFn t).drop (b*N)))=
      ((bitBlocksLaw b N).prod (uniformTape s)).prob
        (fun z => E (tapeWord b N z.1) (List.ofFn z.2)) := by
  rw [AModel.uniformTape_take_drop_prob]
  exact (product_tapeWord_probability b N (uniformTape s)
    (fun a t => E a (List.ofFn t))).symm

/-- A larger carrier may contain a gap and an unused suffix. Only the first
b*N bits and the classifier segment beginning at L are observed. -/
theorem uniform_twoCut {b N L s R : ℕ} (hfirst : b*N≤L) (hsecond : L+s≤R)
    (E : List Bool → List Bool → Prop) :
    (uniformTape R).prob (fun t => E ((List.ofFn t).take (b*N))
      (((List.ofFn t).drop L).take s))=
      ((bitBlocksLaw b N).prod (uniformTape s)).prob
        (fun z => E (tapeWord b N z.1) (List.ofFn z.2)) := by
  rw [Paper2.AEth4.uniform_split_take_prob hfirst hsecond]
  exact (product_tapeWord_probability b N (uniformTape s)
    (fun a t => E a (List.ofFn t))).symm

#print axioms blocksEquiv
#print axioms uniform_blocks_probability
#print axioms tapeWord_probability
#print axioms uniform_prefix_suffix
#print axioms uniform_twoCut
end
end CurrentAdditive.V40BlockTapeLaw
