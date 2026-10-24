import CurrentAdditive.V39WRawFields

/-! All source fields and the header threshold of the encoded printer are
derived from the actual raw sampler/repetition terminal bank. -/
namespace CurrentAdditive.V39WRaw
noncomputable section
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 16384
open Paper2 EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineStackEmbedding
open V38Schedule V39PublicSchedule V39FullSampleResources

private instance seedNZ (L : Nat) : NeZero (seedWidth L) := ⟨ne_of_gt (full_positive_widths L).1⟩
private instance q1NZ (L : Nat) : NeZero (fullQ₁ L) := ⟨ne_of_gt (full_positive_widths L).2.1⟩
private instance q2NZ (L : Nat) : NeZero (fullQ₂ L) := ⟨ne_of_gt (full_positive_widths L).2.2.1⟩
private instance sNZ (L : Nat) : NeZero (fullS L) := ⟨ne_of_gt (full_positive_widths L).2.2.2.1⟩
private instance fsNZ (L : Nat) : NeZero (4*fullS L) := ⟨ne_of_gt (full_positive_widths L).2.2.2.2.1⟩
private instance smNZ (L : Nat) : NeZero (fullS L-3) := ⟨ne_of_gt (full_positive_widths L).2.2.2.2.2.1⟩
private instance wNZ (L : Nat) : NeZero (fullW L) := ⟨ne_of_gt (full_positive_widths L).2.2.2.2.2.2.1⟩
private instance QNZ (L : Nat) : NeZero (fullQ L) := ⟨ne_of_gt (full_positive_widths L).2.2.2.2.2.2.2⟩

section Fields
variable (g : EncodedGraph.Graph) (K : Nat) [NeZero g.vertices]
variable (cc δv ζ : ℚ) (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)
variable (bits : RoundedDraw.BitBlocks (V22RawSamplerJoin.precision g.vertices K)
  (V22RawSamplerJoin.reservation g.vertices K)) (suffix : List Bool)

def labels :=
  V39PhysicalSample.sampleAtBudget g.vertices (seedWidth (Nat.clog 2 g.vertices))
    (fullQ₁ (Nat.clog 2 g.vertices)) (fullQ₂ (Nat.clog 2 g.vertices)) (fullS (Nat.clog 2 g.vertices))
    (fullW (Nat.clog 2 g.vertices)) (fullQ (Nat.clog 2 g.vertices))
    (by have h := fullS_ge_256 (Nat.clog 2 g.vertices); omega) rfl K
    (sampleSide (Nat.clog 2 g.vertices) K) (V22RawSamplerJoin.reservation g.vertices K)
    (fullDrawCap_le cc (Nat.clog 2 g.vertices) g.edges.length K δv ζ ht) bits

def sources : Fin 14 → List Bool :=
  V39WTablePrepare.sourceWords g (V22RawPublicRepeat.repetitions g) K
    (sampleSide (Nat.clog 2 g.vertices) K)
    (labels g K cc δv ζ ht bits).1 (labels g K cc δv ζ ht bits).2

def afterRaw : Stack → List Bool :=
  initial (V22RawPublicRepeat.final g K cc δv ζ ht bits suffix)

theorem core_field (j : Fin 65) :
    afterRaw g K cc δv ζ ht bits suffix (.inl (core j))=
      CodeRecursiveSeedPrep.publicBase g.vertices (fullS (Nat.clog 2 g.vertices))
        (fullQ₁ (Nat.clog 2 g.vertices)) (fullQ₂ (Nat.clog 2 g.vertices))
        (fullW (Nat.clog 2 g.vertices)) (fullQ (Nat.clog 2 g.vertices))
        (seedWidth (Nat.clog 2 g.vertices)) (List.replicate K true) j := by
  change V22RawPublicRepeat.final g K cc δv ζ ht bits suffix (.inl _)=_
  rw [V22RawPublicRepeat.final_original]
  exact V22RawPublicRepeat.sampler_core g K cc δv ζ ht bits suffix j

theorem shapeCell_field (j : Fin 65) :
    afterRaw g K cc δv ζ ht bits suffix (.inl (shapeCell j))=
      V39PhysicalShapeSample.shapeFinal g.vertices (seedWidth (Nat.clog 2 g.vertices))
        (fullQ₁ (Nat.clog 2 g.vertices)) (fullQ₂ (Nat.clog 2 g.vertices)) (fullS (Nat.clog 2 g.vertices))
        (fullW (Nat.clog 2 g.vertices)) (fullQ (Nat.clog 2 g.vertices)) K j := by
  change V22RawPublicRepeat.final g K cc δv ζ ht bits suffix (.inl _)=_
  rw [V22RawPublicRepeat.final_original,V22RawSamplerJoin.final,bank_at]
  apply V39PhysicalShapeSample.final_shape_retained

theorem source_fields (i : Fin 14) :
    afterRaw g K cc δv ζ ht bits suffix (sourceSlots i)=sources g K cc δv ζ ht bits i := by
  fin_cases i
  · change V22RawPublicRepeat.final g K cc δv ζ ht bits suffix (.inl _)=EncodedGraph.encode g
    rw [V22RawPublicRepeat.final_original,V22RawSamplerJoin.final_graph]
  · exact V22RawPublicRepeat.final_repetition g K cc δv ζ ht bits suffix
  · exact V22RawPublicRepeat.final_edgeCount g K cc δv ζ ht bits suffix
  · simpa only [CodeRecursiveSeedPrep.publicBase,↓reduceIte] using core_field g K cc δv ζ ht bits suffix 63
  · simpa only [CodeRecursiveSeedPrep.publicBase,↓reduceIte] using core_field g K cc δv ζ ht bits suffix 16
  · simpa only [CodeRecursiveSeedPrep.publicBase,↓reduceIte] using core_field g K cc δv ζ ht bits suffix 17
  · simpa only [CodeRecursiveSeedPrep.publicBase,↓reduceIte] using core_field g K cc δv ζ ht bits suffix 31
  · simpa only [CodeRecursiveSeedPrep.publicBase,↓reduceIte] using core_field g K cc δv ζ ht bits suffix 32
  · change V22RawPublicRepeat.final g K cc δv ζ ht bits suffix (.inl _)=List.replicate K true
    rw [V22RawPublicRepeat.final_original,V22RawSamplerJoin.final_k]
  · change V22RawPublicRepeat.final g K cc δv ζ ht bits suffix (.inl _)=_
    rw [V22RawPublicRepeat.final_original,V22RawSamplerJoin.final_constructor]
    change V22FullScheduleBatch.constructorInput g.vertices K (.inr (.inr 0)) = _
    rw [V22FullScheduleBatch.constructor_foreign]
    rfl
  · change afterRaw g K cc δv ζ ht bits suffix (.inl (shapeCell 2)) = _
    rw [shapeCell_field,
      V39PhysicalShapeSample.shapeFinal_row]
    rfl
  · change afterRaw g K cc δv ζ ht bits suffix (.inl (shapeCell 33)) = _
    rw [shapeCell_field,
      V39PhysicalShapeSample.shapeFinal_column]
    rfl
  · change V22RawPublicRepeat.final g K cc δv ζ ht bits suffix (.inl _)=_
    rw [V22RawPublicRepeat.final_original,V22RawSamplerJoin.final_output]
    exact V39WEntry.sampleWord_writer_layout g K _ (labels g K cc δv ζ ht bits).1
      (labels g K cc δv ζ ht bits).2
  · rfl

theorem threshold_field :
    afterRaw g K cc δv ζ ht bits suffix (.inl rawThreshold)=
      List.replicate (B (Nat.clog 2 g.vertices) K) true := by
  change V22RawPublicRepeat.final g K cc δv ζ ht bits suffix (.inl _)=_
  rw [V22RawPublicRepeat.final_original]
  exact V22RawSamplerJoin.final_threshold _ _ _ _ _ _ _ _ _ _

theorem printer_ready (j : V39WEncodedTable.Stack) :
    afterRaw g K cc δv ζ ht bits suffix (printerSlots j)=
      V39WEncodedTable.initial (sources g K cc δv ζ ht bits) (B (Nat.clog 2 g.vertices) K) j := by
  rcases j with i | ((w | (h | f)) | p)
  · exact source_fields g K cc δv ζ ht bits suffix i
  · rfl
  · rfl
  · fin_cases f
    · exact threshold_field g K cc δv ζ ht bits suffix
    · rfl
  · fin_cases p; rfl

end Fields
#print axioms source_fields
#print axioms threshold_field
#print axioms printer_ready
end
end CurrentAdditive.V39WRaw
