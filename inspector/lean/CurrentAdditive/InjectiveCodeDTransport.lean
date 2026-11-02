import CurrentAdditive.OrderedAlphabetCodec

/-! The materialized Code D constructor commutes with injective relabelling.
All array positions, duplicate occurrences, rational feature rows, and the
deterministic Gauss branch are kept literally in the same order. -/

namespace CurrentAdditive.InjectiveCodeDTransport

open CurrentAdditive.SequentialCode CurrentAdditive.SequentialSourceCode

variable {Y Z : Type} [DecidableEq Y] [DecidableEq Z]
  (e : Y → Z) (he : Function.Injective e)

def mapEntry (x : Y × ℚ) : Z × ℚ := (e x.1, x.2)

def mapWord {q : Nat} (v : Fin q → Y) : Fin q → Z := e ∘ v

def mapSource {q : Nat} (s : Array ((Fin q → Y) × ℚ)) :
    Array ((Fin q → Z) × ℚ) :=
  s.map (fun x => (mapWord e x.1, x.2))

def mapFeature (c : List (Nat × Y)) : List (Nat × Z) :=
  c.map (fun p => (p.1, e p.2))

theorem mapFeature_length (c : List (Nat × Y)) :
    (mapFeature e c).length = c.length := by simp [mapFeature]

theorem generatedFeatureValue_map (he : Function.Injective e) {q : Nat} (v : Fin q → Y)
    (c : List (Nat × Y)) :
    generatedFeatureValue (mapWord e v) (mapFeature e c) =
      generatedFeatureValue v c := by
  have heq (a b : Y) : e a = e b ↔ a = b :=
    ⟨fun h => he h, fun h => congrArg e h⟩
  have hall :
      (mapFeature e c).all (fun p =>
        if h : p.1 < q then decide ((mapWord e v) ⟨p.1, h⟩ = p.2) else false) =
      c.all (fun p =>
        if h : p.1 < q then decide (v ⟨p.1, h⟩ = p.2) else false) := by
    simp only [mapFeature, List.all_map]
    apply List.all_congr rfl
    intro p
    rcases p with ⟨k, y⟩
    by_cases hk : k < q
    · simp [hk, mapWord, heq]
    · simp [hk]
  unfold generatedFeatureValue
  rw [hall]

theorem appendWord_map {q : Nat} (v : Fin q → Y) (y : Y) :
    mapWord e (appendWord v y) = appendWord (mapWord e v) (e y) := by
  funext j
  simp only [mapWord, Function.comp_apply, appendWord]
  split_ifs <;> rfl

theorem appendSource_map {q : Nat}
    (source : Array ((Fin q → Y) × ℚ))
    (alphabet : Array (Y × ℚ)) :
    appendSource (mapSource e source) (alphabet.map (mapEntry e)) =
      mapSource e (appendSource source alphabet) := by
  unfold appendSource mapSource
  simp only [Array.foldl_map]
  have hfold (l : List ((Fin q → Y) × ℚ))
      (acc : Array ((Fin (q + 1) → Y) × ℚ)) :
      (l.foldl (fun out x =>
        out ++ alphabet.map (fun y => (appendWord x.1 y.1, x.2 * y.2))) acc).map
        (fun x => (mapWord e x.1, x.2)) =
      l.foldl (fun out x =>
        out ++ (alphabet.map (mapEntry e)).map
          (fun y => (appendWord (mapWord e x.1) y.1, x.2 * y.2)))
        (acc.map (fun x => (mapWord e x.1, x.2))) := by
    induction l generalizing acc with
    | nil => rfl
    | cons x xs ih =>
        simp only [List.foldl_cons]
        rw [ih]
        congr 1
        simp [Array.map_append, Array.map_map, mapEntry, appendWord_map,
          Function.comp_def]
  simpa only [← Array.foldl_toList, Array.toList_map, List.foldl_map,
    Array.map_empty]
    using (hfold source.toList #[]).symm

theorem extendFeatures_map (D j : Nat) (alphabet : Array Y)
    (features : Array (List (Nat × Y))) :
    extendFeatures D (alphabet.map e) j (features.map (mapFeature e)) =
      (extendFeatures D alphabet j features).map (mapFeature e) := by
  have hfilter :
      (features.map (mapFeature e)).filter (fun c => decide (c.length < D)) =
        (features.filter (fun c => decide (c.length < D))).map (mapFeature e) := by
    rw [Array.filter_map]
    simp [Function.comp_def, mapFeature_length]
  have hstep (acc : Array (List (Nat × Y))) (c : List (Nat × Y)) :
      acc.map (mapFeature e) ++
          (alphabet.map e).map (fun y => (j, y) :: mapFeature e c) =
        (acc ++ alphabet.map (fun y => (j, y) :: c)).map (mapFeature e) := by
    simp [Array.map_append, Array.map_map, mapFeature, Function.comp_def]
  unfold extendFeatures
  rw [hfilter, Array.map_append]
  simp only [Array.foldl_map]
  have hfold := Array.foldl_hom (f := fun a : Array (List (Nat × Y)) =>
      a.map (mapFeature e))
    (xs := features.filter (fun c => decide (c.length < D)))
    (init := (#[] : Array (List (Nat × Y))))
    (g₁ := fun out c => out ++ alphabet.map (fun y => (j, y) :: c))
    (g₂ := fun out c => out ++ (alphabet.map e).map
      (fun y => (j, y) :: mapFeature e c))
    (fun acc c => hstep acc c)
  simpa only [Array.foldl_map, Array.map_empty] using
    congrArg (fun a => features.map (mapFeature e) ++ a) hfold

theorem generatedFeatures_map (q D : Nat) (alphabet : Array Y) :
    generatedFeatures q D (alphabet.map e) =
      (generatedFeatures q D alphabet).map (mapFeature e) := by
  unfold generatedFeatures
  have hfold := List.foldl_hom
    (f := fun a : Array (List (Nat × Y)) => a.map (mapFeature e))
    (l := List.range q) (init := (#[[]] : Array (List (Nat × Y))))
    (g₁ := fun current j => extendFeatures D alphabet j current)
    (g₂ := fun current j => extendFeatures D (alphabet.map e) j current)
    (fun current j => extendFeatures_map e D j alphabet current)
  simpa [mapFeature] using hfold

theorem featureRows_map {q n : Nat}
    (φY : (Fin q → Y) → Fin n → ℚ)
    (φZ : (Fin q → Z) → Fin n → ℚ)
    (hφ : ∀ v j, φZ (mapWord e v) j = φY v j)
    (source : Array ((Fin q → Y) × ℚ)) :
    featureRows n φZ (mapSource e source) = featureRows n φY source := by
  simp [featureRows, mapSource, Array.map_map, Function.comp_def, hφ]

theorem sourceMass_map {q : Nat}
    (source : Array ((Fin q → Y) × ℚ)) :
    sourceMass (mapSource e source) = sourceMass source := by
  simp [sourceMass, mapSource, List.map_map, Function.comp_def]

theorem sourceMoment_map {q n : Nat}
    (φY : (Fin q → Y) → Fin n → ℚ)
    (φZ : (Fin q → Z) → Fin n → ℚ)
    (hφ : ∀ v j, φZ (mapWord e v) j = φY v j)
    (source : Array ((Fin q → Y) × ℚ)) (j : Fin n) :
    sourceMoment φZ (mapSource e source) j = sourceMoment φY source j := by
  simp [sourceMoment, mapSource, List.map_map, Function.comp_def, hφ]

theorem sourceMomentsCheck_map {q n : Nat}
    (φY : (Fin q → Y) → Fin n → ℚ)
    (φZ : (Fin q → Z) → Fin n → ℚ)
    (hφ : ∀ v j, φZ (mapWord e v) j = φY v j)
    (before after : Array ((Fin q → Y) × ℚ)) :
    sourceMomentsCheck n φZ (mapSource e before) (mapSource e after) =
      sourceMomentsCheck n φY before after := by
  simp [sourceMomentsCheck, sourceMass_map,
    sourceMoment_map e φY φZ hφ]

theorem selected_map {q : Nat}
    (source : Array ((Fin q → Y) × ℚ)) (updated : Array ℚ)
    (indices : List Nat) :
    (indices.filterMap (fun i =>
      ((mapSource e source)[i]?).map (fun entry =>
        (entry.1, updated[i]?.getD 0)))).toArray =
    mapSource e ((indices.filterMap (fun i =>
      (source[i]?).map (fun entry =>
        (entry.1, updated[i]?.getD 0)))).toArray) := by
  apply Array.toList_inj.mp
  simp only [mapSource, Array.toList_map, List.map_filterMap]
  congr 1
  funext i
  rw [Array.getElem?_map]
  simp [Option.map_map, mapWord, Function.comp_def]

theorem compressSourceOnceMaterialized_map {q n : Nat}
    (φY : (Fin q → Y) → Fin n → ℚ)
    (φZ : (Fin q → Z) → Fin n → ℚ)
    (hφ : ∀ v j, φZ (mapWord e v) j = φY v j)
    (source : Array ((Fin q → Y) × ℚ)) :
    compressSourceOnceMaterialized n φZ (mapSource e source) =
      (compressSourceOnceMaterialized n φY source).map (mapSource e) := by
  have hm : featureRows n φZ (mapSource e source) =
      featureRows n φY source := featureRows_map e φY φZ hφ source
  have hw : (mapSource e source).map Prod.snd = source.map Prod.snd := by
    simp [mapSource, Array.map_map, Function.comp_def]
  unfold compressSourceOnceMaterialized
  rw [hm]
  simp only [hw, Array.size_map]
  have hs : (mapSource e source).size = source.size := by simp [mapSource]
  rw [hs]
  cases hcert : MaterializedGauss.certifiedMaterializedDependence
      (featureRows n φY source) with
  | none => simp [hcert]
  | some cert =>
      cases hupdate : eliminateWeights (source.map Prod.snd) cert.val with
      | none => simp [hcert, hupdate]
      | some updated =>
          have hout := selected_map e source updated (positiveIndices updated)
          simp only [hcert, hupdate]
          rw [hout]
          simp only [sourceMomentsCheck_map e φY φZ hφ]
          split_ifs <;> simp

theorem compressSourceFuelMaterialized_map {q n : Nat}
    (φY : (Fin q → Y) → Fin n → ℚ)
    (φZ : (Fin q → Z) → Fin n → ℚ)
    (hφ : ∀ v j, φZ (mapWord e v) j = φY v j)
    (source : Array ((Fin q → Y) × ℚ)) (fuel : Nat) :
    compressSourceFuelMaterialized n φZ (mapSource e source) fuel =
      (compressSourceFuelMaterialized n φY source fuel).map (mapSource e) := by
  induction fuel generalizing source with
  | zero =>
      simp only [compressSourceFuelMaterialized]
      have hs : (mapSource e source).size = source.size := by simp [mapSource]
      rw [hs]
      split_ifs <;> simp
  | succ fuel ih =>
      simp only [compressSourceFuelMaterialized]
      have hs : (mapSource e source).size = source.size := by simp [mapSource]
      rw [hs]
      by_cases hsize : source.size ≤ n
      · simp [hsize]
      · simp only [if_neg hsize]
        rw [compressSourceOnceMaterialized_map e φY φZ hφ]
        cases hstep : compressSourceOnceMaterialized n φY source with
        | none => simp [hstep]
        | some next =>
            simp only [hstep, Option.map_some, Option.bind_some]
            exact ih next

theorem generatedStep_map (he : Function.Injective e) {q : Nat}
    (featuresY : Array (List (Nat × Y)))
    (featuresZ : Array (List (Nat × Z)))
    (hfeatures : featuresZ = featuresY.map (mapFeature e))
    (source : Array ((Fin q → Y) × ℚ)) :
    compressSourceFuelMaterialized featuresZ.size
      (fun v j => generatedFeatureValue v featuresZ[j])
      (mapSource e source) (mapSource e source).size =
    (compressSourceFuelMaterialized featuresY.size
      (fun v j => generatedFeatureValue v featuresY[j])
      source source.size).map (mapSource e) := by
  subst featuresZ
  have hs : (mapSource e source).size = source.size := by simp [mapSource]
  have hφ (v : Fin q → Y) (j : Fin featuresY.size) :
      generatedFeatureValue (mapWord e v)
        (featuresY.map (mapFeature e))[j] =
      generatedFeatureValue v featuresY[j] := by
    simpa using generatedFeatureValue_map e he v featuresY[j]
  have hmap := compressSourceFuelMaterialized_map e
    (fun v j => generatedFeatureValue v featuresY[j])
    (fun v j => generatedFeatureValue v
      (featuresY.map (mapFeature e))[j]) hφ source source.size
  have hsize : (featuresY.map (mapFeature e)).size = featuresY.size := by
    simp
  convert hmap using 1
  · congr 1
    refine Function.hfunext rfl ?_
    intro v v' hv
    cases hv
    apply (Fin.heq_fun_iff hsize).mpr
    intro j
    simp [Array.getElem_map]

theorem sequentialMaterialized_map (he : Function.Injective e) (D : Nat)
    (alphabet : Array (Y × ℚ)) (q : Nat) :
    sequentialMaterialized D (alphabet.map (mapEntry e)) q =
      (sequentialMaterialized D alphabet q).map (mapSource e) := by
  induction q with
  | zero =>
      simp [sequentialMaterialized, mapSource, mapWord]
      funext j
      exact Fin.elim0 j
  | succ q ih =>
      have hfeat :
          generatedFeatures (q + 1) D
            ((alphabet.map (mapEntry e)).map Prod.fst) =
          (generatedFeatures (q + 1) D (alphabet.map Prod.fst)).map
            (mapFeature e) := by
        simpa [Array.map_map, mapEntry, Function.comp_def] using
          (generatedFeatures_map e (q + 1) D (alphabet.map Prod.fst))
      simp only [sequentialMaterialized, ih]
      cases hprev : sequentialMaterialized D alphabet q with
      | none => simp [hprev]
      | some prev =>
          simp only [hprev, Option.map_some, Option.bind_some]
          dsimp only [bind, Option.bind, Option.map]
          rw [appendSource_map e prev alphabet]
          exact generatedStep_map e he
            (generatedFeatures (q + 1) D (alphabet.map Prod.fst))
            (generatedFeatures (q + 1) D
              ((alphabet.map (mapEntry e)).map Prod.fst))
            hfeat (appendSource prev alphabet)

end CurrentAdditive.InjectiveCodeDTransport
