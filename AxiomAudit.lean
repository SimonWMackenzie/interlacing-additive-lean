import CurrentAdditive
import Lean.Util.CollectAxioms

/-!
Audit every new declaration, including private/generated declarations, and
its transitive dependencies. This checks kernel assumptions, not statement
faithfulness or the full-manuscript completion status.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut declarations := 0
  let mut theorems := 0
  for (name, info) in env.constants.toList do
    let ownedByModule := match env.getModuleIdxFor? name with
      | some index => (`CurrentAdditive).isPrefixOf moduleNames[index]!
      | none => false
    if ownedByModule || (`CurrentAdditive).isPrefixOf name then
      declarations := declarations + 1
      if info.isTheorem then
        theorems := theorems + 1
      for axiomName in (← Lean.collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Forbidden axiom {axiomName} in {name}"
  if declarations == 0 || theorems == 0 then
    throwError "Empty CurrentAdditive proof import"
  logInfo m!"CurrentAdditive axiom audit: {declarations} declarations, {theorems} theorems; only propext, Classical.choice, Quot.sound permitted."

#print axioms CurrentAdditive.rational_support_reduction_step
#print axioms CurrentAdditive.integer_support_reduction_step
#print axioms CurrentAdditive.exists_rational_affine_dependence
#print axioms CurrentAdditive.exists_compressed_positive_weights
#print axioms CurrentAdditive.ProjectionMass.ambient_image_mass_ge_conditional_mass_sub
#print axioms CurrentAdditive.ProjectionMass.projected_interlace_cost_le_indexed
#print axioms CurrentAdditive.DeterministicIteration.conditional_reduction
#print axioms CurrentAdditive.SmallBias.pattern_prob_le
#print axioms CurrentAdditive.SmallBias.patterns_prob_le
#print axioms CurrentAdditive.SmallBias.no_retained_cover
#print axioms CurrentAdditive.SmallBias.no_short_lookup_initial_cut_v27
#print axioms CurrentAdditive.flatten_dwise
#print axioms CurrentAdditive.rational_fixed_metadata_flatten_dwise
#print axioms CurrentAdditive.RandomizedSchedule.overhead27_bounds
#print axioms CurrentAdditive.SuffixSmall.suffix_zero
#print axioms CurrentAdditive.SuffixSmall.suffix_one
#print axioms CurrentAdditive.finiteFieldPowering_epsilonBias
#print axioms CurrentAdditive.finite_exceptional_cover_ceiling
#print axioms CurrentAdditive.indicator_witness_count_of_even_moment
#print axioms CurrentAdditive.exists_rational_dwise_source
#print axioms CurrentAdditive.FiniteFieldAdapter.seedLaw_isSmallBiased
#print axioms CurrentAdditive.SmallBias.actual_cut_rectangle
#print axioms CurrentAdditive.SuffixMid.suffix_two
#print axioms CurrentAdditive.SuffixMid.suffix_three
#print axioms CurrentAdditive.SuffixMid.suffix_four
#print axioms CurrentAdditive.exists_rational_dwise_source_le_one_add_pow
#print axioms CurrentAdditive.FiniteFieldAdapter.vectorSeedLaw_isSmallBiased
#print axioms CurrentAdditive.SmallBias.no_short_lookup_source_cut
#print axioms CurrentAdditive.SmallBias.no_payloadShortProtocolFailure_of_small_bias
#print axioms CurrentAdditive.ArbitraryPrefix.padded_prefix
#print axioms CurrentAdditive.Eventual.T24_class_eventual
#print axioms CurrentAdditive.Eventual.T24_square_class_eventual
#print axioms CurrentAdditive.conditioning_exceptional_coordinates_of_even_moment
#print axioms CurrentAdditive.centered_indicator_even_moment_eq_proxy
#print axioms CurrentAdditive.disjoint_blocks_indicator_joint_agreement
#print axioms CurrentAdditive.EvenMoment.iid_centered_indicator_moment_1024
#print axioms CurrentAdditive.exactlyKWiseIndependent_of_isDWise
#print axioms CurrentAdditive.conditioning_exceptional_coordinates_R
#print axioms CurrentAdditive.SmallBias.lower_bound_fullSelector_small_biased
