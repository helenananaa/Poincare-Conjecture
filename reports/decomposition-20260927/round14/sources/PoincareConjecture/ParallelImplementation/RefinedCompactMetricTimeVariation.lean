import PoincareConjecture.ProofContract.Refinement20260927.CompactMetricComparison
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedCompactMetricTimeVariation
open PoincareConjecture.ProofContract.Refinement20260927
theorem compact_metric_time_variation : CompactMetricTimeVariationStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  intro X hX hcompactX hnonemptyX Q a b hab hQ t ht e he
  have hcompact : IsCompact (Set.Icc a b ×ˢ (Set.univ : Set X)) :=
    isCompact_Icc.prod isCompact_univ
  have hUC : UniformContinuousOn Q (Set.Icc a b ×ˢ (Set.univ : Set X)) :=
    hcompact.uniformContinuousOn_of_continuous hQ
  obtain ⟨d, hd, hclose⟩ := Metric.uniformContinuousOn_iff.mp hUC e he
  refine ⟨d, hd, ?_⟩
  intro s hs hst x
  have hdist : dist (s, x) (t, x) < d := by
    simpa only [dist_prod_same_right] using hst
  have hnorm := hclose (s, x) ⟨hs, Set.mem_univ x⟩ (t, x) ⟨ht, Set.mem_univ x⟩ hdist
  exact le_of_lt (by simpa only [dist_eq_norm] using hnorm)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedCompactMetricTimeVariation
