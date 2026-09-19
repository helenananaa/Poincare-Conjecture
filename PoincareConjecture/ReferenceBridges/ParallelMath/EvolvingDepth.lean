import MorganTianLib.Ch03.RicciFlow.EvolvingEpsilonNeck
import ReferenceBridges.ParallelMath.EpsilonFamilyReindex
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Reference
open Set Function Filter
open scoped BigOperators Topology Manifold ContDiff Bundle RealInnerProductSpace

/-- Restrict a real evolving epsilon-neck to a shorter backward interval, preserving its central neck. -/
theorem evolvingNeck_restrict_depth {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    {epsilon tau : ℝ} {g : ℝ → Riemannian.RiemannianMetric I M} {J : Set ℝ}
    {x : M} {t0 : J} (N : MorganTianLib.EvolvingEpsilonNeck epsilon g J x t0 tau)
    (sigma : ℝ) (hsigma : 0 < sigma) (hle : sigma ≤ tau) :
    ∃ N' : MorganTianLib.EvolvingEpsilonNeck epsilon g J x t0 sigma,
      N'.centralNeck = N.centralNeck :=
/- SWARM_PROOF_BEGIN -/
by
  have hsub : MorganTianLib.evolvingEpsilonNeckTimeSet sigma ⊆
      MorganTianLib.evolvingEpsilonNeckTimeSet tau := by
    intro t ht
    have ht' : t ∈ Ioc (-sigma) (0 : ℝ) := by
      simpa [MorganTianLib.evolvingEpsilonNeckTimeSet] using ht
    have : t ∈ Ioc (-tau) (0 : ℝ) :=
      Ioc_subset_Ioc_left (neg_le_neg hle) ht'
    simpa [MorganTianLib.evolvingEpsilonNeckTimeSet] using this
  let incl : MorganTianLib.evolvingEpsilonNeckTimeSet sigma →
      MorganTianLib.evolvingEpsilonNeckTimeSet tau :=
    Set.inclusion hsub
  have hzero :
      incl (MorganTianLib.evolvingEpsilonNeckZeroTime hsigma) =
        MorganTianLib.evolvingEpsilonNeckZeroTime N.depth_pos :=
    Subtype.ext rfl
  haveI : MorganTianLib.EpsilonNeckCylinderModel.Boundaryless := by
    constructor
    rw [ModelWithCorners.transContinuousLinearEquiv_range]
    haveI : MorganTianLib.EpsilonNeckProductModel.Boundaryless := inferInstance
    rw [ModelWithCorners.range_eq_univ]
    exact image_univ_of_surjective MorganTianLib.epsilonNeckModelEquiv.surjective
  refine ⟨
    { flow := N.flow
      depth_pos := hsigma
      scalar_curvature_pos := N.scalar_curvature_pos
      centralNeck := N.centralNeck
      central_center := N.central_center
      time_available := fun s => N.time_available (incl s)
      referenceMetricFamily := N.referenceMetricFamily ∘ incl
      referenceMetric_is_standard := fun s p v w =>
        N.referenceMetric_is_standard (incl s) p v w
      normalizedMetricFamily := N.normalizedMetricFamily ∘ incl
      normalizedMetric_is_pullback := fun s p v w =>
        N.normalizedMetric_is_pullback (incl s) p v w
      central_agreement := fun p v w => by
        convert N.central_agreement p v w
        rw [Function.comp_apply, hzero]
      close := epsilonCloseFamily_reindex N.referenceMetricFamily
        N.normalizedMetricFamily N.close incl },
    rfl⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Reference
