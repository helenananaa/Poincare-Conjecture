import MorganTianLib.Ch02.EpsilonNeck

open Set
open scoped Manifold
noncomputable section
namespace MorganTianLib

/-- **Math.** An invertible linear change of model coordinates preserves absence of boundary. -/
theorem boundaryless_model_transContinuousLinearEquiv
    {K E F H : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] [TopologicalSpace H]
    (I : ModelWithCorners K E H) [I.Boundaryless] (e : E ≃L[K] F) :
    (I.transContinuousLinearEquiv e).Boundaryless := by
  constructor
  rw [Set.range_eq_univ]
  intro z
  have hi : Function.Surjective I := Set.range_eq_univ.mp I.range_eq_univ
  obtain ⟨x, hx⟩ := hi (e.symm z)
  refine ⟨x, ?_⟩
  change e (I x) = z
  rw [hx, e.apply_symm_apply]

instance epsilonNeckCylinderModel_instBoundaryless : EpsilonNeckCylinderModel.Boundaryless :=
  boundaryless_model_transContinuousLinearEquiv EpsilonNeckProductModel epsilonNeckModelEquiv

end MorganTianLib
