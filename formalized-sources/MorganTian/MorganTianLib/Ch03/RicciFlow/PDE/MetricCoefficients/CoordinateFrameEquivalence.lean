import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators Manifold Bundle RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- The coordinate reindexing is implemented by an actual linear equivalence, not an assumed orthonormal frame. -/
theorem coordinate_frame_equivalence (e : Fin 3 ≃ Fin (Module.finrank ℝ E3)) :
    ∃ B : E3 ≃L[ℝ] E3, ∀ v : E3,
      B v = ∑ i : Fin 3, v i • Module.finBasis ℝ E3 (e i) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let b : Module.Basis (Fin 3) ℝ E3 := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let L : E3 ≃ₗ[ℝ] E3 :=
    b.equivFun.trans ((Module.finBasis ℝ E3).reindex e.symm).equivFun.symm
  refine ⟨L.toContinuousLinearEquiv, ?_⟩
  intro v
  change L v = _
  simp [L, b, Module.Basis.equivFun_symm_apply, EuclideanSpace.basisFun_repr]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
