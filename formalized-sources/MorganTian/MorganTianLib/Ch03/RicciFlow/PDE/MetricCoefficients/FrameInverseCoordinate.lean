import DoCarmoLib.Riemannian.Geodesic.CovariantDerivative
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)

/-- **Math.** frame inverse coordinate. -/
theorem frame_inverse_coordinate (e : Fin 3 ≃ Fin (Module.finrank ℝ E3)) (B : E3 ≃L[ℝ] E3)
    (hB : ∀ i : Fin 3, B (EuclideanSpace.single i 1) = Module.finBasis ℝ E3 (e i))
    (v : E3) (k : Fin 3) :
    (B.symm v) k = Riemannian.Geodesic.chartCoord (E := E3) (e k) v :=
/- SWARM_PROOF_BEGIN -/
by
  have hExpand : B.symm v = ∑ i : Fin 3, (B.symm v) i • EuclideanSpace.single i 1 := by
    simpa using ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (B.symm v)).symm
  have hImage : v = ∑ i : Fin 3, (B.symm v) i • Module.finBasis ℝ E3 (e i) := by
    calc
      v = B (B.symm v) := (B.apply_symm_apply v).symm
      _ = B (∑ i : Fin 3, (B.symm v) i • EuclideanSpace.single i 1) := by rw [← hExpand]
      _ = ∑ i : Fin 3, (B.symm v) i • Module.finBasis ℝ E3 (e i) := by
        simp only [map_sum, map_smul, hB]
  have hrepr := congrArg
    (fun x : E3 => ((Module.finBasis ℝ E3).repr x) (e k)) hImage
  have hCoeff : ((Module.finBasis ℝ E3).repr v) (e k) = (B.symm v) k := by
    calc
      ((Module.finBasis ℝ E3).repr v) (e k) =
          ∑ i : Fin 3, (B.symm v) i *
            (((Module.finBasis ℝ E3).repr (Module.finBasis ℝ E3 (e i))) (e k)) := by
        simpa only [map_sum, map_smul, Finset.sum_apply', Finsupp.smul_apply,
          smul_eq_mul, mul_comm] using hrepr
      _ = (B.symm v) k := by
        simp only [Module.Basis.repr_self]
        simp [Finsupp.single_apply]
  rw [Riemannian.Geodesic.chartCoord_def, hCoeff]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
