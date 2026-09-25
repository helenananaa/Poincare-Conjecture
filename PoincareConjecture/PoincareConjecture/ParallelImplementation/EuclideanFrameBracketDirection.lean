import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import MorganTianLib.Ch03.RicciFlow.HamiltonGauge
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.EuclideanFrameBracketDirection
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators ContDiff Manifold
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
theorem frame_bracket_and_direction
    (W : Riemannian.SmoothVectorField 𝓘(ℝ, E3) E3)
    (V : Idx → Riemannian.SmoothVectorField 𝓘(ℝ, E3) E3)
    (hV : ∀ (i : Idx) (x : E3), V i x = EuclideanSpace.single i 1) :

    (∀ (i : Idx) (x : E3), Riemannian.DCLieBracket W (V i) x =
      -(fderiv ℝ (fun y : E3 => (W y : E3)) x (EuclideanSpace.single i 1))) ∧
      ∀ (f : E3 → ℝ) (x : E3), W.dir f x =
        ∑ k : Idx, (PiLp.proj (p := 2) (β := fun _ : Idx => ℝ) k : E3 →L[ℝ] ℝ) (W x) * fderiv ℝ f x (EuclideanSpace.single k 1) :=
/- SWARM_PROOF_BEGIN -/
by
  constructor
  · intro i x
    have hVi : (V i : E3 → E3) = fun _ => EuclideanSpace.single i 1 :=
      funext (hV i)
    change VectorField.mlieBracket 𝓘(ℝ, E3)
      (W : E3 → E3) (V i : E3 → E3) x = _
    rw [← VectorField.mlieBracketWithin_univ,
      VectorField.mlieBracketWithin_eq_lieBracketWithin,
      VectorField.lieBracketWithin_univ,
      VectorField.lieBracket]
    simp [hVi]
  · intro f x
    change mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) f x (W x) = _
    rw [mfderiv_eq_fderiv]
    have hrepr := (EuclideanSpace.basisFun Idx ℝ).sum_repr (W x)
    rw [← hrepr, map_sum]
    simp [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr,
      PiLp.proj]
    rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.EuclideanFrameBracketDirection
