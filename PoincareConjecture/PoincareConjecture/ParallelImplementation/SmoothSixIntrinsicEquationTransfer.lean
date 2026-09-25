import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import MorganTianLib.Ch03.RicciFlow.HamiltonGauge
import PoincareConjecture.ParallelImplementation.MetricTimeDerivativeFromBasis
import PoincareConjecture.ParallelImplementation.IntrinsicMetricLieBilinear
import PoincareConjecture.ParallelImplementation.SmoothSixIntrinsicDeTurckIdentification
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SmoothSixIntrinsicEquationTransfer
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators ContDiff Manifold
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
theorem intrinsic_equation_of_smooth_coordinate_equation
    (E : E6 →L[ℝ] (E3 →L[ℝ] E3))
    (hE : ∀ (q : E6) (v : E3) (i : Idx), (E q v) i = ∑ j : Idx, symmetricSixMatrix q i j*v j)
    (u : ℝ → E3 → E6) (J : Set ℝ)
    (hu : ∀ t : ℝ, ContDiff ℝ ∞ (u t))
    (hpos : ∀ (t : ℝ) (x v : E3), v ≠ 0 → 0 < inner ℝ (metricOp E (u t) x v) v)
    (heq : ∀ t ∈ J, ∀ (x : E3) (i j : Idx),
      HasDerivWithinAt (fun s => metricCoefficients (u s) x i j)
        (-2*actualRicci E (u t) x i j + actualLie E (u t) x i j) J t) :

    ∃ g : ℝ → Riemannian.RiemannianMetric 𝓘(ℝ, E3) E3,
      ∃ W : ℝ → Riemannian.SmoothVectorField 𝓘(ℝ, E3) E3,
        (∀ (t : ℝ) (x v w : E3), (g t).metricInner x v w = inner ℝ (metricOp E (u t) x v) w) ∧
        (∀ (t : ℝ) (x : E3) (k : Idx), (PiLp.proj (p := 2) (β := fun _ : Idx => ℝ) k : E3 →L[ℝ] ℝ) (W t x) = deturckField E (u t) x k) ∧
        MorganTianLib.IsRicciDeTurckEquationOn g W J :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have hident (t : ℝ) :=
    PoincareConjecture.ParallelImplementation.SmoothSixIntrinsicDeTurckIdentification.exists_six_intrinsic_deturck_identification
      E hE (u t) (hu t) (hpos t)
  choose g W hg hW hric hlie hvar using hident
  refine ⟨g, W, hg, hW, ?_⟩
  change MorganTianLib.IsMetricVariationOn g
    (fun t p v w => MorganTianLib.ricciDeTurckVariation (g t) (W t) p v w) J
  intro t ht x v w
  obtain ⟨L, hL⟩ :=
    PoincareConjecture.ParallelImplementation.IntrinsicMetricLieBilinear.exists_metric_lie_bilinear
      (g t) (W t) x
  let tangentTriv := trivializationAt E3 (TangentSpace 𝓘(ℝ, E3)) x
  let lift : E3 →ₗ[ℝ] TangentSpace 𝓘(ℝ, E3) x :=
    (tangentTriv.symmL ℝ x).toLinearMap
  let coord : TangentSpace 𝓘(ℝ, E3) x →ₗ[ℝ] E3 :=
    (tangentTriv.continuousLinearMapAt ℝ x).toLinearMap
  have hlift_coord (z : TangentSpace 𝓘(ℝ, E3) x) : lift (coord z) = z := by
    simp [lift, coord, tangentTriv]
    rfl
  have hcoord_lift (a : E3) : coord (lift a) = a := by
    simp [lift, coord, tangentTriv]
    rfl
  have hlift_model (a : E3) : lift a = (a : TangentSpace 𝓘(ℝ, E3) x) := by
    change tangentTriv.symmL ℝ x a = _
    rw [TangentBundle.symmL_model_space]
    rfl
  have hlift_single (i : Idx) : lift (EuclideanSpace.single i 1) =
      (EuclideanSpace.single i 1 : TangentSpace 𝓘(ℝ, E3) x) := by
    exact hlift_model _
  let Ric : E3 →ₗ[ℝ] E3 →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ
    (fun a b => MorganTianLib.ricciTensorAt (g t) x (lift a) (lift b))
    (by
      intro a a' b
      simp only [map_add, LinearMap.add_apply])
    (by
      intro c a b
      change MorganTianLib.ricciTensorAt (g t) x (lift (c • a)) (lift b) = _
      rw [lift.map_smul, map_smul]
      change c • ((MorganTianLib.ricciTensorAt (g t) x (lift a)) (lift b)) = _
      simp only [smul_eq_mul])
    (by
      intro a b b'
      simp only [map_add])
    (by
      intro c a b
      change MorganTianLib.ricciTensorAt (g t) x (lift a) (lift (c • b)) = _
      rw [lift.map_smul, map_smul])
  let B : E3 →ₗ[ℝ] E3 →ₗ[ℝ] ℝ := (-2 : ℝ) • Ric + L
  have hRic (a b : E3) :
      Ric a b = MorganTianLib.ricciTensorAt (g t) x (lift a) (lift b) := by
    rfl
  have hLlift (a b : E3) :
      L a b = MorganTianLib.metricLieDerivativeAt (g t) (W t) x (lift a) (lift b) := by
    rw [hL a b]
    rw [hlift_model a, hlift_model b]
  have hcoeff (s : ℝ) (x : E3) (i j : Idx) :
      (g s).metricInner x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
        metricCoefficients (u s) x i j := by
    rw [hg s x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)]
    have hentry :
        (metricOp E (u s) x (EuclideanSpace.single i 1)) j =
          metricCoefficients (u s) x i j := by
      fin_cases i <;> fin_cases j <;>
        simp [metricOp, metricCoefficients, hE, symmetricSixMatrix]
    rw [show inner ℝ (metricOp E (u s) x (EuclideanSpace.single i 1))
        (EuclideanSpace.single j 1) =
          (metricOp E (u s) x (EuclideanSpace.single i 1)) j by
          simp [PiLp.inner_apply]]
    exact hentry
  have hbasis : ∀ i j : Idx,
      HasDerivWithinAt
        (fun s => (g s).metricInner x (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1))
        (B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) J t := by
    intro i j
    have hfun :
        (fun s => (g s).metricInner x (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1)) =
        (fun s => metricCoefficients (u s) x i j) := by
      funext s
      exact hcoeff s x i j
    have hB :
        B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
          -2 * actualRicci E (u t) x i j + actualLie E (u t) x i j := by
      dsimp [B]
      change -2 * (Ric (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1) +
        L (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = _
      rw [hRic, hLlift, hlift_single i, hlift_single j,
        hric t x i j, hlie t x i j]
    rw [hfun]
    exact (heq t ht x i j).congr_deriv hB.symm
  have hderiv :=
    PoincareConjecture.ParallelImplementation.MetricTimeDerivativeFromBasis.metric_time_derivative_from_basis
      g B J t x hbasis
  have hBvw : B (coord v) (coord w) =
      MorganTianLib.ricciDeTurckVariation (g t) (W t) x v w := by
    dsimp [B]
    change -2 * (Ric (coord v)) (coord w) + L (coord v) (coord w) = _
    rw [hRic, hLlift, hlift_coord v, hlift_coord w]
    rfl
  have hfun : (fun s => (g s).metricInner x (coord v) (coord w)) =
      (fun s => (g s).metricInner x v w) := by
    funext s
    rw [← hlift_model (coord v), ← hlift_model (coord w),
      hlift_coord v, hlift_coord w]
  have hd := (hderiv (coord v) (coord w)).congr
    (fun s _ => (congrFun hfun s).symm) (congrFun hfun t).symm
  exact hd.congr_deriv hBvw
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SmoothSixIntrinsicEquationTransfer
