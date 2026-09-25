import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import MorganTianLib.Ch03.RicciFlow.HamiltonGauge
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.MetricTimeDerivativeFromBasis
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators ContDiff Manifold
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
theorem metric_time_derivative_from_basis
    (g : ℝ → Riemannian.RiemannianMetric 𝓘(ℝ, E3) E3)
    (B : E3 →ₗ[ℝ] E3 →ₗ[ℝ] ℝ) (J : Set ℝ) (t : ℝ) (x : E3)
    (hderiv : ∀ i j : Idx, HasDerivWithinAt
      (fun s => (g s).metricInner x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
      (B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) J t) :

    ∀ v w : E3, HasDerivWithinAt (fun s => (g s).metricInner x v w) (B v w) J t :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let e : Idx → E3 := fun i => EuclideanSpace.single i 1
  have hrep (v : E3) : (∑ i : Idx, v i • e i) = v := by
    simpa [e] using (EuclideanSpace.basisFun Idx ℝ).sum_repr v
  have hmetric (m : Riemannian.RiemannianMetric 𝓘(ℝ, E3) E3) (v w : E3) :
      m.metricInner x v w =
        ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ,
          v i * w j * m.metricInner x (e i) (e j) := by
    have hleft (s : Finset Idx) (z : E3) :
        m.metricInner x (∑ i ∈ s, v i • e i)
            (z : TangentSpace 𝓘(ℝ, E3) x) =
          ∑ i ∈ s, v i *
            m.metricInner x (e i : TangentSpace 𝓘(ℝ, E3) x) z := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
          rw [Finset.sum_insert hi, m.metricInner_add_left, m.metricInner_smul_left,
            ih, Finset.sum_insert hi]
    have hright (s : Finset Idx) (z : E3) :
        m.metricInner x (z : TangentSpace 𝓘(ℝ, E3) x)
            (∑ j ∈ s, w j • e j) =
          ∑ j ∈ s, w j *
            m.metricInner x z (e j : TangentSpace 𝓘(ℝ, E3) x) := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert j s hj ih =>
          rw [Finset.sum_insert hj, m.metricInner_add_right, m.metricInner_smul_right,
            ih, Finset.sum_insert hj]
    calc
      m.metricInner x v w =
          m.metricInner x (∑ i ∈ Finset.univ, v i • e i)
            (∑ j ∈ Finset.univ, w j • e j) := by rw [hrep v, hrep w]
      _ = ∑ i ∈ Finset.univ,
            v i * m.metricInner x (e i : TangentSpace 𝓘(ℝ, E3) x)
              (∑ j ∈ Finset.univ, w j • e j) :=
          hleft Finset.univ _
      _ = ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ,
            v i * w j * m.metricInner x
              (e i : TangentSpace 𝓘(ℝ, E3) x)
              (e j : TangentSpace 𝓘(ℝ, E3) x) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hright Finset.univ (e i)]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
  intro v w
  have hsum : HasDerivWithinAt
      (fun s : ℝ => ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ,
        v i * w j * (g s).metricInner x (e i) (e j))
      (∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ,
        v i * w j * B (e i) (e j)) J t := by
    apply HasDerivWithinAt.fun_sum
    intro i hi
    apply HasDerivWithinAt.fun_sum
    intro j hj
    convert (hderiv i j).const_smul (v i * w j) using 1
    · funext y
      simp [e, Pi.smul_apply, smul_eq_mul]
    · ring
  have hB : B v w =
      ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ,
        v i * w j * B (e i) (e j) := by
    have hleft (z : E3) :
        B (∑ i ∈ Finset.univ, v i • e i) z =
          ∑ i ∈ Finset.univ, v i * B (e i) z := by
      simp only [map_sum, map_smul, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_eq_mul]
    have hright (i : Idx) :
        B (e i) (∑ j ∈ Finset.univ, w j • e j) =
          ∑ j ∈ Finset.univ, w j * B (e i) (e j) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    calc
      B v w = B (∑ i ∈ Finset.univ, v i • e i)
          (∑ j ∈ Finset.univ, w j • e j) := by rw [hrep v, hrep w]
      _ = ∑ i ∈ Finset.univ, v i *
          B (e i) (∑ j ∈ Finset.univ, w j • e j) := hleft _
      _ = ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ,
          v i * w j * B (e i) (e j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hright i]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have h := hsum.congr (fun s _ => hmetric (g s) v w)
    (hmetric (g t) v w)
  exact h.congr_deriv hB.symm
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.MetricTimeDerivativeFromBasis
