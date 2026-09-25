import Mathlib
import PoincareConjecture.ParallelImplementation.SymmetricSixPacking
import PoincareConjecture.ParallelImplementation.EuclideanCoordinateFields
import PoincareConjecture.ParallelImplementation.EuclideanPositiveOperatorMetric
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.EuclideanMetricOperatorRepresentation
open scoped Topology BigOperators ContDiff Manifold BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem exists_metric_operator_representation
    (g : Riemannian.RiemannianMetric 𝓘(ℝ, E3) E3) :

    ∃ M : E3 → (E3 →L[ℝ] E3), ContDiff ℝ ∞ M ∧
      (∀ x v w : E3, g.metricInner x v w = inner ℝ (M x v) w) ∧
      (∀ x v w : E3, inner ℝ (M x v) w = inner ℝ (M x w) v) ∧
      ∀ x v : E3, v ≠ 0 → 0 < inner ℝ (M x v) v :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E3) : E3 → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e : ∀ x : E3, TangentSpace 𝓘(ℝ, E3) x ≃L[ℝ] E3 := fun x =>
    NormedSpace.fromTangentSpace x
  let b : Fin 3 → E3 := fun i => EuclideanSpace.single i (1 : ℝ)
  have hbasis (v : E3) : v = ∑ i : Fin 3, v i • b i := by
    simpa [b, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
      ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v).symm
  let X : Fin 3 → Riemannian.SmoothVectorField 𝓘(ℝ, E3) E3 := fun i =>
    ⟨fun x => (e x).symm (b i), by
      rw [contMDiff_vectorSpace_iff_contDiff]
      have hconst : (fun y : E3 => (e y).symm (b i)) = fun _ => b i := by
        funext y
        rfl
      rw [hconst]
      exact contDiff_const⟩
  let c : E3 → Fin 3 → Fin 3 → ℝ := fun x i j =>
    g.metricInner x ((e x).symm (b i)) ((e x).symm (b j))
  have hcMD (i j : Fin 3) :
      ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞
        (fun x => g.metricInner x ((e x).symm (b i)) ((e x).symm (b j))) := by
    intro x
    have h := g.metricInner_contMDiffWithinAt
      (s := Set.univ) (x := x) (n := (∞ : ℕ∞ω))
      (v := fun y => X i y) (w := fun y => X j y)
      ((X i).smooth x).contMDiffWithinAt ((X j).smooth x).contMDiffWithinAt
    rw [contMDiffWithinAt_univ] at h
    simpa [X, c] using h
  have hc (i j : Fin 3) : ContDiff ℝ ∞ (fun x => c x i j) := by
    apply (contMDiff_iff_contDiff).mp
    simpa [c] using hcMD i j
  let R : Fin 3 → Fin 3 → E3 →L[ℝ] E3 := fun i j =>
    (innerSL ℝ (b i)).smulRight (b j)
  let M : E3 → E3 →L[ℝ] E3 := fun x =>
    ∑ i : Fin 3, ∑ j : Fin 3, (c x i j) • R i j
  have hM : ContDiff ℝ ∞ M := by
    change ContDiff ℝ ∞ (fun x =>
      ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, (c x i j) • R i j)
    refine ContDiff.sum (s := Finset.univ) ?_
    intro i hi
    refine ContDiff.sum (s := Finset.univ) ?_
    intro j hj
    exact (hc i j).smul contDiff_const
  have hpair (x v w : E3) :
      inner ℝ (M x v) w = ∑ i : Fin 3, ∑ j : Fin 3, c x i j * v i * w j := by
    change inner ℝ
      (∑ i : Fin 3, ∑ j : Fin 3, (c x i j) • (R i j v)) w = _
    simp only [sum_inner]
    simp [R, b, EuclideanSpace.inner_single_left, inner_smul_left,
      ContinuousLinearMap.smulRight_apply,
      mul_assoc, mul_comm, mul_left_comm]
  have hmodel (x : E3) (v : E3) :
      (e x).symm v = ∑ i : Fin 3, v i • (e x).symm (b i) := by
    calc
      (e x).symm v = (e x).symm (∑ i : Fin 3, v i • b i) :=
        congrArg ((e x).symm) (hbasis v)
      _ = ∑ i : Fin 3, v i • (e x).symm (b i) := by simp
  have hmetric (x v w : E3) :
      g.metricInner x ((e x).symm v) ((e x).symm w) =
        ∑ i : Fin 3, ∑ j : Fin 3, c x i j * v i * w j := by
    have hbase :
        g.metricInner x ((e x).symm v) ((e x).symm w) =
          ∑ j : Fin 3, w j * ∑ i : Fin 3,
            v i * g.metricInner x ((e x).symm (b i)) ((e x).symm (b j)) := by
      rw [hmodel x v, hmodel x w]
      simp only [Riemannian.RiemannianMetric.metricInner,
        map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
    rw [hbase]
    calc
      (∑ j : Fin 3, w j * ∑ i : Fin 3,
          v i * g.metricInner x ((e x).symm (b i)) ((e x).symm (b j)))
          = ∑ i : Fin 3, ∑ j : Fin 3,
              v i * (w j * g.metricInner x ((e x).symm (b i)) ((e x).symm (b j))) := by
        calc
          _ = ∑ j : Fin 3, ∑ i : Fin 3,
                w j * (v i * g.metricInner x ((e x).symm (b i)) ((e x).symm (b j))) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [Finset.mul_sum]
          _ = ∑ i : Fin 3, ∑ j : Fin 3,
                w j * (v i * g.metricInner x ((e x).symm (b i)) ((e x).symm (b j))) := by
              rw [Finset.sum_comm]
          _ = ∑ i : Fin 3, ∑ j : Fin 3,
                v i * (w j * g.metricInner x ((e x).symm (b i)) ((e x).symm (b j))) := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              ring
      _ = ∑ i : Fin 3, ∑ j : Fin 3, c x i j * v i * w j := by
        simp [c, mul_comm, mul_left_comm]
  have hrep (x v w : E3) : g.metricInner x v w = inner ℝ (M x v) w := by
    have hv : (e x).symm (e x v) = v := (e x).symm_apply_apply v
    have hw : (e x).symm (e x w) = w := (e x).symm_apply_apply w
    calc
      g.metricInner x v w =
          g.metricInner x ((e x).symm (e x v)) ((e x).symm (e x w)) := by rw [hv, hw]
      _ = ∑ i : Fin 3, ∑ j : Fin 3, c x i j * (e x v) i * (e x w) j :=
        hmetric x (e x v) (e x w)
      _ = inner ℝ (M x v) w := by
        rw [hpair]
        simp [e, NormedSpace.fromTangentSpace, mul_comm, mul_left_comm]
  refine ⟨M, hM, hrep, ?_, ?_⟩
  · intro x v w
    rw [← hrep x v w, ← hrep x w v]
    exact g.metricInner_comm x v w
  · intro x v hv
    rw [← hrep x v v]
    exact g.metricInner_self_pos x v hv
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.EuclideanMetricOperatorRepresentation
