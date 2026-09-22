import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateMetricCompatibility
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffelSmooth
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SymmetricInverseBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- The actual vector-valued coordinate connection term. -/
def connectionVector (A : E3 →L[ℝ] E3) (P : Fin 3 → E3 →L[ℝ] E3) (X Y : E3) : E3 :=
  WithLp.toLp 2 (fun k : Fin 3 => ∑ i : Fin 3, ∑ j : Fin 3,
    coordinateChristoffel A P k i j*X i*Y j)
/-- A bounded bilinear map realizes the coordinate expression, with quantitative control. -/
theorem connection_vector_bilinear (A : E3 →L[ℝ] E3) (P : Fin 3 → E3 →L[ℝ] E3)
    (c : ℝ) (hc : 0<c) (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v) :
    ∃ B : E3 →L[ℝ] E3 →L[ℝ] E3,
      (∀ X Y : E3, B X Y=connectionVector A P X Y) ∧
      ‖B‖ ≤ (100/c)*(∑ l : Fin 3, ‖P l‖) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let q : Fin 3 → E3 →L[ℝ] ℝ := fun i => EuclideanSpace.proj i
  let inc : Fin 3 → ℝ →L[ℝ] E3 := fun k =>
    ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single k (1 : ℝ))
  let R : Fin 3 → Fin 3 → Fin 3 → E3 →L[ℝ] E3 →L[ℝ] E3 := fun k i j =>
    (q i).smulRight
      (coordinateChristoffel A P k i j • (inc k).comp (q j))
  let B : E3 →L[ℝ] E3 →L[ℝ] E3 :=
    ∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, R k i j
  have hcoord : ∀ x : E3, ∀ i : Fin 3, ‖x i‖ ≤ ‖x‖ := by
    intro x i
    rw [EuclideanSpace.norm_eq]
    have hnonneg : 0 ≤ ∑ r : Fin 3, ‖x.ofLp r‖ ^ 2 :=
      Finset.sum_nonneg (fun r _ => sq_nonneg _)
    apply (Real.le_sqrt (norm_nonneg _) hnonneg).2
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin 3)))
      (f := fun r : Fin 3 => ‖x.ofLp r‖ ^ 2)
      (fun r _ => sq_nonneg _) (Finset.mem_univ i)
  have hq : ∀ i : Fin 3, ‖q i‖ ≤ 1 := by
    intro i
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro x
    simpa [q, Real.norm_eq_abs] using hcoord x i
  have hinc : ∀ k : Fin 3, ‖inc k‖ ≤ 1 := by
    intro k
    simpa [inc] using
      (ContinuousLinearMap.norm_toSpanSingleton
        (EuclideanSpace.single k (1 : ℝ)))
  have hinner : ∀ k j : Fin 3, ‖(inc k).comp (q j)‖ ≤ 1 := by
    intro k j
    calc
      ‖(inc k).comp (q j)‖ ≤ ‖inc k‖ * ‖q j‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul (hinc k) (hq j) (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hterm : ∀ k i j : Fin 3,
      ‖R k i j‖ ≤ |coordinateChristoffel A P k i j| := by
    intro k i j
    apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg _)
    intro x
    change ‖q i x •
        (coordinateChristoffel A P k i j • (inc k).comp (q j))‖ ≤
      |coordinateChristoffel A P k i j| * ‖x‖
    calc
      ‖q i x •
          (coordinateChristoffel A P k i j • (inc k).comp (q j))‖ =
      ‖q i x‖ *
            (|coordinateChristoffel A P k i j| * ‖(inc k).comp (q j)‖) := by
        simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖x‖ * (|coordinateChristoffel A P k i j| * 1) := by
        gcongr
        · simpa [q, Real.norm_eq_abs] using hcoord x i
        · exact hinner k j
      _ = |coordinateChristoffel A P k i j| * ‖x‖ := by ring
  let S : ℝ := ∑ l : Fin 3, ‖P l‖
  have hS : 0 ≤ S := by
    exact Finset.sum_nonneg (fun l _ => norm_nonneg _)
  have hPcoord : ∀ i : Fin 3, ‖P i‖ ≤ S := by
    intro i
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin 3)))
      (f := fun l : Fin 3 => ‖P l‖)
      (fun l _ => norm_nonneg _) (Finset.mem_univ i)
  have hgamma : ∀ k i j : Fin 3,
      |coordinateChristoffel A P k i j| ≤ (7 / (2 * c)) * S := by
    intro k i j
    have hinside : 3 * ‖P i‖ + 3 * ‖P j‖ + S ≤ 7 * S := by
      nlinarith [hPcoord i, hPcoord j]
    calc
      |coordinateChristoffel A P k i j| ≤
          (1 / (2 * c)) *
            (3 * ‖P i‖ + 3 * ‖P j‖ + ∑ l : Fin 3, ‖P l‖) :=
        coordinate_christoffel_bound A c hc hA P k i j
      _ = (1 / (2 * c)) * (3 * ‖P i‖ + 3 * ‖P j‖ + S) := by rfl
      _ ≤ (1 / (2 * c)) * (7 * S) := by
        gcongr
      _ = (7 / (2 * c)) * S := by ring
  refine ⟨B, ?_, ?_⟩
  · intro X Y
    ext k
    simp [B, R, q, inc, connectionVector,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
      Pi.single_apply]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · have hsum : ‖B‖ ≤
        ∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, ‖R k i j‖ := by
      dsimp [B]
      calc
        ‖∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, R k i j‖ ≤
            ∑ k : Fin 3, ‖∑ i : Fin 3, ∑ j : Fin 3, R k i j‖ := by
              exact norm_sum_le (Finset.univ : Finset (Fin 3)) (fun k : Fin 3 => ∑ i : Fin 3, ∑ j : Fin 3, R k i j)
        _ ≤ ∑ k : Fin 3, ∑ i : Fin 3, ‖∑ j : Fin 3, R k i j‖ := by
              gcongr with k hk
              exact norm_sum_le (Finset.univ : Finset (Fin 3)) (fun i : Fin 3 => ∑ j : Fin 3, R k i j)
        _ ≤ ∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, ‖R k i j‖ := by
              gcongr with k hk i hi
              exact norm_sum_le (Finset.univ : Finset (Fin 3)) (fun j : Fin 3 => R k i j)
    calc
      ‖B‖ ≤ ∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
          |coordinateChristoffel A P k i j| := by
        exact hsum.trans (by
          gcongr with k hk i hi j hj
          exact hterm k i j)
      _ ≤ ∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
          (7 / (2 * c)) * S := by
        gcongr with k hk i hi j hj
        exact hgamma k i j
      _ = 27 * ((7 / (2 * c)) * S) := by
        simp
        ring
      _ ≤ (100 / c) * S := by
        have hcoeff : 27 * (7 / (2 * c)) ≤ 100 / c := by
          field_simp [ne_of_gt hc]
          nlinarith
        calc
          27 * ((7 / (2 * c)) * S) = (27 * (7 / (2 * c))) * S := by ring
          _ ≤ (100 / c) * S := mul_le_mul_of_nonneg_right hcoeff hS
      _ = (100 / c) * (∑ l : Fin 3, ‖P l‖) := by rfl
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
