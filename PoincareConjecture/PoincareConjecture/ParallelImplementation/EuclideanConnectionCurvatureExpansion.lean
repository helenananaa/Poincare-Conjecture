import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import MorganTianLib.Ch03.RicciFlow.Basic
import PoincareConjecture.ParallelImplementation.ScalarCoordinateLineDerivative
import PoincareConjecture.ParallelImplementation.EuclideanCovariantFrameExpansion
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.EuclideanConnectionCurvatureExpansion
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators ContDiff Manifold
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
theorem curvature_in_coordinate_frame
    (D : Riemannian.AffineConnection 𝓘(ℝ, E3) E3)
    (V : Idx → Riemannian.SmoothVectorField 𝓘(ℝ, E3) E3)
    (hV : ∀ (i : Idx) (x : E3), V i x = EuclideanSpace.single i 1)
    (G : E3 → First)
    (hG : ∀ (x : E3) (i j k : Idx), (PiLp.proj (p := 2) (β := fun _ : Idx => ℝ) k : E3 →L[ℝ] ℝ) ((D.cov (V i) (V j)) x) = G x k i j)
    (hbr : ∀ (i j : Idx) (x : E3), Riemannian.DCLieBracket (V i) (V j) x = 0)
    (hGsmooth : ∀ k i j : Idx, ContDiff ℝ ∞ (fun x : E3 => G x k i j)) :

    ∀ (x : E3) (i j k s : Idx), (PiLp.proj (p := 2) (β := fun _ : Idx => ℝ) s : E3 →L[ℝ] ℝ) ((D.curvature (V i) (V j) (V k)) x) = (deriv (fun t : ℝ => G (x + t • EuclideanSpace.single j 1) s i k) 0 - deriv (fun t : ℝ => G (x + t • EuclideanSpace.single i 1) s j k) 0 + (∑ m : Idx, (G x m i k * G x s j m - G x m j k * G x s i m))) :=
/- SWARM_PROOF_BEGIN -/
by
  intro x i j k s
  classical
  let π : Idx → E3 →L[ℝ] ℝ := fun a =>
    PiLp.proj (p := 2) (β := fun _ : Idx => ℝ) a
  have hframe :=
    PoincareConjecture.ParallelImplementation.EuclideanCovariantFrameExpansion.covariant_derivative_in_frame
      D V hV G hG
  have hfirst :
      π s ((D.cov (V j) (D.cov (V i) (V k))) x) =
        fderiv ℝ (fun y : E3 => G y s i k) x (EuclideanSpace.single j 1) +
          ∑ m : Idx, G x s j m * G x m i k := by
    have h := hframe (D.cov (V i) (V k)) x j s
    change π s ((D.cov (V j) (D.cov (V i) (V k))) x) =
      fderiv ℝ (fun y : E3 => π s ((D.cov (V i) (V k)) y)) x
          (EuclideanSpace.single j 1) +
        ∑ m : Idx, G x s j m * π m ((D.cov (V i) (V k)) x) at h
    have hcoord :
        (fun y : E3 => π s ((D.cov (V i) (V k)) y)) = fun y => G y s i k := by
      funext y
      exact hG y i k s
    rw [hcoord] at h
    have hsum :
        (∑ m : Idx, G x s j m * π m ((D.cov (V i) (V k)) x)) =
          ∑ m : Idx, G x s j m * G x m i k := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [hG x i k m]
    rw [hsum] at h
    exact h
  have hsecond :
      π s ((D.cov (V i) (D.cov (V j) (V k))) x) =
        fderiv ℝ (fun y : E3 => G y s j k) x (EuclideanSpace.single i 1) +
          ∑ m : Idx, G x s i m * G x m j k := by
    have h := hframe (D.cov (V j) (V k)) x i s
    change π s ((D.cov (V i) (D.cov (V j) (V k))) x) =
      fderiv ℝ (fun y : E3 => π s ((D.cov (V j) (V k)) y)) x
          (EuclideanSpace.single i 1) +
        ∑ m : Idx, G x s i m * π m ((D.cov (V j) (V k)) x) at h
    have hcoord :
        (fun y : E3 => π s ((D.cov (V j) (V k)) y)) = fun y => G y s j k := by
      funext y
      exact hG y j k s
    rw [hcoord] at h
    have hsum :
        (∑ m : Idx, G x s i m * π m ((D.cov (V j) (V k)) x)) =
          ∑ m : Idx, G x s i m * G x m j k := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [hG x j k m]
    rw [hsum] at h
    exact h
  have hbrq :
      Riemannian.bracketField (V i) (V j) x =
        (0 : Riemannian.SmoothVectorField 𝓘(ℝ, E3) E3) x := by
    simp [Riemannian.bracketField_apply, hbr i j x]
  have hbrcov :
      (D.cov (Riemannian.bracketField (V i) (V j)) (V k)) x = 0 := by
    rw [D.cov_congr_apply_left (V k) hbrq, D.cov_zero_left]
  have hd1 : DifferentiableAt ℝ (fun y : E3 => G y s i k) x :=
    (ContDiff.differentiable (hGsmooth s i k) (by simp)) x
  have hd2 : DifferentiableAt ℝ (fun y : E3 => G y s j k) x :=
    (ContDiff.differentiable (hGsmooth s j k) (by simp)) x
  have hderiv1 :=
    PoincareConjecture.ParallelImplementation.ScalarCoordinateLineDerivative.fderiv_eq_coordinate_deriv
      (fun y : E3 => G y s i k) x j hd1
  have hderiv2 :=
    PoincareConjecture.ParallelImplementation.ScalarCoordinateLineDerivative.fderiv_eq_coordinate_deriv
      (fun y : E3 => G y s j k) x i hd2
  calc
    π s ((D.curvature (V i) (V j) (V k)) x) =
        π s ((D.cov (V j) (D.cov (V i) (V k))) x) -
          π s ((D.cov (V i) (D.cov (V j) (V k))) x) := by
      rw [D.curvature_apply]
      simp only [map_add, map_sub]
      rw [hbrcov]
      simp
    _ = deriv (fun t : ℝ => G (x + t • EuclideanSpace.single j 1) s i k) 0 -
          deriv (fun t : ℝ => G (x + t • EuclideanSpace.single i 1) s j k) 0 +
          ∑ m : Idx,
            (G x m i k * G x s j m - G x m j k * G x s i m) := by
      have hsum1 :
          (∑ m : Idx, G x s j m * G x m i k) =
            ∑ m : Idx, G x m i k * G x s j m := by
        apply Finset.sum_congr rfl
        intro m hm
        exact mul_comm _ _
      have hsum2 :
          (∑ m : Idx, G x s i m * G x m j k) =
            ∑ m : Idx, G x m j k * G x s i m := by
        apply Finset.sum_congr rfl
        intro m hm
        exact mul_comm _ _
      have hquad :
          (∑ m : Idx, G x s j m * G x m i k) -
            (∑ m : Idx, G x s i m * G x m j k) =
              ∑ m : Idx,
                (G x m i k * G x s j m - G x m j k * G x s i m) := by
        calc
          (∑ m : Idx, G x s j m * G x m i k) -
              (∑ m : Idx, G x s i m * G x m j k) =
                (∑ m : Idx, G x m i k * G x s j m) -
                  (∑ m : Idx, G x m j k * G x s i m) := by
            rw [hsum1, hsum2]
          _ = ∑ m : Idx,
                (G x m i k * G x s j m - G x m j k * G x s i m) := by
            rw [Finset.sum_sub_distrib]
      rw [hfirst, hsecond, hderiv1, hderiv2]
      linear_combination hquad
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.EuclideanConnectionCurvatureExpansion
