import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import MorganTianLib.Ch03.RicciFlow.HamiltonGauge
import PoincareConjecture.ParallelImplementation.EuclideanCoordinateFields
import PoincareConjecture.ParallelImplementation.ScalarCoordinateLineDerivative
import PoincareConjecture.ParallelImplementation.EuclideanFrameBracketDirection
import PoincareConjecture.ParallelImplementation.IntrinsicMetricLieBracketFormula
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.EuclideanMetricLieCoordinates
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators ContDiff Manifold
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
theorem metric_lie_coordinate_formula
    (g : Riemannian.RiemannianMetric 𝓘(ℝ, E3) E3)
    (W : Riemannian.SmoothVectorField 𝓘(ℝ, E3) E3) :

    ∀ (x : E3) (i j : Idx), MorganTianLib.metricLieDerivativeAt g W x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      ∑ k : Idx, ((PiLp.proj (p := 2) (β := fun _ : Idx => ℝ) k : E3 →L[ℝ] ℝ) (W x) * fderiv ℝ (fun y : E3 => g.metricInner y
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) x (EuclideanSpace.single k 1) +
        g.metricInner x (EuclideanSpace.single k 1) (EuclideanSpace.single j 1) *
          deriv (fun t : ℝ => (PiLp.proj (p := 2) (β := fun _ : Idx => ℝ) k : E3 →L[ℝ] ℝ) (W (x + t • EuclideanSpace.single i 1))) 0 +
        g.metricInner x (EuclideanSpace.single i 1) (EuclideanSpace.single k 1) *
          deriv (fun t : ℝ => (PiLp.proj (p := 2) (β := fun _ : Idx => ℝ) k : E3 →L[ℝ] ℝ) (W (x + t • EuclideanSpace.single j 1))) 0) :=
/- SWARM_PROOF_BEGIN -/
by
  intro x i j
  obtain ⟨V, hV, hbr, hdir⟩ :=
    PoincareConjecture.ParallelImplementation.EuclideanCoordinateFields.exists_coordinate_fields
  let π : Idx → E3 →L[ℝ] ℝ := fun k =>
    PiLp.proj (p := 2) (β := fun _ : Idx => ℝ) k
  have hframe :=
    PoincareConjecture.ParallelImplementation.EuclideanFrameBracketDirection.frame_bracket_and_direction
      W V hV
  have hcoordfun :
      (fun y : E3 => g.metricInner y (V i y) (V j y)) =
        (fun y : E3 => g.metricInner y (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1)) := by
    funext y
    rw [hV i y, hV j y]
  have hdirection : W.dir (fun y : E3 => g.metricInner y
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) x =
      ∑ k : Idx, π k (W x) *
        fderiv ℝ (fun y : E3 => g.metricInner y (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1)) x (EuclideanSpace.single k 1) := by
    have h := hframe.2 (fun y : E3 => g.metricInner y (V i y) (V j y)) x
    rw [hcoordfun] at h
    simpa [π] using h
  have hML :=
    PoincareConjecture.ParallelImplementation.IntrinsicMetricLieBracketFormula.metric_lie_bracket_formula
      g W (V i) (V j) x
  have hbi := hframe.1 i x
  have hbj := hframe.1 j x
  have hML' :
      MorganTianLib.metricLieDerivativeAt g W x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
        W.dir (fun y : E3 => g.metricInner y (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1)) x +
          g.metricInner x
            (fderiv ℝ (fun y : E3 => (W y : E3)) x (EuclideanSpace.single i 1))
            (EuclideanSpace.single j 1) +
          g.metricInner x (EuclideanSpace.single i 1)
            (fderiv ℝ (fun y : E3 => (W y : E3)) x (EuclideanSpace.single j 1)) := by
    rw [hV i x, hV j x, hbi, hbj] at hML
    rw [hcoordfun] at hML
    rw [g.metricInner_neg_left, g.metricInner_neg_right,
      sub_neg_eq_add, sub_neg_eq_add] at hML
    exact hML
  have hWcont : ContDiff ℝ ∞ (W : E3 → E3) :=
    contMDiff_vectorSpace_iff_contDiff.mp W.smooth
  have hWdiff : Differentiable ℝ (W : E3 → E3) :=
    hWcont.differentiable (by simp)
  have hscalarCont (k : Idx) :
      ContDiff ℝ ∞ (fun y : E3 => π k (W y)) :=
    (π k).contDiff.comp hWcont
  have hscalarDiff (k : Idx) : DifferentiableAt ℝ
      (fun y : E3 => π k (W y)) x :=
    (hscalarCont k).differentiable (by simp) x
  have hprojection (k l : Idx) :
      fderiv ℝ (fun y : E3 => π k (W y)) x (EuclideanSpace.single l 1) =
        π k (fderiv ℝ (fun y : E3 => (W y : E3)) x (EuclideanSpace.single l 1)) := by
    change fderiv ℝ ((π k) ∘ (fun y : E3 => (W y : E3))) x
      (EuclideanSpace.single l 1) = _
    rw [fderiv_comp x (π k).differentiableAt (hWdiff x)]
    simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply]
  have hline (k l : Idx) :
      fderiv ℝ (fun y : E3 => π k (W y)) x (EuclideanSpace.single l 1) =
        deriv (fun t : ℝ => π k (W (x + t • EuclideanSpace.single l 1))) 0 := by
    exact PoincareConjecture.ParallelImplementation.ScalarCoordinateLineDerivative.fderiv_eq_coordinate_deriv
      (fun y : E3 => π k (W y)) x l (hscalarDiff k)
  have hcoordinate (k l : Idx) :
      π k (fderiv ℝ (fun y : E3 => (W y : E3)) x (EuclideanSpace.single l 1)) =
        deriv (fun t : ℝ => π k (W (x + t • EuclideanSpace.single l 1))) 0 := by
    calc
      π k (fderiv ℝ (fun y : E3 => (W y : E3)) x (EuclideanSpace.single l 1)) =
          fderiv ℝ (fun y : E3 => π k (W y)) x (EuclideanSpace.single l 1) :=
            (hprojection k l).symm
      _ = deriv (fun t : ℝ => π k (W (x + t • EuclideanSpace.single l 1))) 0 := hline k l
  have hpair (l m : Idx) :
      g.metricInner x
        (fderiv ℝ (fun y : E3 => (W y : E3)) x (EuclideanSpace.single l 1))
        (EuclideanSpace.single m 1) =
        ∑ k : Idx, g.metricInner x (EuclideanSpace.single k 1)
          (EuclideanSpace.single m 1) *
          deriv (fun t : ℝ => π k (W (x + t • EuclideanSpace.single l 1))) 0 := by
    have hrepr :
        fderiv ℝ (fun y : E3 => (W y : E3)) x (EuclideanSpace.single l 1) =
          ∑ k : Idx,
            π k (fderiv ℝ (fun y : E3 => (W y : E3)) x (EuclideanSpace.single l 1)) •
              EuclideanSpace.single k 1 := by
      simpa [π, PiLp.proj_apply] using
        ((EuclideanSpace.basisFun Idx ℝ).sum_repr
          (fderiv ℝ (fun y : E3 => (W y : E3)) x (EuclideanSpace.single l 1))).symm
    have hmetric (s : Finset Idx) :
        g.metricInner x
            (∑ k ∈ s, π k
              (fderiv ℝ (fun y : E3 => (W y : E3)) x (EuclideanSpace.single l 1)) •
                EuclideanSpace.single k 1)
            (EuclideanSpace.single m 1) =
          ∑ k ∈ s, π k
            (fderiv ℝ (fun y : E3 => (W y : E3)) x (EuclideanSpace.single l 1)) *
              g.metricInner x (EuclideanSpace.single k 1) (EuclideanSpace.single m 1) := by
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | @insert k s hk ih =>
          rw [Finset.sum_insert hk, Finset.sum_insert hk,
            g.metricInner_add_left, g.metricInner_smul_left, ih]
    calc
      g.metricInner x
          (fderiv ℝ (fun y : E3 => (W y : E3)) x (EuclideanSpace.single l 1))
          (EuclideanSpace.single m 1) =
          g.metricInner x
            (∑ k : Idx,
              π k (fderiv ℝ (fun y : E3 => (W y : E3)) x (EuclideanSpace.single l 1)) •
                EuclideanSpace.single k 1)
            (EuclideanSpace.single m 1) := by
        exact congrArg (fun v : E3 =>
          g.metricInner x v (EuclideanSpace.single m 1)) hrepr
      _ = ∑ k : Idx,
            π k (fderiv ℝ (fun y : E3 => (W y : E3)) x (EuclideanSpace.single l 1)) *
              g.metricInner x (EuclideanSpace.single k 1) (EuclideanSpace.single m 1) := by
        exact hmetric Finset.univ
      _ = ∑ k : Idx, g.metricInner x (EuclideanSpace.single k 1)
            (EuclideanSpace.single m 1) *
            deriv (fun t : ℝ => π k (W (x + t • EuclideanSpace.single l 1))) 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hcoordinate k l]
        ring
  have hpairRight (l m : Idx) :
      g.metricInner x (EuclideanSpace.single m 1)
          (fderiv ℝ (fun y : E3 => (W y : E3)) x (EuclideanSpace.single l 1)) =
        ∑ k : Idx, g.metricInner x (EuclideanSpace.single m 1)
          (EuclideanSpace.single k 1) *
          deriv (fun t : ℝ => π k (W (x + t • EuclideanSpace.single l 1))) 0 := by
    calc
      g.metricInner x (EuclideanSpace.single m 1)
          (fderiv ℝ (fun y : E3 => (W y : E3)) x (EuclideanSpace.single l 1)) =
          g.metricInner x
            (fderiv ℝ (fun y : E3 => (W y : E3)) x (EuclideanSpace.single l 1))
            (EuclideanSpace.single m 1) := g.metricInner_comm x _ _
      _ = _ := by rw [hpair l m]
      _ = ∑ k : Idx, g.metricInner x (EuclideanSpace.single m 1)
            (EuclideanSpace.single k 1) *
            deriv (fun t : ℝ => π k (W (x + t • EuclideanSpace.single l 1))) 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [g.metricInner_comm x (EuclideanSpace.single k 1) (EuclideanSpace.single m 1)]
  have hfinal := hML'
  rw [hdirection, hpair i j, hpairRight j i] at hfinal
  calc
    MorganTianLib.metricLieDerivativeAt g W x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
        (∑ k : Idx, π k (W x) *
          fderiv ℝ (fun y : E3 => g.metricInner y (EuclideanSpace.single i 1)
            (EuclideanSpace.single j 1)) x (EuclideanSpace.single k 1)) +
        (∑ k : Idx, g.metricInner x (EuclideanSpace.single k 1)
          (EuclideanSpace.single j 1) *
          deriv (fun t : ℝ => π k (W (x + t • EuclideanSpace.single i 1))) 0) +
        (∑ k : Idx, g.metricInner x (EuclideanSpace.single i 1)
          (EuclideanSpace.single k 1) *
          deriv (fun t : ℝ => π k (W (x + t • EuclideanSpace.single j 1))) 0) := hfinal
    _ = ∑ k : Idx,
        (π k (W x) * fderiv ℝ (fun y : E3 => g.metricInner y
            (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) x
              (EuclideanSpace.single k 1) +
          g.metricInner x (EuclideanSpace.single k 1) (EuclideanSpace.single j 1) *
            deriv (fun t : ℝ => π k (W (x + t • EuclideanSpace.single i 1))) 0 +
          g.metricInner x (EuclideanSpace.single i 1) (EuclideanSpace.single k 1) *
            deriv (fun t : ℝ => π k (W (x + t • EuclideanSpace.single j 1))) 0) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.EuclideanMetricLieCoordinates
