import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ActualCoordinateRicci
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoefficientConnectionDifferentiable
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CurvatureCoordinateComponents
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.MetricJetGermSymmetry
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LocalMetricCoercivity
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** actual ricci eq curvature trace. -/
theorem actual_ricci_eq_curvature_trace (G : E3 → (E3 →L[ℝ] E3)) (x : E3) (hG : ContDiffAt ℝ 2 G x)
    (hsym : ∀ᶠ y : E3 in 𝓝 x, ∀ v w : E3, inner ℝ (G y v) w = inner ℝ v (G y w))
    (c : ℝ) (hc : 0 < c) (hpos : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (G x v) v)
    (i j : Fin 3) :
    let Γ := fun y : E3 => coefficientConnectionBilin (G y)
      (fun r : Fin 3 => fderiv ℝ G y (EuclideanSpace.single r 1));
    actualCoordinateRicci G x i j = ∑ k : Fin 3,
      (MorganTianLib.christoffelCurvature Γ x (EuclideanSpace.single k 1)
        (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)) k :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let P : E3 → Fin 3 → E3 →L[ℝ] E3 := fun y r =>
    fderiv ℝ G y (EuclideanSpace.single r 1)
  let Γ : E3 → E3 →L[ℝ] E3 →L[ℝ] E3 := fun y =>
    coefficientConnectionBilin (G y) (P y)
  let χ : E3 → Fin 3 → Fin 3 → Fin 3 → ℝ := fun y k a b =>
    coordinateChristoffel (G y) (P y) k a b
  have hG1 : ∀ᶠ y : E3 in 𝓝 x, ContDiffAt ℝ 1 G y := by
    filter_upwards [hG.eventually (by simp)] with y hy
    exact hy.of_le (by norm_num)
  have hcoercive := metric_coercive_eventually G x hG.continuousAt c hc hpos
  have hsym_near : ∀ᶠ y : E3 in 𝓝 x,
      ∀ᶠ z : E3 in 𝓝 y, ∀ v w : E3,
        inner ℝ (G z v) w = inner ℝ v (G z w) := by
    simpa only [eventually_eventually_nhds] using hsym
  have htorsion : ∀ᶠ y : E3 in 𝓝 x, ∀ k i j : Fin 3,
      χ y k i j = χ y k j i := by
    filter_upwards [hG1, hcoercive, hsym_near] with y hyG hypos hysym
    have hGy : DifferentiableAt ℝ G y :=
      hyG.differentiableAt (by norm_num)
    have hjet := metric_jet_selfadjoint_of_eventually G y hGy hysym
    have hysym_at : ∀ v w : E3,
        inner ℝ (G y v) w = inner ℝ v (G y w) := hysym.self_of_nhds
    exact (coordinate_metric_compatibility (G y) (c / 2) (half_pos hc) hypos
      hysym_at (P y) (fun r v w => hjet (EuclideanSpace.single r 1) v w)).1
  have htorsion_x := htorsion.self_of_nhds
  have hchi_eq (k i j : Fin 3) :
      (fun y : E3 => χ y k i j) =ᶠ[𝓝 x] (fun y => χ y k j i) := by
    filter_upwards [htorsion] with y hy
    exact hy k i j
  have hchi_deriv (k i j : Fin 3) (d : E3) :
      fderiv ℝ (fun y : E3 => χ y k i j) x d =
        fderiv ℝ (fun y => χ y k j i) x d := by
    have heq : fderiv ℝ (fun y : E3 => χ y k i j) x =
        fderiv ℝ (fun y : E3 => χ y k j i) x :=
      (hchi_eq k i j).fderiv_eq
    exact congrArg (fun L : E3 →L[ℝ] ℝ => L d) heq
  have hΓdiff : DifferentiableAt ℝ Γ x := by
    dsimp [Γ, P]
    exact coefficient_connection_differentiable G x hG c hc hpos
  have hcoeff (y : E3) (a b q : Fin 3) :
      (Γ y (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)) q =
        χ y q a b := by
    dsimp [Γ, P, χ]
    rw [coefficient_connection_bilin_apply]
    simp [connectionVector]
  have hΓderiv (a b q : Fin 3) (d : E3) :
      fderiv ℝ (fun y : E3 => (Γ y (EuclideanSpace.single a 1)
        (EuclideanSpace.single b 1)) q) x d =
        fderiv ℝ (fun y => χ y q a b) x d := by
    have hf : (fun y : E3 => (Γ y (EuclideanSpace.single a 1)
        (EuclideanSpace.single b 1)) q) = fun y => χ y q a b := by
      funext y
      exact hcoeff y a b q
    rw [hf]
  have hfirst (k : Fin 3) :
      fderiv ℝ (fun y : E3 => coordinateChristoffel (G y)
        (fun a : Fin 3 => fderiv ℝ G y (EuclideanSpace.single a 1)) k i j)
          x (EuclideanSpace.single k 1) =
        fderiv ℝ (fun y => (Γ y (EuclideanSpace.single j 1)
          (EuclideanSpace.single i 1)) k) x (EuclideanSpace.single k 1) := by
    have hfun : (fun y : E3 => coordinateChristoffel (G y)
        (fun a : Fin 3 => fderiv ℝ G y (EuclideanSpace.single a 1)) k i j) =
        fun y => χ y k i j := by
      funext y
      rfl
    calc
      _ = fderiv ℝ (fun y => χ y k i j) x (EuclideanSpace.single k 1) := by
        rw [hfun]
      _ = fderiv ℝ (fun y => χ y k j i) x (EuclideanSpace.single k 1) :=
        hchi_deriv k i j (EuclideanSpace.single k 1)
      _ = fderiv ℝ (fun y => (Γ y (EuclideanSpace.single j 1)
          (EuclideanSpace.single i 1)) k) x (EuclideanSpace.single k 1) :=
        (hΓderiv j i k (EuclideanSpace.single k 1)).symm
  have hsecond (k : Fin 3) :
      fderiv ℝ (fun y : E3 => coordinateChristoffel (G y)
        (fun a : Fin 3 => fderiv ℝ G y (EuclideanSpace.single a 1)) k i k)
          x (EuclideanSpace.single j 1) =
        fderiv ℝ (fun y => (Γ y (EuclideanSpace.single k 1)
          (EuclideanSpace.single i 1)) k) x (EuclideanSpace.single j 1) := by
    have hfun : (fun y : E3 => coordinateChristoffel (G y)
        (fun a : Fin 3 => fderiv ℝ G y (EuclideanSpace.single a 1)) k i k) =
        fun y => χ y k i k := by
      funext y
      rfl
    calc
      _ = fderiv ℝ (fun y => χ y k i k) x (EuclideanSpace.single j 1) := by
        rw [hfun]
      _ = fderiv ℝ (fun y => χ y k k i) x (EuclideanSpace.single j 1) :=
        hchi_deriv k i k (EuclideanSpace.single j 1)
      _ = fderiv ℝ (fun y => (Γ y (EuclideanSpace.single k 1)
          (EuclideanSpace.single i 1)) k) x (EuclideanSpace.single j 1) :=
        (hΓderiv k i k (EuclideanSpace.single j 1)).symm
  have hquad : quadraticRicciProduct (G x) (P x) i j =
      ∑ k : Fin 3, ∑ m : Fin 3,
        ((Γ x (EuclideanSpace.single k 1) (EuclideanSpace.single m 1)) k *
            (Γ x (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)) m -
          (Γ x (EuclideanSpace.single j 1) (EuclideanSpace.single m 1)) k *
            (Γ x (EuclideanSpace.single k 1) (EuclideanSpace.single i 1)) m) := by
    unfold quadraticRicciProduct
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro m hm
    rw [hcoeff x k m k, hcoeff x j i m, htorsion_x m j i,
      hcoeff x j m k, hcoeff x k i m, htorsion_x m k i]
  change actualCoordinateRicci G x i j =
    ∑ k : Fin 3, christoffelCurvature Γ x
      (EuclideanSpace.single k 1) (EuclideanSpace.single j 1)
      (EuclideanSpace.single i 1) k
  calc
    actualCoordinateRicci G x i j =
        (∑ k : Fin 3,
          (fderiv ℝ (fun y : E3 => (Γ y (EuclideanSpace.single j 1)
              (EuclideanSpace.single i 1)) k) x (EuclideanSpace.single k 1) -
            fderiv ℝ (fun y : E3 => (Γ y (EuclideanSpace.single k 1)
              (EuclideanSpace.single i 1)) k) x (EuclideanSpace.single j 1))) +
          quadraticRicciProduct (G x) (P x) i j := by
      unfold actualCoordinateRicci
      apply congrArg (fun z : ℝ => z + quadraticRicciProduct (G x) (P x) i j)
      apply Finset.sum_congr rfl
      intro k hk
      rw [hfirst k, hsecond k]
    _ = ∑ k : Fin 3,
        ((fderiv ℝ (fun y : E3 => (Γ y (EuclideanSpace.single j 1)
            (EuclideanSpace.single i 1)) k) x (EuclideanSpace.single k 1) -
          fderiv ℝ (fun y : E3 => (Γ y (EuclideanSpace.single k 1)
            (EuclideanSpace.single i 1)) k) x (EuclideanSpace.single j 1)) +
          ∑ m : Fin 3,
            ((Γ x (EuclideanSpace.single k 1) (EuclideanSpace.single m 1)) k *
                (Γ x (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)) m -
              (Γ x (EuclideanSpace.single j 1) (EuclideanSpace.single m 1)) k *
                (Γ x (EuclideanSpace.single k 1) (EuclideanSpace.single i 1)) m)) := by
      rw [hquad, ← Finset.sum_add_distrib]
    _ = ∑ k : Fin 3, christoffelCurvature Γ x
        (EuclideanSpace.single k 1) (EuclideanSpace.single j 1)
        (EuclideanSpace.single i 1) k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [curvature_coordinate_components Γ x hΓdiff k j i k]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
