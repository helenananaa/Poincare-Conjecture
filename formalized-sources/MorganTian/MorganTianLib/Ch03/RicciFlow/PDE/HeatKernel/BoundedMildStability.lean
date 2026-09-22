import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedClassicalIVP
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedDuhamelNonlinearDifference
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelBoundedForcing
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideTranslationL1
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.GaussianNormForm
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Calculus.ParametricIntegral
open Set MeasureTheory Filter Function
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "HeatSpace" => (ℝ × E3) →ᵇ ℝ
/-- Quantitative dependence on the actual initial-heat field for mild solutions. -/
theorem bounded_mild_integral_stability (N : ℝ → ℝ) (L T : ℝ)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hLT : T*L < 1)
    (hN : ∀ a b : ℝ, |N a-N b| ≤ L*|a-b|)
    (a b u v : HeatSpace)
    (hu : ∀ p : ℝ × E3, u p = a p + ∫ s in (0:ℝ)..max 0 (min T p.1),
      ∫ y : E3, euclideanHeatKernel 3 (max 0 (min T p.1)-s) y * N (u (s,p.2-y)))
    (hv : ∀ p : ℝ × E3, v p = b p + ∫ s in (0:ℝ)..max 0 (min T p.1),
      ∫ y : E3, euclideanHeatKernel 3 (max 0 (min T p.1)-s) y * N (v (s,p.2-y))) :
    ‖u-v‖ ≤ ‖a-b‖/(1-T*L) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have hNlip : LipschitzWith L.toNNReal N :=
    LipschitzWith.of_dist_le_mul (fun x y => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal L hL]
      exact hN x y)
  have hNcont : Continuous N := hNlip.continuous
  let U : HeatSpace :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun p : ℝ × E3 => N (u p))
      (hNcont.comp u.continuous)
      (|N 0| + L * ‖u‖)
      (by
        intro p
        rw [Real.norm_eq_abs]
        calc
          |N (u p)| = |(N (u p) - N 0) + N 0| := by ring_nf
          _ ≤ |N (u p) - N 0| + |N 0| := abs_add_le _ _
          _ ≤ L * |u p - 0| + |N 0| :=
            by simpa [add_comm] using add_le_add_right (hN (u p) 0) |N 0|
          _ ≤ L * ‖u‖ + |N 0| := by
            gcongr
            simpa [Real.norm_eq_abs] using u.norm_coe_le_norm p
          _ = |N 0| + L * ‖u‖ := by ring)
  let V : HeatSpace :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun p : ℝ × E3 => N (v p))
      (hNcont.comp v.continuous)
      (|N 0| + L * ‖v‖)
      (by
        intro p
        rw [Real.norm_eq_abs]
        calc
          |N (v p)| = |(N (v p) - N 0) + N 0| := by ring_nf
          _ ≤ |N (v p) - N 0| + |N 0| := abs_add_le _ _
          _ ≤ L * |v p - 0| + |N 0| :=
            by simpa [add_comm] using add_le_add_right (hN (v p) 0) |N 0|
          _ ≤ L * ‖v‖ + |N 0| := by
            gcongr
            simpa [Real.norm_eq_abs] using v.norm_coe_le_norm p
          _ = |N 0| + L * ‖v‖ := by ring)
  have hpoint (p : ℝ × E3) :
      |(u - v) p| ≤ ‖a - b‖ + T * L * ‖u - v‖ := by
    let τ : ℝ := max 0 (min T p.1)
    have hτ : 0 ≤ τ := by positivity
    have hτT : τ ≤ T := max_le hT (min_le_left _ _)
    have hUint : IntervalIntegrable
        (fun s : ℝ => ∫ y : E3,
          euclideanHeatKernel 3 (τ-s) y * U (s,p.2-y)) volume 0 τ := by
      simpa [U] using
        (euclideanHeatKernel_three_bounded_duhamel U τ hτ p.2).1
    have hVint : IntervalIntegrable
        (fun s : ℝ => ∫ y : E3,
          euclideanHeatKernel 3 (τ-s) y * V (s,p.2-y)) volume 0 τ := by
      simpa [V] using
        (euclideanHeatKernel_three_bounded_duhamel V τ hτ p.2).1
    have hinner (s : ℝ) (hs : s ∈ uIoc (0 : ℝ) τ) (hsτ : s ≠ τ) :
        (∫ y : E3, euclideanHeatKernel 3 (τ-s) y * U (s,p.2-y)) -
          (∫ y : E3, euclideanHeatKernel 3 (τ-s) y * V (s,p.2-y)) =
        ∫ y : E3, euclideanHeatKernel 3 (τ-s) y *
          (N (u (s,p.2-y)) - N (v (s,p.2-y))) := by
      have hs' : s ∈ Ioc (0 : ℝ) τ := by
        rwa [uIoc_of_le hτ] at hs
      have hst : s < τ := lt_of_le_of_ne hs'.2 hsτ
      have hpos := (euclideanHeatKernel_mass_semigroup 3).1
        (τ-s) (sub_pos.mpr hst)
      have hmeasU : AEStronglyMeasurable
          (fun y : E3 => U (s,p.2-y)) volume := by fun_prop
      have hmeasV : AEStronglyMeasurable
          (fun y : E3 => V (s,p.2-y)) volume := by fun_prop
      have hintU : Integrable
          (fun y : E3 => euclideanHeatKernel 3 (τ-s) y * U (s,p.2-y)) volume :=
        hpos.1.mul_bdd hmeasU
          (Eventually.of_forall (fun y => U.norm_coe_le_norm (s,p.2-y)))
      have hintV : Integrable
          (fun y : E3 => euclideanHeatKernel 3 (τ-s) y * V (s,p.2-y)) volume :=
        hpos.1.mul_bdd hmeasV
          (Eventually.of_forall (fun y => V.norm_coe_le_norm (s,p.2-y)))
      rw [← integral_sub hintU hintV]
      congr 1
      funext y
      dsimp [U, V]
      ring
    have hdiffint : IntervalIntegrable
        (fun s : ℝ => ∫ y : E3, euclideanHeatKernel 3 (τ-s) y *
          (N (u (s,p.2-y)) - N (v (s,p.2-y)))) volume 0 τ := by
      exact (bounded_duhamel_nonlinear_difference N L hL hN u v τ hτ p.2).1
    have hsub :
        (∫ s in (0 : ℝ)..τ, ∫ y : E3,
          euclideanHeatKernel 3 (τ-s) y * U (s,p.2-y)) -
        (∫ s in (0 : ℝ)..τ, ∫ y : E3,
          euclideanHeatKernel 3 (τ-s) y * V (s,p.2-y)) =
        ∫ s in (0 : ℝ)..τ, ∫ y : E3, euclideanHeatKernel 3 (τ-s) y *
          (N (u (s,p.2-y)) - N (v (s,p.2-y)) ) := by
      rw [← intervalIntegral.integral_sub hUint hVint]
      apply intervalIntegral.integral_congr_ae
      filter_upwards [volume.ae_ne τ] with s hsτ hs
      exact hinner s hs hsτ
    have hduh := bounded_duhamel_nonlinear_difference N L hL hN u v τ hτ p.2
    have hτbound :
        |∫ s in (0 : ℝ)..τ, ∫ y : E3, euclideanHeatKernel 3 (τ-s) y *
          (N (u (s,p.2-y)) - N (v (s,p.2-y)))| ≤
          T * L * ‖u-v‖ := by
      calc
        _ ≤ τ * L * ‖u-v‖ := by simpa using hduh.2
        _ ≤ T * L * ‖u-v‖ := by
          gcongr
    have heq :
        (u - v) p = (a - b) p + ∫ s in (0 : ℝ)..τ, ∫ y : E3,
          euclideanHeatKernel 3 (τ-s) y *
            (N (u (s,p.2-y)) - N (v (s,p.2-y))) := by
      calc
        u p - v p = (a p - b p) +
            ((∫ s in (0 : ℝ)..τ, ∫ y : E3,
              euclideanHeatKernel 3 (τ-s) y * U (s,p.2-y)) -
            (∫ s in (0 : ℝ)..τ, ∫ y : E3,
              euclideanHeatKernel 3 (τ-s) y * V (s,p.2-y))) := by
          rw [hu p, hv p]
          dsimp [τ, U, V]
          ring
        _ = (a - b) p + ∫ s in (0 : ℝ)..τ, ∫ y : E3,
            euclideanHeatKernel 3 (τ-s) y *
              (N (u (s,p.2-y)) - N (v (s,p.2-y))) := by
          rw [hsub]
          rfl
    rw [heq]
    calc
      |(a - b) p + ∫ s in (0 : ℝ)..τ, ∫ y : E3,
          euclideanHeatKernel 3 (τ-s) y *
            (N (u (s,p.2-y)) - N (v (s,p.2-y)))| ≤
          |(a-b) p| + |∫ s in (0 : ℝ)..τ, ∫ y : E3,
            euclideanHeatKernel 3 (τ-s) y *
            (N (u (s,p.2-y)) - N (v (s,p.2-y)))| := abs_add_le _ _
      _ ≤ ‖a-b‖ + T * L * ‖u-v‖ := by
        gcongr
        · simpa [Real.norm_eq_abs] using (a-b).norm_coe_le_norm p
  have hnorm : ‖u-v‖ ≤ ‖a-b‖ + T * L * ‖u-v‖ := by
    have hC : 0 ≤ ‖a-b‖ + T * L * ‖u-v‖ :=
      add_nonneg (norm_nonneg _) (mul_nonneg (mul_nonneg hT hL) (norm_nonneg _))
    apply (BoundedContinuousFunction.norm_le (f := u-v)
      (C := ‖a-b‖ + T * L * ‖u-v‖) hC).2
    intro p
    simpa [Real.norm_eq_abs] using hpoint p
  have hden : 0 < 1 - T * L := sub_pos.mpr hLT
  apply (le_div_iff₀ hden).2
  nlinarith
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
