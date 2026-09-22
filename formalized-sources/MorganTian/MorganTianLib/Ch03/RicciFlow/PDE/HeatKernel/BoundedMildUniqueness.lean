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
/-- Uniqueness for the actual clipped-time semilinear integral equation. -/
theorem bounded_mild_integral_unique (N : ℝ → ℝ) (L T : ℝ)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hLT : T*L < 1)
    (hN : ∀ a b : ℝ, |N a-N b| ≤ L*|a-b|)
    (seed u v : HeatSpace)
    (hu : ∀ p : ℝ × E3, u p = seed p + ∫ s in (0:ℝ)..max 0 (min T p.1),
      ∫ y : E3, euclideanHeatKernel 3 (max 0 (min T p.1)-s) y * N (u (s,p.2-y)))
    (hv : ∀ p : ℝ × E3, v p = seed p + ∫ s in (0:ℝ)..max 0 (min T p.1),
      ∫ y : E3, euclideanHeatKernel 3 (max 0 (min T p.1)-s) y * N (v (s,p.2-y))) : u = v :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have hNlip : LipschitzWith L.toNNReal N :=
    LipschitzWith.of_dist_le_mul (fun a b => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal L hL]
      exact hN a b)
  have hNcont : Continuous N := hNlip.continuous
  let Cu : ℝ := |N 0| + L * ‖u‖
  let Cv : ℝ := |N 0| + L * ‖v‖
  have hCu : 0 ≤ Cu := by
    dsimp [Cu]
    positivity
  have hCv : 0 ≤ Cv := by
    dsimp [Cv]
    positivity
  have hNucont : Continuous (fun p : ℝ × E3 => N (u p)) :=
    hNcont.comp u.continuous
  have hNvcont : Continuous (fun p : ℝ × E3 => N (v p)) :=
    hNcont.comp v.continuous
  have hNubound : ∀ p : ℝ × E3, ‖N (u p)‖ ≤ Cu := by
    intro p
    rw [Real.norm_eq_abs]
    calc
      |N (u p)| = |(N (u p) - N 0) + N 0| := by rw [sub_add_cancel]
      _ ≤ |N (u p) - N 0| + |N 0| := abs_add_le _ _
      _ ≤ L * |u p - 0| + |N 0| := by
        exact add_le_add (hN (u p) 0) (le_refl _)
      _ ≤ L * ‖u‖ + |N 0| := by
        have hp : |u p - 0| ≤ ‖u‖ := by
          simpa [Real.norm_eq_abs] using u.norm_coe_le_norm p
        exact add_le_add (mul_le_mul_of_nonneg_left hp hL) (le_refl _)
      _ = Cu := by
        dsimp [Cu]
        ring
  have hNvbound : ∀ p : ℝ × E3, ‖N (v p)‖ ≤ Cv := by
    intro p
    rw [Real.norm_eq_abs]
    calc
      |N (v p)| = |(N (v p) - N 0) + N 0| := by rw [sub_add_cancel]
      _ ≤ |N (v p) - N 0| + |N 0| := abs_add_le _ _
      _ ≤ L * |v p - 0| + |N 0| := by
        exact add_le_add (hN (v p) 0) (le_refl _)
      _ ≤ L * ‖v‖ + |N 0| := by
        have hp : |v p - 0| ≤ ‖v‖ := by
          simpa [Real.norm_eq_abs] using v.norm_coe_le_norm p
        exact add_le_add (mul_le_mul_of_nonneg_left hp hL) (le_refl _)
      _ = Cv := by
        dsimp [Cv]
        ring
  let Nu : HeatSpace :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun p : ℝ × E3 => N (u p)) hNucont Cu hNubound
  let Nv : HeatSpace :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun p : ℝ × E3 => N (v p)) hNvcont Cv hNvbound
  have hpoint : ∀ p : ℝ × E3,
      |u p - v p| ≤ max 0 (min T p.1) * L * ‖u - v‖ := by
    intro p
    let τ : ℝ := max 0 (min T p.1)
    have hτ : 0 ≤ τ := by
      dsimp [τ]
      positivity
    have hτT : τ ≤ T := by
      dsimp [τ]
      exact max_le hT (min_le_left _ _)
    have hU := euclideanHeatKernel_three_bounded_duhamel Nu τ hτ p.2
    have hV := euclideanHeatKernel_three_bounded_duhamel Nv τ hτ p.2
    have hUint : IntervalIntegrable
        (fun s => ∫ y : E3, euclideanHeatKernel 3 (τ-s) y * N (u (s,p.2-y)))
        volume 0 τ := by
      simpa [Nu] using hU.1
    have hVint : IntervalIntegrable
        (fun s => ∫ y : E3, euclideanHeatKernel 3 (τ-s) y * N (v (s,p.2-y)))
        volume 0 τ := by
      simpa [Nv] using hV.1
    have hinnerU : ∀ᵐ s ∂volume, s ∈ Ioc (0 : ℝ) τ →
        Integrable (fun y : E3 => euclideanHeatKernel 3 (τ-s) y * N (u (s,p.2-y)))
          volume := by
      filter_upwards [volume.ae_ne τ] with s hs hst
      have hslt : s < τ := lt_of_le_of_ne hst.2 hs
      have hts : 0 < τ - s := sub_pos.mpr hslt
      have hpos := (euclideanHeatKernel_mass_semigroup 3).1 (τ - s) hts
      have hmeas : AEStronglyMeasurable (fun y : E3 => N (u (s,p.2-y))) volume := by
        fun_prop
      apply hpos.1.mul_bdd hmeas
      exact Eventually.of_forall (fun y => hNubound (s,p.2-y))
    have hinnerV : ∀ᵐ s ∂volume, s ∈ Ioc (0 : ℝ) τ →
        Integrable (fun y : E3 => euclideanHeatKernel 3 (τ-s) y * N (v (s,p.2-y)))
          volume := by
      filter_upwards [volume.ae_ne τ] with s hs hst
      have hslt : s < τ := lt_of_le_of_ne hst.2 hs
      have hts : 0 < τ - s := sub_pos.mpr hslt
      have hpos := (euclideanHeatKernel_mass_semigroup 3).1 (τ - s) hts
      have hmeas : AEStronglyMeasurable (fun y : E3 => N (v (s,p.2-y))) volume := by
        fun_prop
      apply hpos.1.mul_bdd hmeas
      exact Eventually.of_forall (fun y => hNvbound (s,p.2-y))
    have hinner_sub :
        (fun s => ∫ y : E3, euclideanHeatKernel 3 (τ-s) y *
          (N (u (s,p.2-y))-N (v (s,p.2-y)))) =ᵐ[volume.restrict (uIoc (0 : ℝ) τ)]
        (fun s => (∫ y : E3, euclideanHeatKernel 3 (τ-s) y * N (u (s,p.2-y))) -
          ∫ y : E3, euclideanHeatKernel 3 (τ-s) y * N (v (s,p.2-y))) := by
      rw [uIoc_of_le hτ]
      filter_upwards [(ae_restrict_iff' measurableSet_Ioc).2 hinnerU,
        (ae_restrict_iff' measurableSet_Ioc).2 hinnerV] with s hUs hVs
      rw [← integral_sub hUs hVs]
      congr 1
      funext y
      ring
    have hu' : u p = seed p + ∫ s in (0:ℝ)..τ,
        ∫ y : E3, euclideanHeatKernel 3 (τ-s) y * N (u (s,p.2-y)) := by
      simpa [τ] using hu p
    have hv' : v p = seed p + ∫ s in (0:ℝ)..τ,
        ∫ y : E3, euclideanHeatKernel 3 (τ-s) y * N (v (s,p.2-y)) := by
      simpa [τ] using hv p
    have hdiff := bounded_duhamel_nonlinear_difference N L hL hN u v τ hτ p.2
    have heq : u p - v p = ∫ s in (0:ℝ)..τ,
        ∫ y : E3, euclideanHeatKernel 3 (τ-s) y *
          (N (u (s,p.2-y))-N (v (s,p.2-y))) := by
      rw [hu', hv']
      rw [intervalIntegral.integral_congr_ae_restrict hinner_sub]
      rw [intervalIntegral.integral_sub hUint hVint]
      ring
    have hτbound :
        τ * L * ‖u - v‖ ≤ T * L * ‖u - v‖ := by
      gcongr
    rw [heq]
    simpa [τ] using hdiff.2
  have hnorm : ‖u - v‖ ≤ T * L * ‖u - v‖ := by
    apply (BoundedContinuousFunction.norm_le
      (mul_nonneg (mul_nonneg hT hL) (norm_nonneg _))).2
    intro p
    rw [Real.norm_eq_abs]
    have hmax : max 0 (min T p.1) ≤ T := max_le hT (min_le_left _ _)
    have hcoef : max 0 (min T p.1) * L * ‖u - v‖ ≤ T * L * ‖u - v‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hmax hL) (norm_nonneg _)
    exact (hpoint p).trans hcoef
  have hnormzero : ‖u - v‖ = 0 := by
    by_contra hnz
    have hpos : 0 < ‖u - v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnz)
    have hstrict : T * L * ‖u - v‖ < ‖u - v‖ := by
      simpa using (mul_lt_mul_of_pos_right hLT hpos)
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hnormzero)
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
