import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.FixedDomainDuhamel
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
/-- Construct the actual bounded continuous Duhamel operator, not an assumed map. -/
theorem clipped_duhamel_operator (T : ℝ) (hT : 0 ≤ T) :
    ∃ D : HeatSpace → HeatSpace,
      (∀ F p, D F p = ∫ s in (0:ℝ)..max 0 (min T p.1),
        ∫ y : E3, euclideanHeatKernel 3 (max 0 (min T p.1)-s) y * F (s,p.2-y)) ∧
      (∀ F, ‖D F‖ ≤ T*‖F‖) ∧ ∀ F G, ‖D F-D G‖ ≤ T*‖F-G‖ :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let τ : ℝ × E3 → ℝ := fun p => max 0 (min T p.1)
  have hτcont : Continuous τ := by
    dsimp [τ]
    fun_prop
  have hτnonneg (p : ℝ × E3) : 0 ≤ τ p := by
    dsimp [τ]
    positivity
  have hτle (p : ℝ × E3) : τ p ≤ T := by
    dsimp [τ]
    exact max_le hT (min_le_left _ _)
  let K : E3 → ℝ := euclideanHeatKernel 3 1
  obtain ⟨hKint, hKmass⟩ := (euclideanHeatKernel_mass_semigroup 3).1 1 (by norm_num)
  have hKpos (z : E3) : 0 ≤ K z := by
    dsimp [K]
    exact (euclideanHeatKernel_pos 3 (by norm_num) z).le
  have hKcont : Continuous K := by
    dsimp [K]
    exact (euclideanHeatKernel_three_heat_equation (by norm_num)).1.continuous
  let Φ : HeatSpace → (ℝ × E3) → ℝ → E3 → ℝ := fun F p r z =>
    K z * F (τ p * r, p.2 - (Real.sqrt (τ p * (1-r))) • z)
  have hΦmeas (F : HeatSpace) (p : ℝ × E3) (r : ℝ) :
      AEStronglyMeasurable (Φ F p r) volume := by
    have harg : Continuous (fun z : E3 =>
        (τ p * r, p.2 - (Real.sqrt (τ p * (1-r))) • z)) := by
      fun_prop
    dsimp [Φ]
    exact (hKcont.mul (F.continuous.comp harg)).aestronglyMeasurable
  have hΦint (F : HeatSpace) (p : ℝ × E3) (r : ℝ) :
      Integrable (Φ F p r) volume := by
    have harg : Continuous (fun z : E3 =>
        (τ p * r, p.2 - (Real.sqrt (τ p * (1-r))) • z)) := by
      fun_prop
    have hargmeas : AEStronglyMeasurable (fun z : E3 =>
        F (τ p * r, p.2 - (Real.sqrt (τ p * (1-r))) • z)) volume :=
      (F.continuous.comp harg).aestronglyMeasurable
    simpa [Φ, K] using hKint.mul_bdd hargmeas
      (Eventually.of_forall (fun z =>
        F.norm_coe_le_norm (τ p * r, p.2 - (Real.sqrt (τ p * (1-r))) • z)))
  have hΦbound (F : HeatSpace) (p : ℝ × E3) (r : ℝ) :
      ∀ᵐ z ∂volume, ‖Φ F p r z‖ ≤ K z * ‖F‖ := by
    filter_upwards [] with z
    dsimp [Φ]
    rw [abs_mul, abs_of_nonneg (hKpos z)]
    exact mul_le_mul_of_nonneg_left
      (F.norm_coe_le_norm (τ p * r, p.2 - (Real.sqrt (τ p * (1-r))) • z))
      (hKpos z)
  have hΦcont_p (F : HeatSpace) (r : ℝ) (z : E3) :
      Continuous (fun p : ℝ × E3 => Φ F p r z) := by
    have hs : Continuous (fun p : ℝ × E3 =>
        Real.sqrt (τ p * (1-r))) := by
      exact Real.continuous_sqrt.comp (hτcont.mul continuous_const)
    have harg : Continuous (fun p : ℝ × E3 =>
        (τ p * r, p.2 - (Real.sqrt (τ p * (1-r))) • z)) := by
      exact (hτcont.mul continuous_const).prodMk
        (continuous_snd.sub (hs.smul continuous_const))
    exact continuous_const.mul (F.continuous.comp harg)
  have hΦcont_r (F : HeatSpace) (p : ℝ × E3) (z : E3) :
      Continuous (fun r : ℝ => Φ F p r z) := by
    have hs : Continuous (fun r : ℝ =>
        Real.sqrt (τ p * (1-r))) := by
      exact Real.continuous_sqrt.comp (continuous_const.mul (continuous_const.sub continuous_id))
    have harg : Continuous (fun r : ℝ =>
        (τ p * r, p.2 - (Real.sqrt (τ p * (1-r))) • z)) := by
      exact (continuous_const.mul continuous_id).prodMk
        (continuous_const.sub (hs.smul continuous_const))
    exact continuous_const.mul (F.continuous.comp harg)
  let I : HeatSpace → (ℝ × E3) → ℝ → ℝ := fun F p r => ∫ z : E3, Φ F p r z
  have hIcont_p (F : HeatSpace) (r : ℝ) :
      Continuous (fun p : ℝ × E3 => I F p r) := by
    apply continuous_of_dominated (bound := fun z : E3 => K z * ‖F‖)
    · intro p
      exact hΦmeas F p r
    · intro p
      exact hΦbound F p r
    · exact hKint.mul_const ‖F‖
    · filter_upwards [] with z
      exact hΦcont_p F r z
  have hIcont_r (F : HeatSpace) (p : ℝ × E3) :
      Continuous (fun r : ℝ => I F p r) := by
    apply continuous_of_dominated (bound := fun z : E3 => K z * ‖F‖)
    · intro r
      exact hΦmeas F p r
    · intro r
      exact hΦbound F p r
    · exact hKint.mul_const ‖F‖
    · filter_upwards [] with z
      exact hΦcont_r F p z
  have hIbound (F : HeatSpace) (p : ℝ × E3) (r : ℝ) :
      ‖I F p r‖ ≤ ‖F‖ := by
    have hi : ‖I F p r‖ ≤ ∫ z : E3, K z * ‖F‖ := by
      change ‖∫ z : E3, Φ F p r z‖ ≤ _
      refine norm_integral_le_of_norm_le (hKint.mul_const ‖F‖) ?_
      exact hΦbound F p r
    rw [integral_mul_const, hKmass, one_mul] at hi
    exact hi
  have hJcont (F : HeatSpace) :
      Continuous (fun p : ℝ × E3 => ∫ r in (0 : ℝ)..1, I F p r) := by
    apply intervalIntegral.continuous_of_dominated_interval
    · intro p
      exact (hIcont_r F p).aestronglyMeasurable
    · intro p
      filter_upwards [] with r hr
      exact hIbound F p r
    · exact intervalIntegrable_const
    · filter_upwards [] with r hr
      exact (hIcont_p F r)
  have hAcont (F : HeatSpace) :
      Continuous (fun p : ℝ × E3 => τ p * ∫ r in (0 : ℝ)..1, I F p r) :=
    hτcont.mul (hJcont F)
  have hAbound (F : HeatSpace) (p : ℝ × E3) :
      ‖τ p * ∫ r in (0 : ℝ)..1, I F p r‖ ≤ T * ‖F‖ := by
    have hJ : ‖∫ r in (0 : ℝ)..1, I F p r‖ ≤ ‖F‖ := by
      have h := intervalIntegral.norm_integral_le_of_norm_le
        (show (0 : ℝ) ≤ 1 by norm_num)
        (Filter.Eventually.of_forall (fun r hr => hIbound F p r))
        (intervalIntegrable_const :
          IntervalIntegrable (fun _ : ℝ => ‖F‖) volume 0 1)
      simpa using h
    calc
      ‖τ p * ∫ r in (0 : ℝ)..1, I F p r‖ =
          τ p * ‖∫ r in (0 : ℝ)..1, I F p r‖ := by
            rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hτnonneg p)]
      _ ≤ τ p * ‖F‖ := mul_le_mul_of_nonneg_left hJ (hτnonneg p)
      _ ≤ T * ‖F‖ := mul_le_mul_of_nonneg_right (hτle p) (norm_nonneg _)
  let D : HeatSpace → HeatSpace := fun F =>
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun p : ℝ × E3 => τ p * ∫ r in (0 : ℝ)..1, I F p r)
      (hAcont F) (T * ‖F‖) (hAbound F)
  have hI_sub (F G : HeatSpace) (p : ℝ × E3) (r : ℝ) :
      I (F-G) p r = I F p r - I G p r := by
    rw [show I (F-G) p r = ∫ z : E3, Φ (F-G) p r z by rfl]
    rw [show I F p r = ∫ z : E3, Φ F p r z by rfl]
    rw [show I G p r = ∫ z : E3, Φ G p r z by rfl]
    rw [← integral_sub (hΦint F p r) (hΦint G p r)]
    congr 1
    funext z
    simp [Φ]
    ring
  have hJ_sub (F G : HeatSpace) (p : ℝ × E3) :
      (∫ r in (0 : ℝ)..1, I (F-G) p r) =
        (∫ r in (0 : ℝ)..1, I F p r) - ∫ r in (0 : ℝ)..1, I G p r := by
    rw [intervalIntegral.integral_congr (fun r hr => hI_sub F G p r)]
    exact intervalIntegral.integral_sub
      ((hIcont_r F p).intervalIntegrable 0 1)
      ((hIcont_r G p).intervalIntegrable 0 1)
  have hD_sub (F G : HeatSpace) : D F - D G = D (F-G) := by
    ext p
    dsimp [D]
    rw [hJ_sub F G p]
    ring
  refine ⟨D, ?_, ?_, ?_⟩
  · intro F p
    simpa [D, I, Φ, τ] using
      (duhamel_fixed_domain_formula F (τ p) (hτnonneg p) p.2).symm
  · intro F
    exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
      (hAcont F) (mul_nonneg hT (norm_nonneg _)) (hAbound F)
  · intro F G
    rw [hD_sub]
    exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
      (hAcont (F-G)) (mul_nonneg hT (norm_nonneg _)) (hAbound (F-G))
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
