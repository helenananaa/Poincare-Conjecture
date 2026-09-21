import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanSemigroup
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ThreeDimensionalEquation
import Mathlib.Analysis.Calculus.ContDiff.Convolution
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** Actual heat convolution is a contraction linear operator on bounded continuous data. -/
theorem exists_three_dimensional_bounded_heat_operator :
    ∃ A : ℝ → ((E3 →ᵇ ℝ) →L[ℝ] (E3 →ᵇ ℝ)), ∀ t : ℝ, 0 < t →
      ‖A t‖ ≤ 1 ∧ ∀ (f : E3 →ᵇ ℝ) (x : E3),
        Integrable (fun y : E3 => euclideanHeatKernel 3 t y * f (x - y)) volume ∧
        A t f x = ∫ y : E3, euclideanHeatKernel 3 t y * f (x - y) := by
/- SWARM_PROOF_BEGIN -/
  classical
  let E : Type := E3 →ᵇ ℝ
  let k : ℝ → E3 → ℝ := fun s => euclideanHeatKernel 3 s
  have hpos (s : ℝ) (hs : 0 < s) :
      Integrable (k s) volume ∧ (∫ y : E3, k s y) = 1 := by
    simpa [k] using (euclideanHeatKernel_mass_semigroup 3).1 s hs
  have hcont (s : ℝ) (hs : 0 < s) : Continuous (k s) := by
    simpa [k] using (euclideanHeatKernel_three_heat_equation hs).1.continuous
  have hInt (s : ℝ) (hs : 0 < s) (f : E) (x : E3) :
      Integrable (fun y : E3 => k s y * f (x - y)) volume := by
    have hmeas : AEStronglyMeasurable (fun y : E3 => f (x - y)) volume := by
      fun_prop
    apply (hpos s hs).1.mul_bdd hmeas
    exact Eventually.of_forall (fun y => f.norm_coe_le_norm (x - y))
  have hconv_cont (s : ℝ) (hs : 0 < s) (f : E) :
      Continuous (fun x : E3 => ∫ y : E3, k s y * f (x - y)) := by
    have hbg : BddAbove (Set.range (fun y : E3 => ‖f y‖)) := by
      simpa [Function.comp_def] using f.bddAbove_range_norm_comp
    change Continuous
      (MeasureTheory.convolution (k s) (f : E3 → ℝ)
        (ContinuousLinearMap.mul ℝ ℝ) (volume : Measure E3))
    exact hbg.continuous_convolution_right_of_integrable
      (L := ContinuousLinearMap.mul ℝ ℝ) (μ := (volume : Measure E3))
      (hpos s hs).1 f.continuous
  have hbound (s : ℝ) (hs : 0 < s) (f : E) (x : E3) :
      ‖∫ y : E3, k s y * f (x - y)‖ ≤ ‖f‖ := by
    calc
      ‖∫ y : E3, k s y * f (x - y)‖ ≤
          ∫ y : E3, k s y * ‖f‖ := by
        apply norm_integral_le_of_norm_le ((hpos s hs).1.mul_const ‖f‖)
        filter_upwards [] with y
        have hky : 0 ≤ k s y := by
          simpa [k] using (euclideanHeatKernel_pos 3 hs y).le
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hky]
        gcongr
        exact f.norm_coe_le_norm (x - y)
      _ = ‖f‖ := by
        rw [integral_mul_const, (hpos s hs).2, one_mul]
  let out (s : ℝ) (hs : 0 < s) (f : E) : E :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x : E3 => ∫ y : E3, k s y * f (x - y))
      (hconv_cont s hs f) ‖f‖ (hbound s hs f)
  have hout_add (s : ℝ) (hs : 0 < s) (f g : E) :
      out s hs (f + g) = out s hs f + out s hs g := by
    apply BoundedContinuousFunction.ext
    intro x
    change (∫ y : E3, k s y * (f + g) (x - y)) =
      (∫ y : E3, k s y * f (x - y)) +
        ∫ y : E3, k s y * g (x - y)
    rw [show (fun y : E3 => k s y * (f + g) (x - y)) =
        (fun y => k s y * f (x - y)) + (fun y => k s y * g (x - y)) by
          funext y
          rw [BoundedContinuousFunction.add_apply]
          simp only [Pi.add_apply]
          rw [mul_add]]
    exact integral_add (hInt s hs f x) (hInt s hs g x)
  have hout_smul (s : ℝ) (hs : 0 < s) (c : ℝ) (f : E) :
      out s hs (c • f) = c • out s hs f := by
    apply BoundedContinuousFunction.ext
    intro x
    change (∫ y : E3, k s y * (c • f) (x - y)) =
      c • ∫ y : E3, k s y * f (x - y)
    calc
      (∫ y : E3, k s y * (c • f) (x - y)) =
          ∫ y : E3, c • (k s y * f (x - y)) := by
        congr 1
        funext y
        rw [BoundedContinuousFunction.smul_apply]
        ring
      _ = c • ∫ y : E3, k s y * f (x - y) := integral_smul c _
  let lin (s : ℝ) (hs : 0 < s) : E →ₗ[ℝ] E :=
    { toFun := out s hs
      map_add' := hout_add s hs
      map_smul' := hout_smul s hs }
  let posOp (s : ℝ) (hs : 0 < s) : E →L[ℝ] E :=
    (lin s hs).mkContinuous 1 (fun f => by
      simpa [lin] using
        (BoundedContinuousFunction.norm_le_of_nonempty.mpr
          (fun x : E3 => hbound s hs f x)))
  let A : ℝ → E →L[ℝ] E := fun s =>
    if hs : 0 < s then posOp s hs else 0
  refine ⟨A, ?_⟩
  intro t ht
  have hA : A t = posOp t ht := by
    simp [A, ht]
  constructor
  · rw [hA]
    exact (lin t ht).mkContinuous_norm_le zero_le_one _
  · intro f x
    constructor
    · simpa [k] using hInt t ht f x
    · rw [hA]
      change out t ht f x = _
      rfl
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
