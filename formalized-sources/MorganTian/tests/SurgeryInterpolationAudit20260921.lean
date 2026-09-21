import MorganTianLib.Ch02.SurgeryInterpolation.NativeNeckMetric
import MorganTianLib.Ch02.SurgeryInterpolation.LengthComparison
import MorganTianLib.Ch02.SurgeryInterpolation.ProfileJets
import MorganTianLib.Ch02.SurgeryInterpolation.TipFlattening
import Lean

open MorganTianLib.SurgeryInterpolation Riemannian Set
open scoped ContDiff Manifold

/-- **Math.** A nonempty example: an actual smooth metric on the real line, unchanged on the left
and strictly shorter than the Euclidean metric at the right-hand sample point. -/
example : ∃ g : RiemannianMetric 𝓘(ℝ, ℝ) ℝ,
    (∀ x : ℝ, x ≤ 0 → g.metricInner x 1 1 = 1) ∧ g.metricInner 2 1 1 < 1 := by
  let ge : RiemannianMetric 𝓘(ℝ, ℝ) ℝ := DCEuclideanMetric
  have hunit (x : ℝ) : ge.metricInner x 1 1 = 1 := by
    change (DCEuclideanMetric (F := ℝ)).metricInner x 1 1 = 1
    rw [DCEuclideanMetric_apply]
    norm_num <;> first | rfl | exact Or.inl rfl
  have hdom : ∀ x (v : ℝ), (1 / 2 : ℝ) * ge.metricInner x v v ≤ ge.metricInner x v v := by
    intro x v
    linarith [ge.metricInner_self_nonneg x v]
  obtain ⟨g, _, hleft, hright, _⟩ := exists_neck_interpolationMetric ge ge id
    contMDiff_id 1 4 (1 / 2) (by norm_num) (by norm_num) (by norm_num) hdom
  refine ⟨g, ?_, ?_⟩
  · intro x hx
    rw [hleft x hx, hunit]
  · rw [hright 2 (by norm_num), hunit]
    have hf := neckProfile_nonneg (show (0 : ℝ) ≤ 1 by norm_num) 4 2
    have he : Real.exp (-2 * neckProfile 1 4 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    simp only [mul_one, id_eq]
    linarith

open Lean Elab Command in
run_cmd do
  let names : Array Name := #[
    ``neckProfile_contDiff,
    ``neckCutoff_contDiff,
    ``neckProfile_flat_and_derivatives,
    ``exists_weighted_riemannianMetric,
    ``contMDiff_comp_of_flattened_tip,
    ``exists_neck_interpolationMetric,
    ``nativeAxis_contMDiff,
    ``exists_native_neck_surgeryMetric,
    ``arcLength_le_of_metric_pullback_le]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in names do
    unless (← getEnv).contains n do throwError "Missing theorem: {n}"
    let axioms ← Lean.collectAxioms n
    let bad := axioms.filter (fun a ↦ !allowed.contains a)
    unless bad.isEmpty do throwError "Nonstandard axioms for {n}: {bad}"
    logInfo m!"PASS {n}: {axioms}"
  logInfo m!"SURGERY_INTERPOLATION_GUARD_PASS {names.size}"

#check MorganTianLib.SurgeryInterpolation.exists_native_neck_surgeryMetric
