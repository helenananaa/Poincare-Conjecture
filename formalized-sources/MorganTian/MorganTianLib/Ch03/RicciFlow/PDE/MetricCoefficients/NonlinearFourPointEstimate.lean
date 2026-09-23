import Mathlib
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "J3" => (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3)
local notation "M3" => Fin 3 → Fin 3 → ℝ
local notation "E9" => EuclideanSpace ℝ (Fin 3 × Fin 3)

/-- **Math.** nonlinear four point estimate. -/
theorem nonlinear_four_point_estimate {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (s : Set E) (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hbound : ∀ x ∈ s, ‖fderiv ℝ f x‖ ≤ M)
    (hLip : ∀ x ∈ s, ∀ y ∈ s, ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤ L*‖x-y‖)
    (a b c d : E) (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s) :
    ‖f a-f b-f c+f d‖ ≤ M*‖(a-b)-(c-d)‖ +
      L*(‖a-c‖+‖b-d‖)*‖c-d‖ :=
/- SWARM_PROOF_BEGIN -/
by
  let p : ℝ → E := fun t => b + t • (a - b)
  let q : ℝ → E := fun t => d + t • (c - d)
  let H : ℝ → F := fun t => f (p t) - f (q t)
  have hp_mem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : p t ∈ s := by
    exact hs.add_smul_sub_mem hb ha ht
  have hq_mem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : q t ∈ s := by
    exact hs.add_smul_sub_mem hd hc ht
  have hH (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt H
      (fderiv ℝ f (p t) (a - b) - fderiv ℝ f (q t) (c - d)) t := by
    have hp : HasDerivAt p (a - b) t := by
      simpa [p] using ((hasDerivAt_id t).smul_const (a - b)).const_add b
    have hq : HasDerivAt q (c - d) t := by
      simpa [q] using ((hasDerivAt_id t).smul_const (c - d)).const_add d
    have hfp : HasDerivAt (fun u => f (p u)) (fderiv ℝ f (p t) (a - b)) t := by
      simpa [Function.comp_def] using
        (hf (p t) (hp_mem t ht)).hasFDerivAt.comp_hasDerivAt t hp
    have hfq : HasDerivAt (fun u => f (q u)) (fderiv ℝ f (q t) (c - d)) t := by
      simpa [Function.comp_def] using
        (hf (q t) (hq_mem t ht)).hasFDerivAt.comp_hasDerivAt t hq
    convert hfp.sub hfq using 1
    rfl
  have hpath_dist (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖p t - q t‖ ≤ ‖a - c‖ + ‖b - d‖ := by
    have hpath : p t - q t = (1 - t) • (b - d) + t • (a - c) := by
      dsimp [p, q]
      module
    have ht0 : 0 ≤ t := ht.1
    have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
    have htab : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; exact ht.2
    have ht1ab : |1 - t| ≤ 1 := by rw [abs_of_nonneg ht1]; linarith [ht.2]
    rw [hpath]
    calc
      ‖(1 - t) • (b - d) + t • (a - c)‖ ≤
          ‖(1 - t) • (b - d)‖ + ‖t • (a - c)‖ := norm_add_le _ _
      _ = |1 - t| * ‖b - d‖ + |t| * ‖a - c‖ := by simp [norm_smul, Real.norm_eq_abs]
      _ ≤ 1 * ‖b - d‖ + 1 * ‖a - c‖ := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right ht1ab (norm_nonneg _))
          (mul_le_mul_of_nonneg_right htab (norm_nonneg _))
      _ = ‖a - c‖ + ‖b - d‖ := by ring
  have hderiv_bound : ∀ t ∈ Ico (0 : ℝ) 1,
      ‖derivWithin H (Icc (0 : ℝ) 1) t‖ ≤
        M * ‖(a - b) - (c - d)‖ +
          L * (‖a - c‖ + ‖b - d‖) * ‖c - d‖ := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
    have hderiv := (hH t htI).hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Icc_zero_one t htI)
    let A : E →L[ℝ] F := fderiv ℝ f (p t)
    let B : E →L[ℝ] F := fderiv ℝ f (q t)
    have hsplit : A (a - b) - B (c - d) =
        A ((a - b) - (c - d)) + (A - B) (c - d) := by
      simp only [map_sub, sub_apply]
      abel
    have hfirst : ‖A ((a - b) - (c - d))‖ ≤
        M * ‖(a - b) - (c - d)‖ := by
      calc
        ‖A ((a - b) - (c - d))‖ ≤ ‖A‖ * ‖(a - b) - (c - d)‖ := A.le_opNorm _
        _ ≤ M * ‖(a - b) - (c - d)‖ :=
          mul_le_mul_of_nonneg_right (hbound (p t) (hp_mem t htI)) (norm_nonneg _)
    have hsecond : ‖(A - B) (c - d)‖ ≤
        (L * ‖p t - q t‖) * ‖c - d‖ := by
      calc
        ‖(A - B) (c - d)‖ ≤ ‖A - B‖ * ‖c - d‖ := (A - B).le_opNorm _
        _ ≤ (L * ‖p t - q t‖) * ‖c - d‖ :=
          mul_le_mul_of_nonneg_right
            (hLip (p t) (hp_mem t htI) (q t) (hq_mem t htI)) (norm_nonneg _)
    rw [hderiv]
    calc
      ‖A (a - b) - B (c - d)‖ =
          ‖A ((a - b) - (c - d)) + (A - B) (c - d)‖ := by rw [hsplit]
      _ ≤ ‖A ((a - b) - (c - d))‖ + ‖(A - B) (c - d)‖ := norm_add_le _ _
      _ ≤ M * ‖(a - b) - (c - d)‖ + (L * ‖p t - q t‖) * ‖c - d‖ :=
          add_le_add hfirst hsecond
      _ ≤ M * ‖(a - b) - (c - d)‖ +
          L * (‖a - c‖ + ‖b - d‖) * ‖c - d‖ := by
        have htmp : (L * ‖p t - q t‖) * ‖c - d‖ ≤
            (L * (‖a - c‖ + ‖b - d‖)) * ‖c - d‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hpath_dist t htI) hL) (norm_nonneg (c - d))
        calc
          M * ‖(a - b) - (c - d)‖ + (L * ‖p t - q t‖) * ‖c - d‖ =
              (L * ‖p t - q t‖) * ‖c - d‖ + M * ‖(a - b) - (c - d)‖ := by ring
          _ ≤ (L * (‖a - c‖ + ‖b - d‖)) * ‖c - d‖ + M * ‖(a - b) - (c - d)‖ :=
            add_le_add_left htmp _
          _ = M * ‖(a - b) - (c - d)‖ +
              L * (‖a - c‖ + ‖b - d‖) * ‖c - d‖ := by ring
  have hmean := norm_image_sub_le_of_norm_deriv_le_segment_01
    (f := H) (C := M * ‖(a - b) - (c - d)‖ +
      L * (‖a - c‖ + ‖b - d‖) * ‖c - d‖)
    (fun t ht => (hH t ht).differentiableAt.differentiableWithinAt)
    hderiv_bound
  have hends : H 1 - H 0 = f a - f b - f c + f d := by
    have hp0 : p 0 = b := by simp [p]
    have hp1 : p 1 = a := by simp [p]
    have hq0 : q 0 = d := by simp [q]
    have hq1 : q 1 = c := by simp [q]
    simp [H, hp0, hp1, hq0, hq1]
    abel
  calc
    ‖f a - f b - f c + f d‖ = ‖H 1 - H 0‖ := by rw [hends]
    _ ≤ M * ‖(a - b) - (c - d)‖ +
        L * (‖a - c‖ + ‖b - d‖) * ‖c - d‖ := hmean
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
