import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveHessianFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveHessianEstimate
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursivePolynomialMoment
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HessianCancellation
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanSemigroup
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Actual mixed/diagonal Frechet Hessian entries have integrable zero mass. -/
theorem euclideanHeatKernel_three_hessian_cancellation {t : ℝ} (ht : 0 < t)
    (i j : Fin 3) :
    Integrable (fun y : E3 => fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
      (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)) volume ∧
    (∫ y : E3, fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
      (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)) = 0 :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let F : E3 → ℝ := fun y =>
    fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 t) z
      (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)
  have hFformula (y : E3) :
      F y = (y i * y j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)) *
        euclideanHeatKernel 3 t y := by
    exact euclideanHeatKernel_three_hessian_formula ht y i j
  have hKcont : Continuous (fun y : E3 => euclideanHeatKernel 3 t y) := by
    unfold euclideanHeatKernel
    exact (contDiff_prod (fun k _ =>
      (gaussianHeatKernel_derivatives ht).1.comp (by fun_prop))).continuous
  have hFcont : Continuous F := by
    rw [show F = (fun y : E3 =>
        (y i * y j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)) *
          euclideanHeatKernel 3 t y) by
      funext y
      exact hFformula y]
    exact (by fun_prop : Continuous (fun y : E3 =>
      y i * y j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0))).mul hKcont
  obtain ⟨C2, hC2, hmoment2⟩ :=
    euclideanHeatKernel_three_nonnegative_moment (2 : ℝ) (by norm_num)
  obtain ⟨C0, hC0, hmoment0⟩ :=
    euclideanHeatKernel_three_nonnegative_moment (0 : ℝ) (by norm_num)
  let G : E3 → ℝ := fun y =>
    (1 / (4 * t ^ 2)) * (euclideanHeatKernel 3 t y * ‖y‖ ^ (2 : ℕ)) +
      (1 / (2 * t)) * euclideanHeatKernel 3 t y
  have hG : Integrable G volume := by
    dsimp [G]
    have h2 : Integrable
        (fun y : E3 => euclideanHeatKernel 3 t y * ‖y‖ ^ (2 : ℕ)) volume := by
      convert (hmoment2 t ht).1 using 1 <;> norm_num [Real.rpow_two]
    have h0 : Integrable (fun y : E3 => euclideanHeatKernel 3 t y) volume := by
      simpa using (hmoment0 t ht).1
    exact (h2.const_mul _).add (h0.const_mul _)
  have hpoint (y : E3) : ‖F y‖ ≤ G y := by
    rw [hFformula y, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (euclideanHeatKernel_pos 3 ht y).le]
    have hyi : |y i| ≤ ‖y‖ := by
      simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le y i)
    have hyj : |y j| ≤ ‖y‖ := by
      simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le y j)
    have hprod : |y i * y j| ≤ ‖y‖ ^ (2 : ℕ) := by
      rw [abs_mul]
      exact (mul_le_mul hyi hyj (abs_nonneg _) (norm_nonneg _)).trans_eq (by ring)
    have hden : 0 < 4 * t ^ 2 := by positivity
    have hdiag : |(if i = j then 1 / (2 * t) else 0)| ≤ 1 / (2 * t) := by
      by_cases hij : i = j
      · rw [if_pos hij, abs_of_pos (by positivity : 0 < (1 : ℝ) / (2 * t))]
      · rw [if_neg hij, abs_zero]
        positivity
    have hcoef :
        |y i * y j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)| ≤
          ‖y‖ ^ (2 : ℕ) / (4 * t ^ 2) + 1 / (2 * t) := by
      calc
        |y i * y j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)| ≤
            |y i * y j / (4 * t ^ 2)| +
              |(if i = j then 1 / (2 * t) else 0)| := by
          simpa [abs_neg] using
            (abs_sub_le (y i * y j / (4 * t ^ 2)) (0 : ℝ)
              (if i = j then 1 / (2 * t) else 0))
        _ = |y i * y j| / (4 * t ^ 2) +
              |(if i = j then 1 / (2 * t) else 0)| := by
          rw [abs_div, abs_of_pos hden]
        _ ≤ ‖y‖ ^ (2 : ℕ) / (4 * t ^ 2) + 1 / (2 * t) := by
          exact add_le_add (div_le_div_of_nonneg_right hprod hden.le) hdiag
    have hmul :
        |y i * y j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)| *
            euclideanHeatKernel 3 t y ≤
          (‖y‖ ^ (2 : ℕ) / (4 * t ^ 2) + 1 / (2 * t)) *
            euclideanHeatKernel 3 t y :=
      mul_le_mul_of_nonneg_right hcoef (euclideanHeatKernel_pos 3 ht y).le
    calc
      |y i * y j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)| *
          euclideanHeatKernel 3 t y ≤
          (‖y‖ ^ (2 : ℕ) / (4 * t ^ 2) + 1 / (2 * t)) *
            euclideanHeatKernel 3 t y := hmul
      _ = G y := by
        dsimp [G]
        ring
  have hF : Integrable F volume := by
    exact hG.mono' hFcont.aestronglyMeasurable (Eventually.of_forall hpoint)
  let e : (Fin 3 → ℝ) ≃ᵐ E3 := MeasurableEquiv.toLp 2 (Fin 3 → ℝ)
  let P : (Fin 3 → ℝ) → ℝ := fun v =>
    (v i * v j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)) *
      ∏ k, gaussianHeatKernel t (v k)
  have hPeq (v : Fin 3 → ℝ) : P v = F (e v) := by
    rw [hFformula (e v)]
    simp [P, e, euclideanHeatKernel, MeasurableEquiv.toLp_apply,
      PiLp.toLp_apply]
  have hPcomp : P = F ∘ e := by
    funext v
    simpa [Function.comp_def, e] using hPeq v
  have hPintegral : (∫ v : Fin 3 → ℝ, P v) = ∫ y : E3, F y := by
    rw [hPcomp]
    exact (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding F
  refine ⟨hF, ?_⟩
  by_cases hij : i = j
  · subst j
    let A : Fin 3 → ℝ → ℝ := fun k =>
      if k = i then iteratedDeriv 2 (gaussianHeatKernel t) else gaussianHeatKernel t
    have hA : ∀ k : Fin 3, Integrable (A k) volume := by
      intro k
      by_cases hki : k = i
      · subst k
        simpa [A] using (gaussianHeatKernel_hessian_cancellation ht).1
      · simpa [A, hki] using (gaussianHeatKernel_mass_semigroup.1 t ht).1
    have hprod : Integrable (fun v : Fin 3 → ℝ => ∏ k, A k (v k)) volume :=
      Integrable.fintype_prod hA
    have hprod_integral :
        (∫ v : Fin 3 → ℝ, ∏ k, A k (v k)) =
          ∏ k, ∫ x : ℝ, A k x :=
      integral_fintype_prod_volume_eq_prod A
    have hdiag_formula (x : ℝ) :
        iteratedDeriv 2 (gaussianHeatKernel t) x =
          (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gaussianHeatKernel t x :=
      (gaussianHeatKernel_derivatives ht).2 x |>.2.1
    have hPprod (v : Fin 3 → ℝ) : P v = ∏ k, A k (v k) := by
      fin_cases i <;>
        simp [P, A, Fin.prod_univ_succ, hdiag_formula] <;> ring
    have hfactor (k : Fin 3) :
        (∫ x : ℝ, A k x) = if k = i then 0 else 1 := by
      by_cases hki : k = i
      · subst k
        simp [A, (gaussianHeatKernel_hessian_cancellation ht).2]
      · simp [A, hki, (gaussianHeatKernel_mass_semigroup.1 t ht).2]
    have hzeroP : (∫ v : Fin 3 → ℝ, P v) = 0 := by
      rw [show (fun v : Fin 3 → ℝ => P v) =
          (fun v : Fin 3 → ℝ => ∏ k, A k (v k)) by
        funext v
        exact hPprod v, hprod_integral]
      simp_rw [hfactor]
      simp
    rw [← hPintegral]
    exact hzeroP
  · let R : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun v k =>
      if k = i then -v k else v k
    have hR_involutive : Function.Involutive R := by
      intro v
      funext k
      by_cases hki : k = i <;> simp [R, hki]
    have hR_measurable : Measurable R := by
      rw [measurable_pi_iff]
      intro k
      by_cases hki : k = i
      · subst k
        simpa [R] using (measurable_pi_apply i :
          Measurable (fun x : (Fin 3 → ℝ) => x i))
      · simp [R, hki, measurable_pi_apply k]
    let R' : (Fin 3 → ℝ) ≃ᵐ (Fin 3 → ℝ) :=
      MeasurableEquiv.ofInvolutive R hR_involutive hR_measurable
    have hR : MeasurePreserving R' volume volume := by
      have hcoordinate : ∀ k : Fin 3,
          MeasurePreserving (fun x : ℝ => if k = i then -x else x) volume volume := by
        intro k
        by_cases hki : k = i
        · subst k
          simpa using (Measure.measurePreserving_neg (volume : Measure ℝ))
        · simp only [if_neg hki]
          exact MeasurePreserving.id _
      have hR0 : MeasurePreserving R volume volume := by
        simpa [R] using (volume_preserving_pi hcoordinate)
      change MeasurePreserving R volume volume
      exact hR0
    have hprodR (v : Fin 3 → ℝ) :
        (∏ k, gaussianHeatKernel t ((R v) k)) =
          ∏ k, gaussianHeatKernel t (v k) := by
      apply Finset.prod_congr rfl
      intro k hk
      by_cases hki : k = i <;> simp [R, hki, gaussianHeatKernel, neg_sq]
    have hodd (v : Fin 3 → ℝ) : P (R v) = -P v := by
      dsimp [P]
      rw [hprodR]
      simp [R, hij, Ne.symm hij]
      ring
    have hzeroP : (∫ v : Fin 3 → ℝ, P v) = 0 := by
      have hchange : (∫ v : Fin 3 → ℝ, P (R' v)) =
          ∫ v : Fin 3 → ℝ, P v :=
        hR.integral_comp R'.measurableEmbedding P
      have hneg : (∫ v : Fin 3 → ℝ, P (R' v)) =
          -(∫ v : Fin 3 → ℝ, P v) := by
        rw [show (fun v : Fin 3 → ℝ => P (R' v)) =
            (fun v : Fin 3 → ℝ => -P v) by
              funext v
              simpa [R', MeasurableEquiv.ofInvolutive_apply] using hodd v,
          integral_neg]
      rw [hneg] at hchange
      linarith
    rw [← hPintegral]
    exact hzeroP
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
