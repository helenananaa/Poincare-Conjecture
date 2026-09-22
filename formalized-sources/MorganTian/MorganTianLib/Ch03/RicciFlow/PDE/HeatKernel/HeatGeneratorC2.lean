import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.GaussianCovariance
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.GaussianSecondTail
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HeatLocalTaylor
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursivePolynomialMoment
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.GaussianNormForm
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideGradientL1
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HeatTimeDerivativeL1
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatTimeEquation
import Mathlib
open Set MeasureTheory Filter Function
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- The heat generator at time zero is the actual spatial Laplacian. -/
theorem heat_generator_at_C2_initial_data (f : E3 →ᵇ ℝ)
    (hf : ContDiff ℝ 2 (f : E3 → ℝ)) (x : E3) :
    Tendsto (fun t : ℝ => t⁻¹ * ((∫ y : E3, euclideanHeatKernel 3 t y*f (x-y))-f x))
      (𝓝[>] (0:ℝ))
      (𝓝 (∑ i : Fin 3, fderiv ℝ (fun z : E3 => fderiv ℝ (f : E3 → ℝ) z
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1))) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let K : ℝ → E3 → ℝ := fun s y => euclideanHeatKernel 3 s y
  let D : E3 →L[ℝ] ℝ := fderiv ℝ (f : E3 → ℝ) x
  let B : E3 →L[ℝ] E3 →L[ℝ] ℝ :=
    fderiv ℝ (fun z : E3 => fderiv ℝ (f : E3 → ℝ) z) x
  let R : E3 → ℝ := fun y =>
    f (x-y)-f x+D y-(1/2:ℝ)*(B y) y
  have hf2 : ContDiff ℝ 2 (f : E3 → ℝ) := hf
  have hmass (s : ℝ) (hs : 0 < s) : Integrable (K s) volume ∧
      (∫ y : E3, K s y) = 1 := by
    simpa [K] using (euclideanHeatKernel_mass_semigroup 3).1 s hs
  have hKcont (s : ℝ) (hs : 0 < s) : Continuous (fun y : E3 =>
      euclideanHeatKernel 3 s y) := by
    unfold euclideanHeatKernel
    exact (contDiff_prod (fun i _ =>
      (gaussianHeatKernel_derivatives hs).1.comp (by fun_prop))).continuous
  have hcoord_expand (L : E3 →L[ℝ] ℝ) (v : E3) :
      L v = ∑ i : Fin 3, (L (EuclideanSpace.single i 1)) * v i := by
    have hv : v = ∑ i : Fin 3, v i • EuclideanSpace.single i 1 := by
      ext j
      fin_cases j <;> simp [Fin.sum_univ_succ]
    calc
      L v = L (∑ i : Fin 3, v i • EuclideanSpace.single i 1) := congrArg L hv
      _ = ∑ i : Fin 3, L (v i • EuclideanSpace.single i 1) := by rw [map_sum]
      _ = ∑ i : Fin 3, (L (EuclideanSpace.single i 1)) * v i := by
        simp only [map_smul, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hquad_expand (C : E3 →L[ℝ] E3 →L[ℝ] ℝ) (v : E3) :
      (C v) v = ∑ i : Fin 3, ∑ j : Fin 3,
        C (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) * v i * v j := by
    have hv : v = ∑ i : Fin 3, v i • EuclideanSpace.single i 1 := by
      ext j
      fin_cases j <;> simp [Fin.sum_univ_succ]
    calc
      (C v) v = (C (∑ i : Fin 3, v i • EuclideanSpace.single i 1)) v :=
        congrArg (fun z => (C z) v) hv
      _ = (∑ i : Fin 3, C (v i • EuclideanSpace.single i 1)) v := by rw [map_sum]
      _ = ∑ i : Fin 3, (C (v i • EuclideanSpace.single i 1)) v := by
        rw [ContinuousLinearMap.sum_apply]
      _ = ∑ i : Fin 3, (v i) * (C (EuclideanSpace.single i 1)) v := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      _ = ∑ i : Fin 3, ∑ j : Fin 3,
          C (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) * v i * v j := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hcoord_expand (C (EuclideanSpace.single i 1)) v]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hmom (s : ℝ) (hs : 0 < s) :
      (∀ i : Fin 3, Integrable (fun y : E3 => K s y*y i) volume ∧
        (∫ y : E3, K s y*y i)=0) ∧
      (∀ i j : Fin 3, Integrable (fun y : E3 => K s y*y i*y j) volume ∧
        (∫ y : E3, K s y*y i*y j)=(if i=j then 2*s else 0)) := by
    simpa [K] using (heat_kernel_first_second_moments (t := s) hs)
  /- old malformed declaration retained outside the proof path
  have hmom_bad (s : ℝ) (hs : 0 < s) :
      (∀ i : Fin 3, Integrable (fun y : E3 => K s y*y i) volume ∧
        (∫ y : E3, K s y*y i)=0) ∧
      ∀ i j : Fin 3, Integrable (fun y : E3, K y*y i*y j) volume ∧
        (∫ y : E3, K s y*y i*y j)=(if i=j then 2*s else 0) := by
    simpa [K] using (heat_kernel_first_second_moments (t := s) hs)
  -/
  have hKint (s : ℝ) (hs : 0 < s) : Integrable (K s) volume := (hmass s hs).1
  have hKnonneg (s : ℝ) (hs : 0 < s) : ∀ y : E3, 0 ≤ K s y := by
    intro y
    exact (by simpa [K] using (euclideanHeatKernel_pos 3 hs y).le)
  have hnorm2_int (s : ℝ) (hs : 0 < s) :
      Integrable (fun y : E3 => K s y * ‖y‖^2) volume := by
    have hi : ∀ i : Fin 3, Integrable (fun y : E3 => K s y * (y i)^2) volume := by
      intro i
      simpa [pow_two, mul_assoc] using (hmom s hs).2 i i |>.1
    have hsum0 : Integrable (fun y : E3 => ∑ i : Fin 3, K s y * (y i)^2) volume := by
      refine integrable_finsetSum Finset.univ ?_
      intro i himem
      exact hi i
    have hsum : Integrable (fun y : E3 => K s y * ∑ i : Fin 3, (y i)^2) volume := by
      apply hsum0.congr
      filter_upwards [] with y
      rw [Finset.mul_sum]
    apply hsum.congr
    filter_upwards [] with y
    rw [EuclideanSpace.real_norm_sq_eq]
  have hnorm2_integral (s : ℝ) (hs : 0 < s) :
      (∫ y : E3, K s y * ‖y‖^2) = 6*s := by
    calc
      (∫ y : E3, K s y * ‖y‖^2) =
          ∫ y : E3, K s y * ∑ i : Fin 3, (y i)^2 := by
            apply integral_congr_ae
            filter_upwards [] with y
            rw [EuclideanSpace.real_norm_sq_eq]
      _ =
          ∫ y : E3, ∑ i : Fin 3, K s y * (y i)^2 := by
            congr 1
            funext y
            rw [Finset.mul_sum]
      _ = ∑ i : Fin 3, ∫ y : E3, K s y * (y i)^2 := by
            simpa using (integral_finsetSum (μ := (volume : Measure E3))
              Finset.univ (fun i hi => by
                simpa [pow_two, mul_assoc] using (hmom s hs).2 i i |>.1))
      _ = ∑ i : Fin 3, (2*s) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [show (fun y : E3 => K s y * (y i)^2) =
              (fun y : E3 => K s y * y i * y i) by
                funext y
                ring, (hmom s hs).2 i i |>.2]
            simp
      _ = 6*s := by simp; ring
  have hKlinear_int (s : ℝ) (hs : 0 < s) :
      Integrable (fun y : E3 => K s y * D y) volume := by
    have hi : ∀ i : Fin 3, Integrable
        (fun y : E3 => K s y * (D (EuclideanSpace.single i 1)) * y i) volume := by
      intro i
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        ((hmom s hs).1 i).1.const_mul (D (EuclideanSpace.single i 1))
    have hsum0 : Integrable (fun y : E3 => ∑ i : Fin 3,
        K s y * (D (EuclideanSpace.single i 1)) * y i) volume := by
      refine integrable_finsetSum Finset.univ ?_
      intro i himem
      exact hi i
    refine hsum0.congr ?_
    filter_upwards [] with y
    rw [show D y = ∑ i : Fin 3, D (EuclideanSpace.single i 1) * y i by
      exact hcoord_expand D y]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hKquad_int (s : ℝ) (hs : 0 < s) :
      Integrable (fun y : E3 => K s y * (B y) y) volume := by
    have hi : ∀ i j : Fin 3, Integrable
        (fun y : E3 => K s y * (B (EuclideanSpace.single i 1))
          (EuclideanSpace.single j 1) * y i * y j) volume := by
      intro i j
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        ((hmom s hs).2 i j).1.const_mul
          ((B (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1))
    have hsum0 : Integrable (fun y : E3 => ∑ i : Fin 3, ∑ j : Fin 3,
        K s y * (B (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1) * y i * y j)
        volume := by
      refine integrable_finsetSum Finset.univ ?_
      intro i himem
      refine integrable_finsetSum Finset.univ ?_
      intro j hjmem
      exact hi i j
    refine hsum0.congr ?_
    filter_upwards [] with y
    rw [hquad_expand B y]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hKf_int (s : ℝ) (hs : 0 < s) :
      Integrable (fun y : E3 => K s y * f (x-y)) volume := by
    have hdom : Integrable (fun y : E3 => K s y * ‖f‖) volume := by
      simpa [mul_comm] using (hKint s hs).const_mul ‖f‖
    have hc : Continuous (fun y : E3 => K s y * f (x-y)) := by
      exact (hKcont s hs).mul (f.continuous.comp (continuous_const.sub continuous_id))
    apply hdom.mono' hc.aestronglyMeasurable
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hKnonneg s hs y)]
    exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm (x-y)) (hKnonneg s hs y)
  have hKR_int (s : ℝ) (hs : 0 < s) :
      Integrable (fun y : E3 => K s y * R y) volume := by
    have hKfx : Integrable (fun y : E3 => K s y * f x) volume := by
      simpa [mul_comm] using (hKint s hs).const_mul (f x)
    have hhalf : Integrable (fun y : E3 => (1/2:ℝ) * (K s y * (B y) y)) volume :=
      (hKquad_int s hs).const_mul (1/2:ℝ)
    have hsum := (((hKf_int s hs).sub hKfx).add (hKlinear_int s hs)).sub hhalf
    refine hsum.congr ?_
    filter_upwards [] with y
    dsimp [R]
    ring
  have hlinear_integral (s : ℝ) (hs : 0 < s) :
      (∫ y : E3, K s y * D y) = 0 := by
    rw [show (fun y : E3 => K s y * D y) =
      (fun y : E3 => ∑ i : Fin 3, K s y * D (EuclideanSpace.single i 1) * y i) by
        funext y
        rw [hcoord_expand D y, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring]
    rw [integral_finsetSum]
    · apply Finset.sum_eq_zero
      intro i hi
      calc
        (∫ y : E3, K s y * D (EuclideanSpace.single i 1) * y i) =
            D (EuclideanSpace.single i 1) * (∫ y : E3, K s y * y i) := by
              rw [show (fun y : E3 => K s y * D (EuclideanSpace.single i 1) * y i) =
                (fun y : E3 => D (EuclideanSpace.single i 1) * (K s y * y i)) by
                  funext y; ring, integral_const_mul]
        _ = 0 := by rw [(hmom s hs).1 i |>.2, mul_zero]
    · intro i hi
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        ((hmom s hs).1 i).1.const_mul (D (EuclideanSpace.single i 1))
  have hquad_integral (s : ℝ) (hs : 0 < s) :
      (∫ y : E3, K s y * (B y) y) =
      2*s * ∑ i : Fin 3, (B (EuclideanSpace.single i 1))
        (EuclideanSpace.single i 1) := by
    have hi (i j : Fin 3) : Integrable (fun y : E3 =>
        B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) * (K s y*y i*y j)) volume :=
      ((hmom s hs).2 i j).1.const_mul _
    have heq : (fun y : E3 => K s y*(B y) y) =
        (fun y : E3 => ∑ i : Fin 3, ∑ j : Fin 3,
          B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)*(K s y*y i*y j)) := by
      funext y
      rw [hquad_expand B y, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq, integral_finsetSum]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum]
      · simp_rw [integral_const_mul]
        simp_rw [show ∀ j : Fin 3, (∫ y : E3, K s y*y i*y j) =
          (if i=j then 2*s else 0) from fun j => ((hmom s hs).2 i j).2]
        simp [mul_ite, mul_comm]
      · intro j _; exact hi i j
    · intro i _; exact integrable_finsetSum Finset.univ (fun j _ => hi i j)
  have hpoly_identity (s : ℝ) (hs : 0 < s) :
      (∫ y : E3, euclideanHeatKernel 3 s y * f (x-y)) - f x =
        (∫ y : E3, euclideanHeatKernel 3 s y * R y) +
          s * ∑ i : Fin 3, (B (EuclideanSpace.single i 1))
            (EuclideanSpace.single i 1) := by
    have hKs : Integrable (fun y : E3 => euclideanHeatKernel 3 s y) volume :=
      (euclideanHeatKernel_mass_semigroup 3).1 s hs |>.1
    have hKsD : Integrable (fun y : E3 => euclideanHeatKernel 3 s y * D y) volume := by
      simpa [K] using hKlinear_int s hs
    have hKsB : Integrable (fun y : E3 => euclideanHeatKernel 3 s y * (B y) y) volume := by
      simpa [K] using hKquad_int s hs
    have hKsR : Integrable (fun y : E3 => euclideanHeatKernel 3 s y * R y) volume := by
      simpa [K] using hKR_int s hs
    have hfirsts : (∫ y : E3, euclideanHeatKernel 3 s y * D y) = 0 := by
      simpa [K] using hlinear_integral s hs
    have hseconds : (∫ y : E3, euclideanHeatKernel 3 s y * (B y) y) =
        2*s * ∑ i : Fin 3, (B (EuclideanSpace.single i 1))
          (EuclideanSpace.single i 1) := by
      simpa [K] using hquad_integral s hs
    calc
      (∫ y : E3, euclideanHeatKernel 3 s y * f (x-y)) - f x =
          (∫ y : E3, euclideanHeatKernel 3 s y * f (x-y)) -
            (∫ y : E3, euclideanHeatKernel 3 s y * f x) := by
              rw [integral_mul_const, (euclideanHeatKernel_mass_semigroup 3).1 s hs |>.2]
              ring
      _ = ∫ y : E3, euclideanHeatKernel 3 s y * (f (x-y) - f x) := by
            rw [← integral_sub (hKf_int s hs) (by
              simpa [mul_comm] using hKs.const_mul (f x))]
            congr 1
            funext y
            ring
      _ = (∫ y : E3, euclideanHeatKernel 3 s y * R y) -
            (∫ y : E3, euclideanHeatKernel 3 s y * D y) +
              (1/2:ℝ) * (∫ y : E3, euclideanHeatKernel 3 s y * (B y) y) := by
            rw [show (fun y : E3 => euclideanHeatKernel 3 s y * (f (x-y) - f x)) =
              (fun y : E3 => (euclideanHeatKernel 3 s y * R y +
                (1/2:ℝ) * (euclideanHeatKernel 3 s y * (B y) y)) -
                euclideanHeatKernel 3 s y * D y) by
                  funext y; dsimp [R]; ring]
            have hsplit := integral_sub (hKsR.add (hKsB.const_mul (1/2:ℝ))) hKsD
            have hadd := integral_add hKsR (hKsB.const_mul (1/2:ℝ))
            simp only [Pi.add_apply] at hsplit hadd
            rw [integral_const_mul] at hadd
            calc
              _ = (∫ y : E3, euclideanHeatKernel 3 s y * R y +
                    (1/2:ℝ)*(euclideanHeatKernel 3 s y*(B y) y)) -
                    (∫ y : E3, euclideanHeatKernel 3 s y*D y) := by
                      convert! hsplit using 1
              _ = _ := by rw [hadd]; ring
      _ = (∫ y : E3, euclideanHeatKernel 3 s y * R y) +
            s * ∑ i : Fin 3, (B (EuclideanSpace.single i 1))
              (EuclideanSpace.single i 1) := by
            rw [hfirsts, hseconds]
            ring
  let C : ℝ := 1 + 2*‖f‖ + ‖D‖ + (1/2:ℝ)*‖B‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hglobal (y : E3) : |R y| ≤ C*(1+‖y‖^2) := by
    have hn : ‖y‖ ≤ 1+‖y‖^2 := by nlinarith [sq_nonneg (‖y‖-1)]
    have hfd : |f (x-y)-f x| ≤ 2*‖f‖ := by
      calc
        |f (x-y)-f x| ≤ ‖f (x-y)‖+‖f x‖ := by simpa only [Real.norm_eq_abs] using (norm_sub_le (f (x-y)) (f x))
        _ ≤ ‖f‖+‖f‖ := add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)
        _ = 2*‖f‖ := by ring
    have hd : |D y| ≤ ‖D‖*‖y‖ := by simpa [Real.norm_eq_abs] using D.le_opNorm y
    have hb : |(B y) y| ≤ ‖B‖*‖y‖^2 := by
      calc
        |(B y) y| ≤ ‖B y‖*‖y‖ := by simpa [Real.norm_eq_abs] using (B y).le_opNorm y
        _ ≤ (‖B‖*‖y‖)*‖y‖ := mul_le_mul_of_nonneg_right (B.le_opNorm y) (norm_nonneg _)
        _ = ‖B‖*‖y‖^2 := by ring
    have htri : |R y| ≤ |f (x-y)-f x|+|D y|+(1/2:ℝ)*|(B y) y| := by
      dsimp [R]
      calc
        |f (x-y)-f x+D y-(1/2:ℝ)*(B y) y| ≤
            |f (x-y)-f x+D y|+|(1/2:ℝ)*(B y) y| := abs_sub _ _
        _ ≤ (|f (x-y)-f x|+|D y|)+|(1/2:ℝ)*(B y) y| :=
          add_le_add (abs_add_le (f (x-y)-f x) (D y)) le_rfl
        _ = _ := by rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
    calc
      |R y| ≤ 2*‖f‖+‖D‖*‖y‖+(1/2:ℝ)*(‖B‖*‖y‖^2) := by
        exact htri.trans (add_le_add (add_le_add hfd hd) (mul_le_mul_of_nonneg_left hb (by norm_num)))
      _ ≤ (2*‖f‖+‖D‖+(1/2:ℝ)*‖B‖)*(1+‖y‖^2) := by
        nlinarith [mul_nonneg (norm_nonneg f) (sq_nonneg ‖y‖), mul_nonneg (norm_nonneg D) (sub_nonneg.mpr hn), norm_nonneg B]
      _ ≤ C*(1+‖y‖^2) := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity)
  have hR_limit : Tendsto (fun s : ℝ => s⁻¹*(∫ y : E3, K s y*R y))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let eta : ℝ := ε/12
    have heta : 0<eta := by dsimp [eta]; linarith
    obtain ⟨r, hr, hl⟩ := C2_local_quadratic_remainder (f : E3 → ℝ) hf x eta heta
    have htail := heat_kernel_quadratic_tail_small_time r hr
    have htC : Tendsto (fun s : ℝ => C*(s⁻¹*∫ y : E3 in {z | r≤‖z‖},
        euclideanHeatKernel 3 s y*(1+‖y‖^2))) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_const_nhds.mul htail : Tendsto
        (fun s : ℝ => C*(s⁻¹*∫ y : E3 in {z | r≤‖z‖}, euclideanHeatKernel 3 s y*(1+‖y‖^2)))
        (𝓝[>] (0:ℝ)) (𝓝 (C*0)))
    have hevent := htC.eventually (eventually_lt_nhds (by linarith : (0:ℝ)<ε/2))
    filter_upwards [self_mem_nhdsWithin, hevent] with s hs hsmall
    have hspos : 0<s := hs
    let S : Set E3 := {y | r≤‖y‖}
    have hS : MeasurableSet S := (isClosed_le continuous_const continuous_norm).measurableSet
    have hG : Integrable (fun y : E3 => K s y*(1+‖y‖^2)) volume := by
      convert! (hKint s hspos).add (hnorm2_int s hspos) using 1
      funext y
      simp only [Pi.add_apply, mul_add, mul_one]
    have hGind := hG.indicator hS
    have hupper : Integrable (fun y : E3 => eta*(K s y*‖y‖^2)+
        C*S.indicator (fun z : E3 => K s z*(1+‖z‖^2)) y) volume :=
      ((hnorm2_int s hspos).const_mul eta).add (hGind.const_mul C)
    have hbound (y : E3) : ‖K s y*R y‖ ≤ eta*(K s y*‖y‖^2)+
        C*S.indicator (fun z : E3 => K s z*(1+‖z‖^2)) y := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hKnonneg s hspos y)]
      by_cases hy : y∈S
      · rw [Set.indicator_of_mem hy]
        calc
          K s y*|R y| ≤ K s y*(C*(1+‖y‖^2)) :=
            mul_le_mul_of_nonneg_left (hglobal y) (hKnonneg s hspos y)
          _ = C*(K s y*(1+‖y‖^2)) := by ring
          _ ≤ eta*(K s y*‖y‖^2)+C*(K s y*(1+‖y‖^2)) :=
            le_add_of_nonneg_left (mul_nonneg heta.le (mul_nonneg (hKnonneg s hspos y) (sq_nonneg ‖y‖)))
      · rw [Set.indicator_of_notMem hy, mul_zero, add_zero]
        have hyr : ‖y‖<r := lt_of_not_ge (by simpa [S] using hy)
        have hlocal : |R y| ≤ eta*‖y‖^2 := by simpa only [R,D,B] using hl y hyr
        calc
          K s y*|R y| ≤ K s y*(eta*‖y‖^2) :=
            mul_le_mul_of_nonneg_left hlocal (hKnonneg s hspos y)
          _ = eta*(K s y*‖y‖^2) := by ring
    have hle := norm_integral_le_of_norm_le hupper (ae_of_all _ hbound)
    have hupper_eq : (∫ y : E3, eta*(K s y*‖y‖^2)+
        C*S.indicator (fun z : E3 => K s z*(1+‖z‖^2)) y) =
        eta*(6*s)+C*(∫ y : E3 in S, K s y*(1+‖y‖^2)) := by
      rw [integral_add ((hnorm2_int s hspos).const_mul eta) (hGind.const_mul C),
        integral_const_mul, integral_const_mul, integral_indicator hS,
        hnorm2_integral s hspos]
    rw [hupper_eq] at hle
    rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos (inv_pos.mpr hspos)]
    calc
      s⁻¹*|∫ y : E3, K s y*R y| ≤
          s⁻¹*(eta*(6*s)+C*(∫ y : E3 in S, K s y*(1+‖y‖^2))) :=
        mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hle)
          (inv_nonneg.mpr hspos.le)
      _ = 6*eta+C*(s⁻¹*∫ y : E3 in S, K s y*(1+‖y‖^2)) := by
        field_simp [hspos.ne'] <;> ring
      _ < ε := by
        have he : C*(s⁻¹*∫ y : E3 in S, K s y*(1+‖y‖^2)) < ε/2 := by
          simpa only [K,S] using hsmall
        dsimp [eta]
        linarith
  have hfinal : Tendsto (fun s : ℝ => s⁻¹ *
      ((∫ y : E3, euclideanHeatKernel 3 s y*f (x-y))-f x))
      (𝓝[>] (0:ℝ)) (𝓝 (∑ i : Fin 3, B (EuclideanSpace.single i 1)
        (EuclideanSpace.single i 1))) := by
    have hsum := hR_limit.add (tendsto_const_nhds (x :=
      ∑ i : Fin 3, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)))
    simp only [zero_add] at hsum
    apply hsum.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hspos : 0<s := hs
    rw [hpoly_identity s hspos]
    dsimp only [K]
    field_simp [hspos.ne'] <;> ring
  have hBcoord (i : Fin 3) : B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) =
      fderiv ℝ (fun z : E3 => fderiv ℝ (f : E3 → ℝ) z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1) := by
    have hd : DifferentiableAt ℝ (fderiv ℝ (f : E3 → ℝ)) x :=
      (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
    have hc : DifferentiableAt ℝ (fun _ : E3 => (EuclideanSpace.single i 1 : E3)) x := by fun_prop
    have hh := congrArg (fun A : E3 →L[ℝ] ℝ => A (EuclideanSpace.single i 1)) (fderiv_clm_apply hd hc)
    simpa [B, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply] using hh.symm
  simpa only [hBcoord] using hfinal
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
