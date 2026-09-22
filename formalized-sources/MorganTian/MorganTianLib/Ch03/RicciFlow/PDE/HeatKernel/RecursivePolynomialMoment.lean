import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ThreeDimensionalMoment
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanSemigroup
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ThreeDimensionalEquation
import Mathlib.Analysis.Calculus.ContDiff.Convolution
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Uniform-in-time moment bound in the actual Euclidean three-dimensional norm. -/
theorem euclideanHeatKernel_three_nonnegative_moment (beta : ℝ) (hb : 0 ≤ beta) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      Integrable (fun y : E3 => euclideanHeatKernel 3 t y * ‖y‖^beta) volume ∧
      (∫ y : E3, euclideanHeatKernel 3 t y * ‖y‖^beta) ≤ C*t^(beta/2) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have hpow_sum (a b c : ℝ) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) :
      (a + b + c) ^ beta ≤ 3 ^ beta * (a ^ beta + b ^ beta + c ^ beta) := by
    let m : ℝ := max (max a b) c
    have hm : 0 ≤ m := by
      dsimp [m]
      positivity
    have hsum : a + b + c ≤ 3 * m := by
      have ha' : a ≤ m := by
        dsimp [m]
        exact le_trans (le_max_left _ _) (le_max_left _ _)
      have hb' : b ≤ m := by
        dsimp [m]
        exact le_trans (le_max_right _ _) (le_max_left _ _)
      have hc' : c ≤ m := by
        dsimp [m]
        exact le_max_right _ _
      linarith
    have hm_cases : m = a ∨ m = b ∨ m = c := by
      by_cases hab : a ≤ b
      · by_cases hbc : b ≤ c
        · right; right
          simp [m, max_eq_right hab, max_eq_right hbc]
        · right; left
          have hcb : c ≤ b := le_of_not_ge hbc
          simp [m, max_eq_right hab, max_eq_left hcb]
      · have hba : b ≤ a := le_of_not_ge hab
        by_cases hac : a ≤ c
        · right; right
          simp [m, max_eq_left hba, max_eq_right hac]
        · left
          have hca : c ≤ a := le_of_not_ge hac
          simp [m, max_eq_left hba, max_eq_left hca]
    have hm_sum : m ^ beta ≤ a ^ beta + b ^ beta + c ^ beta := by
      by_cases hβ : beta = 0
      · subst beta
        simp only [Real.rpow_zero]
        norm_num
      rcases hm_cases with hma | hmb | hmc
      · rw [hma]
        have hb' : 0 ≤ b ^ beta := Real.rpow_nonneg hb0 _
        have hc' : 0 ≤ c ^ beta := Real.rpow_nonneg hc0 _
        linarith
      · rw [hmb]
        have ha' : 0 ≤ a ^ beta := Real.rpow_nonneg ha0 _
        have hc' : 0 ≤ c ^ beta := Real.rpow_nonneg hc0 _
        linarith
      · rw [hmc]
        have ha' : 0 ≤ a ^ beta := Real.rpow_nonneg ha0 _
        have hb' : 0 ≤ b ^ beta := Real.rpow_nonneg hb0 _
        linarith
    have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ a + b + c) hsum hb
    calc
      (a + b + c) ^ beta ≤ (3 * m) ^ beta := hpow
      _ = 3 ^ beta * m ^ beta := by rw [Real.mul_rpow (by norm_num) hm]
      _ ≤ 3 ^ beta * (a ^ beta + b ^ beta + c ^ beta) := by
        exact mul_le_mul_of_nonneg_left hm_sum (Real.rpow_nonneg (by norm_num) _)
  have hnorm_le (x : E3) : ‖x‖ ≤ ∑ i : Fin 3, |x i| := by
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_succ, Real.norm_eq_abs]
    have hq : 0 ≤ x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by positivity
    have hs : 0 ≤ |x 0| + |x 1| + |x 2| := by positivity
    have hsq_abs : |x 0| ^ 2 + |x 1| ^ 2 + |x 2| ^ 2 ≤
        (|x 0| + |x 1| + |x 2|) ^ 2 := by
      nlinarith [mul_nonneg (abs_nonneg (x 0)) (abs_nonneg (x 1)),
        mul_nonneg (abs_nonneg (x 0)) (abs_nonneg (x 2)),
        mul_nonneg (abs_nonneg (x 1)) (abs_nonneg (x 2))]
    have hsq : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 ≤
        (|x 0| + |x 1| + |x 2|) ^ 2 := by
      simpa only [sq_abs] using hsq_abs
    have hq' : 0 ≤ x 0 ^ 2 + (x 1 ^ 2 + x 2 ^ 2) := by positivity
    have hsq' : x 0 ^ 2 + (x 1 ^ 2 + x 2 ^ 2) ≤
        (|x 0| + (|x 1| + |x 2|)) ^ 2 := by
      convert hsq using 1 <;> ring
    have hs' : 0 ≤ |x 0| + (|x 1| + |x 2|) := by positivity
    nlinarith [Real.sq_sqrt hq', Real.sqrt_nonneg
      (x 0 ^ 2 + (x 1 ^ 2 + x 2 ^ 2))]
  have hnorm_power (x : E3) :
      ‖x‖ ^ beta ≤ 3 ^ beta * ∑ i : Fin 3, |x i| ^ beta := by
    calc
      ‖x‖ ^ beta ≤ (∑ i : Fin 3, |x i|) ^ beta :=
        Real.rpow_le_rpow (norm_nonneg x) (hnorm_le x) hb
      _ ≤ 3 ^ beta * (|x 0| ^ beta + |x 1| ^ beta + |x 2| ^ beta) := by
        rw [show (∑ i : Fin 3, |x i|) = |x 0| + |x 1| + |x 2| by
          simp [Fin.sum_univ_succ]; ring]
        exact hpow_sum |x 0| |x 1| |x 2| (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
      _ = 3 ^ beta * ∑ i : Fin 3, |x i| ^ beta := by
        rw [show (∑ i : Fin 3, |x i| ^ beta) =
            |x 0| ^ beta + |x 1| ^ beta + |x 2| ^ beta by
          simp [Fin.sum_univ_succ]; ring]
  have hgauss : Integrable
      (fun y : ℝ => |y| ^ beta * Real.exp (-(1 / 4 : ℝ) * y ^ 2)) volume := by
    have hpos : IntegrableOn
        (fun y : ℝ => y ^ beta * Real.exp (-(1 / 4 : ℝ) * y ^ 2)) (Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num) (by linarith)
    have hpos' : IntegrableOn
        (fun y : ℝ => |y| ^ beta * Real.exp (-(1 / 4 : ℝ) * y ^ 2)) (Ioi 0) := by
      refine hpos.congr_fun (fun y hy => ?_) measurableSet_Ioi
      rw [abs_of_pos (mem_Ioi.mp hy)]
    have hneg : IntegrableOn
        (fun y : ℝ => |y| ^ beta * Real.exp (-(1 / 4 : ℝ) * y ^ 2)) (Iio 0) := by
      rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
        (Homeomorph.neg ℝ).measurableEmbedding]
      simp only [Function.comp_def, neg_sq, neg_preimage, neg_Iio, neg_zero]
      refine hpos.congr_fun (fun y hy => ?_) measurableSet_Ioi
      rw [abs_neg, abs_of_pos (mem_Ioi.mp hy)]
    rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
      integrableOn_Ici_iff_integrableOn_Ioi]
    exact ⟨hneg, hpos'⟩
  have h1 : Integrable
      (fun y : ℝ => gaussianHeatKernel 1 y * |y| ^ beta) volume := by
    have h := hgauss.const_mul ((Real.sqrt (4 * Real.pi))⁻¹)
    convert h using 1
    funext y
    unfold gaussianHeatKernel
    simp only [mul_one]
    have he : -y ^ 2 / 4 = -(1 / 4 : ℝ) * y ^ 2 := by ring
    rw [he]
    ring
  let F : ℝ → ℝ := fun x => gaussianHeatKernel 1 x * |x| ^ beta
  let M : ℝ := ∫ y : ℝ, F y
  have hM_nonneg : 0 ≤ M := by
    dsimp [M, F]
    apply integral_nonneg_of_ae
    filter_upwards [] with y
    exact mul_nonneg (gaussianHeatKernel_pos (by norm_num) y).le
      (Real.rpow_nonneg (abs_nonneg y) _)
  let C₀ : ℝ := 1 + M
  have hC₀ : 0 < C₀ := by
    dsimp [C₀]
    linarith
  have hmoment : ∀ t : ℝ, 0 < t →
      Integrable (fun x : ℝ => gaussianHeatKernel t x * |x| ^ beta) volume ∧
      (∫ x : ℝ, gaussianHeatKernel t x * |x| ^ beta) ≤ C₀ * t ^ (beta / 2) := by
    intro t ht
    let a : ℝ := Real.sqrt t
    let Ft : ℝ → ℝ := fun x => gaussianHeatKernel t x * |x| ^ beta
    have ha : 0 < a := by
      dsimp [a]
      exact Real.sqrt_pos.2 ht
    have ha_sq : a ^ 2 = t := by
      dsimp [a]
      exact Real.sq_sqrt ht.le
    have hkernel_scale : ∀ y : ℝ,
        gaussianHeatKernel t (a * y) = a⁻¹ * gaussianHeatKernel 1 y := by
      intro y
      unfold gaussianHeatKernel
      have hsqrt : Real.sqrt (4 * Real.pi * t) =
          Real.sqrt (4 * Real.pi) * a := by
        rw [show 4 * Real.pi * t = (4 * Real.pi) * t by ring,
          Real.sqrt_mul (by positivity)]
      rw [hsqrt]
      have hexp : -(a * y) ^ 2 / (4 * t) = -(y ^ 2) / 4 := by
        rw [show (a * y) ^ 2 = a ^ 2 * y ^ 2 by ring, ha_sq]
        field_simp [ht.ne']
      rw [hexp]
      simp only [mul_one]
      ring
    have hscale_rpow : ∀ y : ℝ, |a * y| ^ beta = a ^ beta * |y| ^ beta := by
      intro y
      rw [abs_mul, abs_of_pos ha, Real.mul_rpow ha.le (abs_nonneg y)]
    have hsub : a ^ (beta - 1) = a⁻¹ * a ^ beta := by
      rw [Real.rpow_sub ha beta 1, Real.rpow_one, div_eq_mul_inv]
      ring
    have hcomp_eq : (fun y : ℝ => Ft (a * y)) =
        (fun y : ℝ => a ^ (beta - 1) * F y) := by
      funext y
      dsimp [Ft, F]
      rw [hkernel_scale y, hscale_rpow y, hsub]
      ring
    have hcomp : Integrable (fun y : ℝ => Ft (a * y)) volume := by
      rw [hcomp_eq]
      exact h1.const_mul _
    have hFt : Integrable Ft volume :=
      (integrable_comp_mul_left_iff Ft ha.ne').mp hcomp
    have hchange : (∫ y : ℝ, Ft (a * y)) = a⁻¹ * ∫ x : ℝ, Ft x := by
      simpa [smul_eq_mul, abs_of_pos (inv_pos.mpr ha)] using
        (Measure.integral_comp_mul_left Ft a)
    have hcomp_int : (∫ y : ℝ, Ft (a * y)) = a ^ (beta - 1) * M := by
      rw [hcomp_eq, integral_const_mul]
    have hmoment' : (∫ x : ℝ, Ft x) = a ^ beta * M := by
      have heq : a⁻¹ * (∫ x : ℝ, Ft x) = a ^ (beta - 1) * M :=
        hchange.symm.trans hcomp_int
      calc
        (∫ x : ℝ, Ft x) = a * (a⁻¹ * ∫ x : ℝ, Ft x) := by
          field_simp
        _ = a * (a ^ (beta - 1) * M) := by rw [heq]
        _ = a ^ beta * M := by
          rw [Real.rpow_sub ha beta 1, Real.rpow_one, div_eq_mul_inv]
          field_simp
    have ha_rpow : a ^ beta = t ^ (beta / 2) := by
      dsimp [a]
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
      congr 1
      ring
    refine ⟨hFt, ?_⟩
    rw [hmoment', ha_rpow]
    dsimp [C₀]
    have ht_nonneg : 0 ≤ t ^ (beta / 2) := Real.rpow_nonneg ht.le _
    nlinarith
  let C : ℝ := (3 ^ beta * 3) * C₀
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro t ht
  have hmass : Integrable (gaussianHeatKernel t) (volume : Measure ℝ) ∧
      (∫ x : ℝ, gaussianHeatKernel t x) = 1 :=
    gaussianHeatKernel_mass_semigroup.1 t ht
  have hfrac : Integrable
      (fun x : ℝ => gaussianHeatKernel t x * |x| ^ beta) (volume : Measure ℝ) ∧
      (∫ x : ℝ, gaussianHeatKernel t x * |x| ^ beta) ≤ C₀ * t ^ (beta / 2) :=
    hmoment t ht
  have hform (i : Fin 3) :
      (fun v : Fin 3 → ℝ =>
        (∏ j, gaussianHeatKernel t (v j)) * |v i| ^ beta) =
      (fun v : Fin 3 → ℝ =>
        ∏ j, gaussianHeatKernel t (v j) *
          (if j = i then |v j| ^ beta else 1)) := by
    funext v
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']
    simp
  have hpi (i : Fin 3) : Integrable
      (fun v : Fin 3 → ℝ =>
        (∏ j, gaussianHeatKernel t (v j)) * |v i| ^ beta) volume := by
    rw [hform i]
    refine Integrable.fintype_prod
      (μ := fun _ : Fin 3 => (volume : Measure ℝ))
      (f := fun j (z : ℝ) => gaussianHeatKernel t z *
        (if j = i then |z| ^ beta else 1)) ?_
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hfrac.1
    · simpa [hji] using hmass.1
  have hterm (i : Fin 3) : Integrable
      (fun y : E3 => euclideanHeatKernel 3 t y * |y i| ^ beta) volume := by
    rw [← (PiLp.volume_preserving_toLp (Fin 3)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding]
    simpa [euclideanHeatKernel, Function.comp_def, PiLp.toLp_apply,
      MeasurableEquiv.toLp_apply] using hpi i
  have hfactor (i j : Fin 3) :
      (∫ x : ℝ, gaussianHeatKernel t x *
        (if j = i then |x| ^ beta else 1)) =
        (if j = i then ∫ x : ℝ, gaussianHeatKernel t x * |x| ^ beta else 1) := by
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji, hmass.2]
  have hterm_int (i : Fin 3) :
      (∫ y : E3, euclideanHeatKernel 3 t y * |y i| ^ beta) =
        ∫ x : ℝ, gaussianHeatKernel t x * |x| ^ beta := by
    rw [← (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding]
    have hpi_int :
        (∫ v : Fin 3 → ℝ,
          (∏ j, gaussianHeatKernel t (v j)) * |v i| ^ beta) =
          ∫ x : ℝ, gaussianHeatKernel t x * |x| ^ beta := by
      rw [hform i, integral_fintype_prod_volume_eq_prod
        (f := fun j (z : ℝ) => gaussianHeatKernel t z *
          (if j = i then |z| ^ beta else 1))]
      simp_rw [hfactor i]
      simp
    simpa [euclideanHeatKernel, Function.comp_def, PiLp.toLp_apply,
      MeasurableEquiv.toLp_apply] using hpi_int
  let G : E3 → ℝ := fun y =>
    3 ^ beta * ∑ i : Fin 3, euclideanHeatKernel 3 t y * |y i| ^ beta
  have hG : Integrable G volume := by
    dsimp [G]
    have hsum : Integrable
        (fun y : E3 => ∑ i : Fin 3, euclideanHeatKernel 3 t y * |y i| ^ beta) volume := by
      refine integrable_finsetSum Finset.univ ?_
      intro i hi
      exact hterm i
    exact hsum.const_mul (3 ^ beta)
  have hkernel_cont : Continuous (fun y : E3 => euclideanHeatKernel 3 t y) := by
    unfold euclideanHeatKernel
    exact (contDiff_prod (fun i _ =>
      (gaussianHeatKernel_derivatives ht).1.comp (by fun_prop))).continuous
  have hF_cont : Continuous
      (fun y : E3 => euclideanHeatKernel 3 t y * ‖y‖ ^ beta) := by
    exact hkernel_cont.mul (continuous_norm.rpow_const (fun _ => Or.inr hb))
  have hpoint (y : E3) :
      euclideanHeatKernel 3 t y * ‖y‖ ^ beta ≤ G y := by
    dsimp [G]
    calc
      euclideanHeatKernel 3 t y * ‖y‖ ^ beta ≤
          euclideanHeatKernel 3 t y * (3 ^ beta * ∑ i : Fin 3, |y i| ^ beta) := by
        exact mul_le_mul_of_nonneg_left (hnorm_power y)
          (euclideanHeatKernel_pos 3 ht y).le
      _ = 3 ^ beta * ∑ i : Fin 3, euclideanHeatKernel 3 t y * |y i| ^ beta := by
        rw [← Finset.mul_sum]
        ring
  have hfull : Integrable
      (fun y : E3 => euclideanHeatKernel 3 t y * ‖y‖ ^ beta) volume := by
    refine hG.mono' hF_cont.measurable.aestronglyMeasurable ?_
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hpoint y
    exact mul_nonneg (euclideanHeatKernel_pos 3 ht y).le
      (Real.rpow_nonneg (norm_nonneg y) _)
  have hG_int : (∫ y : E3, G y) =
      (3 ^ beta * 3) * (∫ x : ℝ, gaussianHeatKernel t x * |x| ^ beta) := by
    dsimp [G]
    rw [integral_const_mul, integral_finsetSum Finset.univ]
    · simp_rw [hterm_int]
      simp
      ring
    · intro i hi
      exact hterm i
  refine ⟨hfull, ?_⟩
  have hle :
      (∫ y : E3, euclideanHeatKernel 3 t y * ‖y‖ ^ beta) ≤
        ∫ y : E3, G y :=
    integral_mono hfull hG hpoint
  rw [hG_int] at hle
  dsimp [C]
  calc
    (∫ y : E3, euclideanHeatKernel 3 t y * ‖y‖ ^ beta) ≤
        (3 ^ beta * 3) * (C₀ * t ^ (beta / 2)) := by
          exact hle.trans (mul_le_mul_of_nonneg_left hfrac.2
            (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by norm_num)))
    _ = (3 ^ beta * 3 * C₀) * t ^ (beta / 2) := by ring
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
