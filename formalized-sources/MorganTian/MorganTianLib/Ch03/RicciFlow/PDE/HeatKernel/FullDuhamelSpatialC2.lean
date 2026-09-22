import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.TruncatedDuhamelHessian
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.TruncatedDuhamelFirstDerivative
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.TruncatedDuhamelGradientDerivative
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.UniformC2Limit
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelUniformValueLimit
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelUniformDerivativeLimits
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelBoundedForcing
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelHessianTerminalTail
import Mathlib
open Set MeasureTheory Filter Function
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Actual untruncated Duhamel spatial derivatives, obtained by a checked limit passage. -/
theorem full_duhamel_spatial_C2 (alpha : ℝ) (ha : 0<alpha) (ha1 : alpha<1) :
    ∃ C : ℝ, 0<C ∧ ∀ (F : (ℝ × E3) →ᵇ ℝ) (L T : ℝ), 0≤L → 0<T →
      (∀ s∈Icc (0:ℝ) T, ∀ x y : E3, |F (s,x)-F (s,y)|≤L*‖x-y‖^alpha) →
      let v : E3 → ℝ := fun x => ∫ s in (0:ℝ)..T, ∫ y : E3,
        euclideanHeatKernel 3 (T-s) (x-y)*F (s,y)
      ContDiff ℝ 2 v ∧ ∀ (x : E3) (i j : Fin 3),
        fderiv ℝ (fun z : E3 => fderiv ℝ v z (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single j 1) =
            (∫ s in (0:ℝ)..T, ∫ y : E3,
              fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) z
                (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)*F (s,x-y)) ∧
        |fderiv ℝ (fun z : E3 => fderiv ℝ v z (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single j 1)| ≤ C*L*T^(alpha/2) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨C, hC, hcontrol⟩ :=
    euclideanHeatKernel_three_duhamel_hessian_control alpha ha ha1
  refine ⟨C, hC, ?_⟩
  intro F L T hL hT hHolder
  dsimp
  have hTpos : 0 < T := hT
  let P : Fin 3 → E3 →L[ℝ] ℝ := fun i =>
    PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i
  let eps : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let f : ℕ → E3 → ℝ := fun n x => ∫ s in (0 : ℝ)..(T - eps n),
    ∫ y : E3, euclideanHeatKernel 3 (T-s) (x-y) * F (s,y)
  let q : Fin 3 → ℕ → E3 → ℝ := fun i n x =>
    ∫ s in (0 : ℝ)..(T-eps n), ∫ y : E3,
      fderiv ℝ (euclideanHeatKernel 3 (T-s)) (x-y)
        (EuclideanSpace.single i 1) * F (s,y)
  let r : Fin 3 → Fin 3 → ℕ → E3 → ℝ := fun i j n x =>
    ∫ s in (0 : ℝ)..(T-eps n), ∫ y : E3,
      fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) z
        (EuclideanSpace.single i 1)) (x-y) (EuclideanSpace.single j 1) * F (s,y)
  let qFull : Fin 3 → E3 → ℝ := fun i x =>
    ∫ s in (0 : ℝ)..T, ∫ y : E3,
      fderiv ℝ (euclideanHeatKernel 3 (T-s)) (x-y)
        (EuclideanSpace.single i 1) * F (s,y)
  let rFull : Fin 3 → Fin 3 → E3 → ℝ := fun i j x =>
    ∫ s in (0 : ℝ)..T, ∫ y : E3,
      fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) z
        (EuclideanSpace.single i 1)) (x-y) (EuclideanSpace.single j 1) * F (s,y)
  let A : ℕ → E3 → E3 →L[ℝ] ℝ := fun n x =>
    ∑ i : Fin 3, q i n x • P i
  let AFull : E3 → E3 →L[ℝ] ℝ := fun x =>
    ∑ i : Fin 3, qFull i x • P i
  let B : Fin 3 → ℕ → E3 → E3 →L[ℝ] ℝ := fun i n x =>
    ∑ j : Fin 3, r i j n x • P j
  let BFull : Fin 3 → E3 → E3 →L[ℝ] ℝ := fun i x =>
    ∑ j : Fin 3, rFull i j x • P j
  let H : ℕ → E3 → E3 →L[ℝ] (E3 →L[ℝ] ℝ) := fun n x =>
    ∑ i : Fin 3, (B i n x).smulRight (P i)
  let HFull : E3 → E3 →L[ℝ] (E3 →L[ℝ] ℝ) := fun x =>
    ∑ i : Fin 3, (BFull i x).smulRight (P i)
  have heps_pos (n : ℕ) : 0 < eps n := by
    dsimp [eps]
    positivity
  have heps_le (n : ℕ) : eps n ≤ T := by
    dsimp [eps]
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 2)).2
    have hn : (1 : ℝ) ≤ (n : ℝ) + 2 := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hn hT.le]
  have hP (i : Fin 3) : ‖P i‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro x
    simpa [P, PiLp.proj_apply, Real.norm_eq_abs] using (PiLp.norm_apply_le x i)
  have hsum_limit {a : Fin 3 → ℕ → E3 → ℝ} {b : Fin 3 → E3 → ℝ}
      (hab : ∀ i : Fin 3, TendstoUniformly (fun n => a i n) (b i) atTop) :
      TendstoUniformly
        (fun n x => ∑ i : Fin 3, a i n x • P i)
        (fun x => ∑ i : Fin 3, b i x • P i) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    have hε6 : 0 < ε / 6 := by linarith
    have hall : ∀ᶠ n : ℕ in atTop, ∀ i : Fin 3, ∀ x : E3,
        |b i x - a i n x| < ε / 6 := by
      apply eventually_all.2
      intro i
      have hi := (Metric.tendstoUniformly_iff.mp (hab i)) (ε / 6) hε6
      filter_upwards [hi] with n hn x
      simpa [Real.dist_eq, abs_sub_comm] using hn x
    filter_upwards [hall] with n hn
    intro x
    rw [dist_eq_norm]
    have hdiff :
        (∑ i : Fin 3, b i x • P i) - ∑ i : Fin 3, a i n x • P i =
          ∑ i : Fin 3, (b i x - a i n x) • P i := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      exact (sub_smul (b i x) (a i n x) (P i)).symm
    have hbound :
        ‖(∑ i : Fin 3, b i x • P i) - ∑ i : Fin 3, a i n x • P i‖ ≤ ε / 2 := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by linarith)
      intro v
      rw [hdiff, ContinuousLinearMap.sum_apply]
      calc
        ‖∑ i : Fin 3, (b i x - a i n x) • P i v‖ ≤
            ∑ i : Fin 3, ‖(b i x - a i n x) • P i v‖ := norm_sum_le _ _
        _ ≤ ∑ i : Fin 3, (ε / 6) * ‖v‖ := by
          apply Finset.sum_le_sum
          intro i hi
          rw [norm_smul]
          calc
            ‖b i x - a i n x‖ * ‖P i v‖ ≤
                (ε / 6) * ‖P i v‖ := by
              exact mul_le_mul_of_nonneg_right
                (by simpa [Real.norm_eq_abs] using le_of_lt (hn i x)) (norm_nonneg _)
            _ ≤ (ε / 6) * ‖v‖ := by
              apply mul_le_mul_of_nonneg_left _ (by linarith)
              simpa [P, PiLp.proj_apply, Real.norm_eq_abs] using (PiLp.norm_apply_le v i)
        _ = (ε / 2) * ‖v‖ := by simp; ring
    exact hbound.trans_lt (by linarith)
  have hderiv_limits := duhamel_uniform_derivative_limits alpha ha ha1 F L T hL hT hHolder
  have hq_limit (i : Fin 3) : TendstoUniformly (fun n => q i n) (qFull i) atTop := by
    simpa [q, qFull] using hderiv_limits.1 i
  have hr_limit (i j : Fin 3) : TendstoUniformly (fun n => r i j n) (rFull i j) atTop := by
    simpa [r, rFull] using hderiv_limits.2 i j
  have hA_limit : TendstoUniformly A AFull atTop := by
    apply hsum_limit
    intro i
    exact hq_limit i
  have hB_limit (i : Fin 3) : TendstoUniformly (B i) (BFull i) atTop := by
    apply hsum_limit
    intro j
    exact hr_limit i j
  have hH_limit : TendstoUniformly H HFull atTop := by
    refine (Metric.tendstoUniformly_iff (α := E3 →L[ℝ] (E3 →L[ℝ] ℝ)) (F := H) (f := HFull)).mpr ?_
    intro ε hε
    have hε6 : 0 < ε / 6 := by linarith
    have hall : ∀ᶠ n : ℕ in atTop, ∀ i : Fin 3, ∀ x : E3,
        ‖BFull i x - B i n x‖ < ε / 6 := by
      apply eventually_all.2
      intro i
      have hi := (Metric.tendstoUniformly_iff.mp (hB_limit i)) (ε / 6) hε6
      filter_upwards [hi] with n hn x
      simpa [dist_eq_norm] using hn x
    filter_upwards [hall] with n hn
    intro x
    rw [dist_eq_norm (HFull x) (H n x)]
    have hdiff : HFull x - H n x =
        ∑ i : Fin 3, (BFull i x - B i n x).smulRight (P i) := by
      ext v w
      simp [HFull, H, ContinuousLinearMap.smulRight_apply,
        Finset.sum_sub_distrib, sub_mul]
    have hbound : ‖HFull x - H n x‖ ≤ ε / 2 := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by linarith)
      intro v
      rw [hdiff, ContinuousLinearMap.sum_apply]
      calc
        ‖∑ i : Fin 3, ((BFull i x - B i n x).smulRight (P i)) v‖ ≤
            ∑ i : Fin 3, ‖((BFull i x - B i n x).smulRight (P i)) v‖ :=
              norm_sum_le _ _
        _ ≤ ∑ i : Fin 3, (ε / 6) * ‖v‖ := by
          apply Finset.sum_le_sum
          intro i hi
          rw [ContinuousLinearMap.smulRight_apply, norm_smul]
          calc
            ‖(BFull i x - B i n x) v‖ * ‖P i‖ ≤
                ((ε / 6) * ‖v‖) * ‖P i‖ := by
              apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
              exact (BFull i x - B i n x).le_opNorm v |>.trans
                (mul_le_mul_of_nonneg_right (le_of_lt (hn i x)) (norm_nonneg _))
            _ ≤ (ε / 6) * ‖v‖ := by
              calc
                ((ε / 6) * ‖v‖) * ‖P i‖ ≤ ((ε / 6) * ‖v‖) * 1 :=
                  mul_le_mul_of_nonneg_left (hP i) (by positivity)
                _ = (ε / 6) * ‖v‖ := by ring
        _ = (ε / 2) * ‖v‖ := by simp; ring
    exact hbound.trans_lt (by linarith)
  let vFull : E3 → ℝ := fun x => ∫ s in (0 : ℝ)..T,
    ∫ y : E3, euclideanHeatKernel 3 (T-s) (x-y) * F (s,y)
  have hf : ∀ n : ℕ, ContDiff ℝ 2 (f n) := by
    intro n
    simpa [f, eps] using
      (truncated_duhamel_hessian F T (eps n) (heps_pos n) (heps_le n)).1
  have hfd (n : ℕ) (x : E3) : fderiv ℝ (f n) x = A n x := by
    simpa [f, A, q, P, eps] using
      (truncated_duhamel_first_derivative F T (eps n) (heps_pos n) (heps_le n) x).fderiv
  have hfd2 (n : ℕ) (x : E3) : fderiv ℝ (fderiv ℝ (f n)) x = H n x := by
    have hsum : HasFDerivAt (A n)
        (∑ i : Fin 3, (B i n x).smulRight (P i)) x := by
      dsimp [A]
      apply HasFDerivAt.fun_sum
      intro i hi
      simpa [q, B, P, eps] using
        (truncated_duhamel_gradient_derivative F T (eps n) (heps_pos n)
          (heps_le n) x i).smul_const (P i)
    have hfun : fderiv ℝ (f n) = A n := by
      funext z
      exact hfd n z
    rw [hfun]
    simpa [H] using hsum.fderiv
  have hv_limit : TendstoUniformly f vFull atTop := by
    simpa [f, vFull, eps] using duhamel_uniform_value_limit F T hT
  have hA_limit' : TendstoUniformly (fun n => fderiv ℝ (f n)) AFull atTop := by
    have heq : (fun n : ℕ => A n) =ᶠ[atTop]
        (fun n : ℕ => fderiv ℝ (f n)) :=
      Filter.Eventually.of_forall (fun (n : ℕ) =>
        funext (fun (x : E3) => (hfd n x).symm))
    apply (tendstoUniformly_congr heq).mp
    exact hA_limit
  have hH_limit' :
      TendstoUniformly (fun n => fderiv ℝ (fderiv ℝ (f n))) HFull atTop := by
    have heq : (fun n : ℕ => H n) =ᶠ[atTop]
        (fun n : ℕ => fderiv ℝ (fderiv ℝ (f n))) :=
      Filter.Eventually.of_forall (fun (n : ℕ) =>
        funext (fun (x : E3) => (hfd2 n x).symm))
    apply (tendstoUniformly_congr heq).mp
    exact hH_limit
  obtain ⟨hv2, hvderiv, hHderiv⟩ :=
    contDiff_two_of_uniform_derivative_limits f vFull AFull HFull hf hv_limit
      hA_limit' hH_limit'
  have hA_cont : ContDiff ℝ 1 AFull := by
    rw [← hvderiv]
    exact hv2.fderiv_right (m := 1) (by norm_num)
  have hcoord_deriv (i j : Fin 3) (x : E3) :
      fderiv ℝ (fun z : E3 => AFull z (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single j 1) =
        (HFull x (EuclideanSpace.single j 1)) (EuclideanSpace.single i 1) := by
    have hu : DifferentiableAt ℝ
        (fun _ : E3 => (EuclideanSpace.single i 1 : E3)) x := by
      fun_prop
    have h := fderiv_clm_apply (hA_cont.differentiable (by norm_num) x) hu
    have h' := congrArg (fun L : E3 →L[ℝ] ℝ => L (EuclideanSpace.single j 1)) h
    rw [hHderiv] at h'
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply] using h'
  have hHcoord (i j : Fin 3) (x : E3) :
      (HFull x (EuclideanSpace.single j 1)) (EuclideanSpace.single i 1) =
        rFull i j x := by
    dsimp [HFull, BFull]
    simp [P, PiLp.proj_apply]
  have hFbound : ∀ s ∈ Icc (0 : ℝ) T, ∀ y : E3, |F (s,y)| ≤ ‖F‖ := by
    intro s hs y
    simpa [Real.norm_eq_abs] using F.norm_coe_le_norm (s,y)
  have hchange (i j : Fin 3) (x : E3) :
      rFull i j x = ∫ s in (0 : ℝ)..T, ∫ y : E3,
        fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) z
          (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1) * F (s,x-y) := by
    apply intervalIntegral.integral_congr_ae
    exact Eventually.of_forall (fun s hs => by
      let h : E3 → ℝ := fun y =>
        fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) z
          (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)
      rw [← integral_sub_left_eq_self (fun z : E3 => h z * F (s,x-z)) volume x]
      congr 1
      funext y
      congr 2
      abel)
  have hHolderBound := hcontrol F F.continuous ‖F‖ L T (norm_nonneg F) hL hT.le
    hFbound hHolder
  refine ⟨?_, ?_⟩
  · simpa [vFull] using hv2
  · intro x i j
    have hvcoord (i : Fin 3) :
        (fun z : E3 => fderiv ℝ vFull z (EuclideanSpace.single i 1)) =
          (fun z : E3 => AFull z (EuclideanSpace.single i 1)) := by
      funext z
      rw [hvderiv]
    constructor
    · calc
        fderiv ℝ (fun z : E3 => fderiv ℝ vFull z (EuclideanSpace.single i 1)) x
            (EuclideanSpace.single j 1) =
            fderiv ℝ (fun z : E3 => AFull z (EuclideanSpace.single i 1)) x
              (EuclideanSpace.single j 1) := by rw [hvcoord i]
        _ = (HFull x (EuclideanSpace.single j 1)) (EuclideanSpace.single i 1) :=
          hcoord_deriv i j x
        _ = rFull i j x := hHcoord i j x
        _ = ∫ s in (0 : ℝ)..T, ∫ y : E3,
          fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) z
            (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1) * F (s,x-y) :=
          hchange i j x
    · rw [hvcoord i, hcoord_deriv i j x, hHcoord i j x, hchange i j x]
      exact (hHolderBound i j x).2
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
