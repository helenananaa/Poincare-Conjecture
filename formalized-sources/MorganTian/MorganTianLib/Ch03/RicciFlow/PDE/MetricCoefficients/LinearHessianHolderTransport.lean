import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LinearPullbackSecondDerivative
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)

/-- **Math.** linear hessian holder transport. -/
theorem linear_hessian_holder_transport 
    (f : E3 → ℝ) (hf : ContDiff ℝ 2 f) (B : E3 →L[ℝ] E3)
    (alpha H : ℝ) (ha : 0 < alpha) (hH : 0 ≤ H)
    (hhold : ∀ x z : E3, ∀ i j : Fin 3,
      |fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1)-
       fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) z (EuclideanSpace.single j 1)| ≤ H*‖x-z‖^alpha) :
    ∀ x z : E3, ∀ i j : Fin 3,
      |fderiv ℝ (fun y => fderiv ℝ (fun w => f (B w)) y (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1)-
       fderiv ℝ (fun y => fderiv ℝ (fun w => f (B w)) y (EuclideanSpace.single i 1)) z (EuclideanSpace.single j 1)| ≤
      (9*H*‖B‖^2*‖B‖^alpha)*‖x-z‖^alpha :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  intro x z
  let e : Fin 3 → E3 := fun i => EuclideanSpace.single i (1 : ℝ)
  let K : E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ := fun q =>
    fderiv ℝ (fderiv ℝ f) (B q)
  have hdecomp (v : E3) : v = ∑ i : Fin 3, v i • e i := by
    simpa [e, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
      ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v).symm
  have h_eval (q v w : E3) :
      fderiv ℝ (fun y => fderiv ℝ f y v) (B q) w = K q w v := by
    have hfAt : ContDiffAt ℝ 2 f (B q) := by
      intro n hn
      exact hf.contDiffAt (x := B q) n (by exact_mod_cast hn)
    have hfderiv : ContDiffAt ℝ 1 (fderiv ℝ f) (B q) :=
      hfAt.fderiv_right (by norm_num)
    have hdiff : DifferentiableAt ℝ (fderiv ℝ f) (B q) :=
      hfderiv.differentiableAt (by norm_num)
    have h := fderiv_clm_apply hdiff
      (differentiableAt_const (c := v) (x := B q))
    have h' := congrArg (fun L : E3 →L[ℝ] ℝ => L w) h
    simpa [K] using h'
  have hbilin (q u v : E3) :
      K q u v = ∑ r : Fin 3, ∑ s : Fin 3,
        u r * v s * K q (e r) (e s) := by
    calc
      K q u v = ∑ r : Fin 3, (u r) • K q (e r) v := by
        rw [hdecomp u]
        simp only [map_sum, map_smul]
        simp [e, Pi.single_apply]
      _ = ∑ r : Fin 3, u r * (∑ s : Fin 3, v s * K q (e r) (e s)) := by
        congr 1
        funext r
        rw [hdecomp v]
        simp only [map_sum, map_smul, smul_eq_mul]
        simp [e, Pi.single_apply]
      _ = ∑ r : Fin 3, ∑ s : Fin 3,
          u r * v s * K q (e r) (e s) := by
        simp_rw [Finset.mul_sum, mul_assoc]
  have hcoord : ∀ (v : E3) (i : Fin 3), |v i| ≤ ‖v‖ := by
    intro v i
    have hnorm : ‖v i‖ ≤ ‖v‖ := by
      rw [EuclideanSpace.norm_eq]
      have hnonneg : 0 ≤ ∑ r : Fin 3, ‖v.ofLp r‖ ^ 2 :=
        Finset.sum_nonneg (fun r _ => sq_nonneg _)
      apply (Real.le_sqrt (norm_nonneg _) hnonneg).2
      exact Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin 3)))
        (f := fun r : Fin 3 => ‖v.ofLp r‖ ^ 2)
        (fun r _ => sq_nonneg _) (Finset.mem_univ i)
    simpa [Real.norm_eq_abs] using hnorm
  have hBcoord (i r : Fin 3) : |(B (e i)) r| ≤ ‖B‖ := by
    calc
      |(B (e i)) r| ≤ ‖B (e i)‖ := hcoord _ _
      _ ≤ ‖B‖ * ‖e i‖ := B.le_opNorm _
      _ = ‖B‖ := by simp [e]
  have hdisp : ‖B x - B z‖ ≤ ‖B‖ * ‖x - z‖ := by
    calc
      ‖B x - B z‖ = ‖B (x - z)‖ := by rw [map_sub]
      _ ≤ ‖B‖ * ‖x - z‖ := B.le_opNorm _
  have hpow : ‖B x - B z‖ ^ alpha ≤ ‖B‖ ^ alpha * ‖x - z‖ ^ alpha := by
    calc
      ‖B x - B z‖ ^ alpha ≤ (‖B‖ * ‖x - z‖) ^ alpha :=
        Real.rpow_le_rpow (norm_nonneg _) hdisp ha.le
      _ = ‖B‖ ^ alpha * ‖x - z‖ ^ alpha :=
        Real.mul_rpow (norm_nonneg _) (norm_nonneg _)
  have hcoordDiff (r s : Fin 3) :
      |K x (e r) (e s) - K z (e r) (e s)| ≤ H * ‖B x - B z‖ ^ alpha := by
    rw [← h_eval x (e s) (e r), ← h_eval z (e s) (e r)]
    exact hhold (B x) (B z) s r
  have hpull (q : E3) (i j : Fin 3) :
      fderiv ℝ (fun y => fderiv ℝ (fun w => f (B w)) y (e i)) q (e j) =
        K q (B (e j)) (B (e i)) := by
    have hfAt : ContDiffAt ℝ 2 f (B q) := by
      intro n hn
      exact hf.contDiffAt (x := B q) n (by exact_mod_cast hn)
    rw [linear_pullback_second_derivative f B q (e i) (e j) hfAt]
    exact h_eval q (B (e i)) (B (e j))
  have hexpand (i j : Fin 3) :
      K x (B (e j)) (B (e i)) - K z (B (e j)) (B (e i)) =
        ∑ r : Fin 3, ∑ s : Fin 3,
          (B (e j)) r * (B (e i)) s *
            (K x (e r) (e s) - K z (e r) (e s)) := by
    rw [hbilin x (B (e j)) (B (e i)), hbilin z (B (e j)) (B (e i))]
    calc
      (∑ r : Fin 3, ∑ s : Fin 3,
          (B (e j)) r * (B (e i)) s * K x (e r) (e s)) -
        (∑ r : Fin 3, ∑ s : Fin 3,
          (B (e j)) r * (B (e i)) s * K z (e r) (e s)) =
          ∑ r : Fin 3,
            ((∑ s : Fin 3, (B (e j)) r * (B (e i)) s * K x (e r) (e s)) -
              (∑ s : Fin 3, (B (e j)) r * (B (e i)) s * K z (e r) (e s))) := by
        rw [← Finset.sum_sub_distrib]
      _ = ∑ r : Fin 3, ∑ s : Fin 3,
          ((B (e j)) r * (B (e i)) s * K x (e r) (e s) -
            (B (e j)) r * (B (e i)) s * K z (e r) (e s)) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [← Finset.sum_sub_distrib]
      _ = ∑ r : Fin 3, ∑ s : Fin 3,
          (B (e j)) r * (B (e i)) s *
            (K x (e r) (e s) - K z (e r) (e s)) := by
        apply Finset.sum_congr rfl
        intro r _
        apply Finset.sum_congr rfl
        intro s _
        ring
  have hterm (i j r s : Fin 3) :
      |(B (e j)) r * (B (e i)) s *
          (K x (e r) (e s) - K z (e r) (e s))| ≤
        ‖B‖ ^ 2 * (H * ‖B x - B z‖ ^ alpha) := by
    rw [abs_mul, abs_mul]
    calc
      |(B (e j)) r| * |(B (e i)) s| *
          |K x (e r) (e s) - K z (e r) (e s)| ≤
        (‖B‖ * ‖B‖) * |K x (e r) (e s) - K z (e r) (e s)| := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul (hBcoord j r) (hBcoord i s)
              (abs_nonneg _) (norm_nonneg _)) (abs_nonneg _)
      _ ≤ (‖B‖ * ‖B‖) * (H * ‖B x - B z‖ ^ alpha) :=
        mul_le_mul_of_nonneg_left (hcoordDiff r s) (by positivity)
      _ = ‖B‖ ^ 2 * (H * ‖B x - B z‖ ^ alpha) := by rw [pow_two]
  have hbound (i j : Fin 3) :
      |K x (B (e j)) (B (e i)) - K z (B (e j)) (B (e i))| ≤
        9 * ‖B‖ ^ 2 * (H * ‖B x - B z‖ ^ alpha) := by
    rw [hexpand]
    calc
      |∑ r : Fin 3, ∑ s : Fin 3,
          (B (e j)) r * (B (e i)) s *
            (K x (e r) (e s) - K z (e r) (e s))| ≤
        ∑ r : Fin 3, ∑ s : Fin 3,
          |(B (e j)) r * (B (e i)) s *
            (K x (e r) (e s) - K z (e r) (e s))| := by
          calc
            |∑ r : Fin 3, ∑ s : Fin 3, _| ≤
                ∑ r : Fin 3, |∑ s : Fin 3,
                  (B (e j)) r * (B (e i)) s *
                    (K x (e r) (e s) - K z (e r) (e s))| :=
              Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ r : Fin 3, ∑ s : Fin 3,
                |(B (e j)) r * (B (e i)) s *
                  (K x (e r) (e s) - K z (e r) (e s))| := by
              apply Finset.sum_le_sum
              intro r _
              exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r : Fin 3, ∑ s : Fin 3,
          (‖B‖ ^ 2 * (H * ‖B x - B z‖ ^ alpha)) := by
        apply Finset.sum_le_sum
        intro r _
        apply Finset.sum_le_sum
        intro s _
        exact hterm i j r s
      _ = 9 * ‖B‖ ^ 2 * (H * ‖B x - B z‖ ^ alpha) := by
        simp
        ring
  intro i j
  rw [hpull x i j, hpull z i j]
  calc
    |K x (B (e j)) (B (e i)) - K z (B (e j)) (B (e i))| ≤
        9 * ‖B‖ ^ 2 * (H * ‖B x - B z‖ ^ alpha) := hbound i j
    _ ≤ 9 * ‖B‖ ^ 2 * (H * (‖B‖ ^ alpha * ‖x - z‖ ^ alpha)) := by
      gcongr
    _ = (9 * H * ‖B‖ ^ 2 * ‖B‖ ^ alpha) * ‖x - z‖ ^ alpha := by ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
