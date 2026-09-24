import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LinearPullbackSecondDerivative
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.LinearHessianDifferenceTransport
open scoped BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** A uniform Hessian difference bound survives a fixed linear pullback. -/
theorem linear_pullback_hessian_difference_bound
    (f g : E3 → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (S : E3 →L[ℝ] E3) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ (x : E3) (i j : Fin 3),
      |fderiv ℝ (fun z => fderiv ℝ f z (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1) -
       fderiv ℝ (fun z => fderiv ℝ g z (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1)| ≤ K) :
    ∀ (x : E3) (i j : Fin 3),
      |fderiv ℝ (fun z => fderiv ℝ (fun y => f (S y)) z (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1) -
       fderiv ℝ (fun z => fderiv ℝ (fun y => g (S y)) z (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1)| ≤
      9 * K * ‖S‖^2 :=
/- SWARM_PROOF_BEGIN -/
by
  intro x i j
  let e : Fin 3 → E3 := fun k => EuclideanSpace.single k 1
  have repr (w : E3) : (∑ k : Fin 3, w k • e k) = w := by
    ext k
    simp [e, Pi.single_apply]
  have expand (φ : E3 → ℝ) (hφ : ContDiff ℝ 2 φ) (u v : E3) :
      fderiv ℝ (fun y => fderiv ℝ (fun z => φ (S z)) y u) x v =
        ∑ a : Fin 3, ∑ b : Fin 3,
          (S u) a * (S v) b *
            fderiv ℝ (fun y => fderiv ℝ φ y (e a)) (S x) (e b) := by
    rw [MorganTianLib.MetricCoefficient.linear_pullback_second_derivative φ S x u v
      (hφ.contDiffAt)]
    let G : E3 → E3 →L[ℝ] ℝ := fun z => fderiv ℝ φ z
    let A : E3 →L[ℝ] (E3 →L[ℝ] ℝ) := fderiv ℝ G (S x)
    have hG : ContDiff ℝ 1 G := by
      dsimp [G]
      exact hφ.fderiv_right (by norm_num)
    have hGdiff (z : E3) : DifferentiableAt ℝ G z :=
      (hG.differentiable one_ne_zero) z
    have hsecond (u v : E3) :
        fderiv ℝ (fun y => fderiv ℝ φ y u) (S x) v = (A v) u := by
      change fderiv ℝ (fun y => (G y) u) (S x) v = (A v) u
      rw [fderiv_clm_apply (hGdiff (S x)) (differentiableAt_const u)]
      simp [A]
    calc
      fderiv ℝ (fun y => fderiv ℝ φ y (S u)) (S x) (S v) = (A (S v)) (S u) :=
        hsecond (S u) (S v)
      _ = (A (S v)) (∑ a : Fin 3, (S u) a • e a) := by
        exact congrArg (A (S v)) (repr (S u)).symm
      _ = ∑ a : Fin 3, (S u) a * (A (S v)) (e a) := by
        simp only [map_sum, map_smul]
        simp [smul_eq_mul]
      _ = ∑ a : Fin 3, (S u) a *
            (∑ b : Fin 3, (S v) b * (A (e b)) (e a)) := by
        apply Finset.sum_congr rfl
        intro a ha
        congr 1
        have hv := congrArg (fun w => (A w) (e a)) (repr (S v)).symm
        rw [hv]
        simp only [map_sum, map_smul]
        simp [smul_eq_mul]
      _ = ∑ a : Fin 3, ∑ b : Fin 3,
            (S u) a * (S v) b *
              fderiv ℝ (fun y => fderiv ℝ φ y (e a)) (S x) (e b) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        rw [← hsecond (e a) (e b)]
        ring
  have hcoeff₁ (k : Fin 3) : |(S (EuclideanSpace.single i 1)) k| ≤ ‖S‖ := by
    have hcoord : ‖(S (EuclideanSpace.single i 1)) k‖ ≤ ‖S (EuclideanSpace.single i 1)‖ := by
      simpa using (PiLp.norm_apply_le (p := 2) (x := S (EuclideanSpace.single i 1)) k)
    calc
      |(S (EuclideanSpace.single i 1)) k| = ‖(S (EuclideanSpace.single i 1)) k‖ := by simp
      _ ≤ ‖S (EuclideanSpace.single i 1)‖ := hcoord
      _ ≤ ‖S‖ * ‖EuclideanSpace.single i 1‖ := S.le_opNorm _
      _ = ‖S‖ := by simp
  have hcoeff₂ (k : Fin 3) : |(S (EuclideanSpace.single j 1)) k| ≤ ‖S‖ := by
    have hcoord : ‖(S (EuclideanSpace.single j 1)) k‖ ≤ ‖S (EuclideanSpace.single j 1)‖ := by
      simpa using (PiLp.norm_apply_le (p := 2) (x := S (EuclideanSpace.single j 1)) k)
    calc
      |(S (EuclideanSpace.single j 1)) k| = ‖(S (EuclideanSpace.single j 1)) k‖ := by simp
      _ ≤ ‖S (EuclideanSpace.single j 1)‖ := hcoord
      _ ≤ ‖S‖ * ‖EuclideanSpace.single j 1‖ := S.le_opNorm _
      _ = ‖S‖ := by simp
  have hcomponent (a b : Fin 3) :
      |fderiv ℝ (fun y => fderiv ℝ f y (e a)) (S x) (e b) -
        fderiv ℝ (fun y => fderiv ℝ g y (e a)) (S x) (e b)| ≤ K := by
    simpa [e] using h (S x) a b
  have hcombine :
      (∑ a : Fin 3, ∑ b : Fin 3,
        (S (EuclideanSpace.single i 1)) a * (S (EuclideanSpace.single j 1)) b *
          fderiv ℝ (fun y => fderiv ℝ f y (e a)) (S x) (e b)) -
      (∑ a : Fin 3, ∑ b : Fin 3,
        (S (EuclideanSpace.single i 1)) a * (S (EuclideanSpace.single j 1)) b *
          fderiv ℝ (fun y => fderiv ℝ g y (e a)) (S x) (e b)) =
      ∑ a : Fin 3, ∑ b : Fin 3,
        (S (EuclideanSpace.single i 1)) a * (S (EuclideanSpace.single j 1)) b *
          (fderiv ℝ (fun y => fderiv ℝ f y (e a)) (S x) (e b) -
            fderiv ℝ (fun y => fderiv ℝ g y (e a)) (S x) (e b)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  have hterm (a b : Fin 3) :
      |(S (EuclideanSpace.single i 1)) a * (S (EuclideanSpace.single j 1)) b *
        (fderiv ℝ (fun y => fderiv ℝ f y (e a)) (S x) (e b) -
          fderiv ℝ (fun y => fderiv ℝ g y (e a)) (S x) (e b))| ≤
        K * ‖S‖ ^ 2 := by
    rw [abs_mul, abs_mul]
    calc
      |(S (EuclideanSpace.single i 1)) a| * |(S (EuclideanSpace.single j 1)) b| *
          |fderiv ℝ (fun y => fderiv ℝ f y (e a)) (S x) (e b) -
            fderiv ℝ (fun y => fderiv ℝ g y (e a)) (S x) (e b)| ≤
        (‖S‖ * ‖S‖) * K := by
          exact mul_le_mul
            (mul_le_mul (hcoeff₁ a) (hcoeff₂ b) (abs_nonneg _) (norm_nonneg _))
            (hcomponent a b)
            (abs_nonneg _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = K * ‖S‖ ^ 2 := by ring
  calc
    |fderiv ℝ (fun z => fderiv ℝ (fun y => f (S y)) z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single j 1) -
      fderiv ℝ (fun z => fderiv ℝ (fun y => g (S y)) z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single j 1)| =
      |(∑ a : Fin 3, ∑ b : Fin 3,
          (S (EuclideanSpace.single i 1)) a * (S (EuclideanSpace.single j 1)) b *
            fderiv ℝ (fun y => fderiv ℝ f y (e a)) (S x) (e b)) -
        (∑ a : Fin 3, ∑ b : Fin 3,
          (S (EuclideanSpace.single i 1)) a * (S (EuclideanSpace.single j 1)) b *
            fderiv ℝ (fun y => fderiv ℝ g y (e a)) (S x) (e b))| := by
      rw [expand f hf (EuclideanSpace.single i 1) (EuclideanSpace.single j 1),
        expand g hg (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)]
    _ = |∑ a : Fin 3, ∑ b : Fin 3,
          (S (EuclideanSpace.single i 1)) a * (S (EuclideanSpace.single j 1)) b *
            (fderiv ℝ (fun y => fderiv ℝ f y (e a)) (S x) (e b) -
              fderiv ℝ (fun y => fderiv ℝ g y (e a)) (S x) (e b))| := by rw [hcombine]
    _ ≤ ∑ a : Fin 3, ∑ b : Fin 3,
          |(S (EuclideanSpace.single i 1)) a * (S (EuclideanSpace.single j 1)) b *
            (fderiv ℝ (fun y => fderiv ℝ f y (e a)) (S x) (e b) -
              fderiv ℝ (fun y => fderiv ℝ g y (e a)) (S x) (e b))| := by
      calc
        _ ≤ ∑ a : Fin 3,
              |∑ b : Fin 3,
                (S (EuclideanSpace.single i 1)) a * (S (EuclideanSpace.single j 1)) b *
                  (fderiv ℝ (fun y => fderiv ℝ f y (e a)) (S x) (e b) -
                    fderiv ℝ (fun y => fderiv ℝ g y (e a)) (S x) (e b))| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ a : Fin 3, ∑ b : Fin 3,
              |(S (EuclideanSpace.single i 1)) a * (S (EuclideanSpace.single j 1)) b *
                (fderiv ℝ (fun y => fderiv ℝ f y (e a)) (S x) (e b) -
                  fderiv ℝ (fun y => fderiv ℝ g y (e a)) (S x) (e b))| := by
          apply Finset.sum_le_sum
          intro a ha
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, K * ‖S‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact hterm a b
    _ = 9 * K * ‖S‖ ^ 2 := by norm_num [Finset.sum_const]; ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.LinearHessianDifferenceTransport
