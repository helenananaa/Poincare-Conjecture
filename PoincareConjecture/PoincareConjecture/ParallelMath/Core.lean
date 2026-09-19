import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath
open Set
/-- Integral of the scalar coefficient; for loop width q = R_min / 2. -/
def rateIntegral (q : ℝ → ℝ) (s t : ℝ) : ℝ := ∫ x in s..t, q x
/-- Explicit solution candidate for w' = -k - q(t) w, w(s)=a. -/
def comparisonSolution (q : ℝ → ℝ) (k a s t : ℝ) : ℝ :=
  Real.exp (-rateIntegral q s t) *
    (a - k * ∫ x in s..t, Real.exp (rateIntegral q s x))
/-- Barrier for w'=-k+alpha/(t+c)*w; c>0 and 0<alpha<1 in applications. -/
def powerBarrier (alpha c a k t : ℝ) : ℝ :=
  (t+c)^alpha * (a/c^alpha - k/(1-alpha)*((t+c)^(1-alpha)-c^(1-alpha)))
/-- A quadratic tensor contraction in a finite orthonormal coordinate frame. -/
def quadraticForm {ι : Type*} [Fintype ι] (A : ι → ι → ℝ) (v : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * v i * v j
end PoincareConjecture.ParallelMath
