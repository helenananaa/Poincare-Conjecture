import DoCarmoLib.Riemannian.Manifold.DoCarmoCh4Ricci

open Riemannian
noncomputable section
namespace MorganTianLib.SurgeryCap
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- **Math.** In dimension three the scalar trace is twice the sum of the three sectional numerators of an orthonormal basis. -/
theorem scalarCurvature_three_trace {B : V → V → V → V → ℝ}
    (hB : IsAlgCurvatureForm B) (e : OrthonormalBasis (Fin 3) ℝ V) :
    scalarCurvature hB = 2 * (B (e 0) (e 1) (e 0) (e 1) +
      B (e 0) (e 2) (e 0) (e 2) + B (e 1) (e 2) (e 1) (e 2)) := by
  rw [scalarCurvature_eq_sum hB e]
  have hdiag (v : V) : B v v v v = 0 := by
    have h := hB.antisymm₁₂ v v v v
    linarith
  have hswap (v w : V) : B w v w v = B v w v w := by
    rw [hB.antisymm₁₂ w v w v, hB.antisymm₃₄ v w w v, neg_neg]
  norm_num [Fin.sum_univ_succ, hdiag, hswap]
  rw [hswap (e 0) (e 1)]
  ring

end MorganTianLib.SurgeryCap
