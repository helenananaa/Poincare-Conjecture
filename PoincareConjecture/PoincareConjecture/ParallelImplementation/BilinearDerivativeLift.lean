import Mathlib
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.IndependentAlgebra
open scoped BigOperators RealInnerProductSpace
theorem hasDerivWithinAt_bilinear_of_evaluations
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (B : ℝ → V →L[ℝ] V →L[ℝ] ℝ) (D : V →L[ℝ] V →L[ℝ] ℝ)
    (J : Set ℝ) (t₀ : ℝ)
    (h : ∀ v w : V, HasDerivWithinAt (fun t : ℝ => B t v w) (D v w) J t₀) :
    HasDerivWithinAt B D J t₀ :=
/- SWARM_PROOF_BEGIN -/
by
  let n : ℕ := Module.finrank ℝ V
  let b : Module.Basis (Fin n) ℝ V := Module.finBasisOfFinrankEq ℝ V (by rfl)
  let e : V ≃L[ℝ] (Fin n → ℝ) := b.equivFun.toContinuousLinearEquiv
  let e₂ : (V →L[ℝ] ℝ) ≃L[ℝ] (Fin n → ℝ) :=
    (e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)).trans
      (ContinuousLinearEquiv.piRing (Fin n))
  let e₃ : (V →L[ℝ] V →L[ℝ] ℝ) ≃L[ℝ] (Fin n → Fin n → ℝ) :=
    (e.arrowCongr e₂).trans (ContinuousLinearEquiv.piRing (Fin n))
  have hcoord : ∀ i j : Fin n,
      HasDerivWithinAt (fun t : ℝ => e₃ (B t) i j) (e₃ D i j) J t₀ := by
    intro i j
    simpa [e₃, e₂, e, ContinuousLinearEquiv.piRing] using h (b i) (b j)
  have hmatrix : HasDerivWithinAt (fun t : ℝ => e₃ (B t)) (e₃ D) J t₀ := by
    apply hasDerivWithinAt_pi.2
    intro i
    apply hasDerivWithinAt_pi.2
    intro j
    exact hcoord i j
  let L : (Fin n → Fin n → ℝ) →L[ℝ] (V →L[ℝ] V →L[ℝ] ℝ) :=
    e₃.symm.toContinuousLinearMap
  have hcomp : HasFDerivWithinAt (fun t : ℝ => L (e₃ (B t)))
      (L.comp (ContinuousLinearMap.toSpanSingleton ℝ (e₃ D))) J t₀ := by
    exact L.hasFDerivAt.comp_hasFDerivWithinAt t₀ hmatrix.hasFDerivWithinAt
  have hlinear : L.comp (ContinuousLinearMap.toSpanSingleton ℝ (e₃ D)) =
      ContinuousLinearMap.toSpanSingleton ℝ D := by
    ext r
    simp [L]
  have hfinal : HasFDerivWithinAt (fun t : ℝ => B t)
      (ContinuousLinearMap.toSpanSingleton ℝ D) J t₀ := by
    rw [← hlinear]
    simpa [L, Function.comp_def] using hcomp
  simpa using hfinal.hasDerivWithinAt
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.IndependentAlgebra
