import PoincareConjecture.ProofContract.V1.Decomposition
import PoincareConjecture.ParallelImplementation.ManifoldInvarianceOfDomain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ClosedSphereCollarOpen
open Set PoincareConjecture.ProofContract.V1
open scoped Manifold Topology
/-- The interior of the ACTUAL given closed sphere collar is an open embedding.
No open-image hypothesis or smoothness of the embedding is assumed. -/
theorem closed_sphere_collar_interior_isOpenEmbedding
    {M : ClosedThreeManifold} (f : Sphere2 × Icc (-1 : ℝ) 1 → M)
    (hf : Topology.IsEmbedding f) :
    let g : Sphere2 × Ioo (-2 : ℝ) 2 → M := fun q =>
      f (q.1, ⟨(q.2 : ℝ) / 2, by constructor <;> linarith [q.2.2.1,q.2.2.2]⟩)
    Topology.IsOpenEmbedding g :=
/- SWARM_PROOF_BEGIN -/
by
  dsimp only
  let ρ : Sphere2 × Ioo (-2 : ℝ) 2 → Sphere2 × Icc (-1 : ℝ) 1 :=
    fun q => (q.1, ⟨(q.2 : ℝ) / 2, by
      constructor <;> linarith [q.2.2.1, q.2.2.2]⟩)
  change Topology.IsOpenEmbedding (f ∘ ρ)
  have hρcont : Continuous ρ := by
    dsimp [ρ]
    fun_prop
  have hρinj : Function.Injective ρ := by
    intro q r h
    simp only [ρ, Prod.mk.injEq] at h
    rcases h with ⟨h₁, h₂eq⟩
    have h₂ : (q.2 : ℝ) = (r.2 : ℝ) := by
      have h' := congrArg Subtype.val h₂eq
      dsimp at h'
      linarith
    exact Prod.ext h₁ (Subtype.ext h₂)
  let eL : Euclidean3 ≃L[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ) :=
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)).trans
      ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2))).prodCongr
        (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)))
  let e : Euclidean3 ≃ₜ ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ :=
    { toEquiv := eL.toEquiv
      continuous_toFun := eL.continuous
      continuous_invFun := eL.symm.continuous }
  letI : ChartedSpace Euclidean3 (ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) :=
    e.chartedSpace
  letI : Nonempty (Ioo (-2 : ℝ) 2) := ⟨⟨0, by norm_num⟩⟩
  letI : ChartedSpace ℝ (Ioo (-2 : ℝ) 2) :=
    isOpen_Ioo.isOpenEmbedding_subtypeVal.singletonChartedSpace
  letI : ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ)
      (Sphere2 × Ioo (-2 : ℝ) 2) := inferInstance
  letI : ChartedSpace Euclidean3 (Sphere2 × Ioo (-2 : ℝ) 2) :=
    ChartedSpace.comp Euclidean3 (ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ)
      (Sphere2 × Ioo (-2 : ℝ) 2)
  exact ManifoldInvarianceOfDomain.isOpenEmbedding_of_continuous_injective
    (E := Euclidean3)
    (f ∘ ρ) (hf.continuous.comp hρcont) (hf.injective.comp hρinj)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ClosedSphereCollarOpen
