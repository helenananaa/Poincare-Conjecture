import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.Core
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.NeckAdapter
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- The native one-dimensional Euclidean neck axis is smoothly identified with Real. -/
theorem exists_native_axis_real_diffeomorph {V H X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
    (I : ModelWithCorners ℝ V H) [IsManifold I ∞ X] :
    ∃ e : (X × EuclideanSpace ℝ (Fin 1)) ≃ₘ⟮I.prod (𝓡 1), I.prod (𝓘(ℝ, ℝ))⟯ (X × ℝ),
      ∀ z, e z = (z.1, z.2 0) :=
/- SWARM_PROOF_BEGIN -/
by
  let eAxis : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
    PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
  let dAxis : EuclideanSpace ℝ (Fin 1) ≃ₘ⟮𝓡 1, 𝓘(ℝ, ℝ)⟯ ℝ :=
    eAxis.toDiffeomorph
  refine ⟨{
      toEquiv := (Equiv.refl X).prodCongr dAxis.toEquiv
      contMDiff_toFun := ContMDiff.prodMap contMDiff_id dAxis.contMDiff
      contMDiff_invFun := ContMDiff.prodMap contMDiff_id dAxis.symm.contMDiff }, ?_⟩
  intro z
  rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.NeckAdapter
