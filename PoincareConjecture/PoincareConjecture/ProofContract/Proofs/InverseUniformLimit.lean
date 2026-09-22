import PoincareConjecture.ProofContract.V1.Obligations
import PoincareConjecture.ProofContract.Proofs.CoordinateClosureFrontier
import PoincareConjecture.ProofContract.Proofs.ChartSupportedHomeomorph
import PoincareConjecture.ProofContract.Proofs.EuclideanBallCompression
import PoincareConjecture.ProofContract.Proofs.CoordinateBallShrinking
set_option autoImplicit false
noncomputable section
universe u v
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Filter Topology
open scoped Topology
/-- Simultaneous forward and inverse uniform limits remain an actual homeomorphism. -/
theorem homeomorph_of_uniform_inverse_limits {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]
    (h : ℕ → X ≃ₜ Y) (f : X → Y) (g : Y → X)
    (hf : TendstoUniformly (fun n x => h n x) f atTop)
    (hg : TendstoUniformly (fun n y => (h n).symm y) g atTop) :
    ∃ e : X ≃ₜ Y, (∀ x, e x = f x) ∧ ∀ y, e.symm y = g y :=
/- SWARM_PROOF_BEGIN -/
by
  have hfc : Continuous f :=
    hf.continuous (Filter.Frequently.of_forall fun n => (h n).continuous)
  have hgc : Continuous g :=
    hg.continuous (Filter.Frequently.of_forall fun n => (h n).symm.continuous)
  have hfu : UniformContinuous f := CompactSpace.uniformContinuous_of_continuous hfc
  have hgu : UniformContinuous g := CompactSpace.uniformContinuous_of_continuous hgc
  have hleft : Function.LeftInverse g f := by
    intro x
    have hx : Tendsto (fun n => (h n).symm (h n x)) atTop (𝓝 (g (f x))) :=
      hg.tendsto_comp hgu.continuous.continuousAt (hf.tendsto_at x)
    have hx' : Tendsto (fun _ : ℕ => x) atTop (𝓝 (g (f x))) := by
      simpa using hx
    exact tendsto_nhds_unique hx' tendsto_const_nhds
  have hright : Function.RightInverse g f := by
    intro y
    have hy : Tendsto (fun n => h n ((h n).symm y)) atTop (𝓝 (f (g y))) :=
      hf.tendsto_comp hfu.continuous.continuousAt (hg.tendsto_at y)
    have hy' : Tendsto (fun _ : ℕ => y) atTop (𝓝 (f (g y))) := by
      simpa using hy
    exact tendsto_nhds_unique hy' tendsto_const_nhds
  let e : X ≃ Y :=
    { toFun := f
      invFun := g
      left_inv := hleft
      right_inv := hright }
  refine ⟨Homeomorph.mk e hfc hgc, ?_, ?_⟩
  · intro x
    rfl
  · intro y
    rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
