import Mathlib
import PoincareConjecture.ParallelMath.Variational.Core
import PoincareConjecture.Topology.FiberSaturation.TorusShortStrip
import Mathlib.Topology.Covering.Quotient
import PoincareConjecture.ParallelMath.Transport.TorusCovering
import PoincareConjecture.ParallelMath.Transport.TorusFiberIntegers

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transport
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal Manifold ContDiff

/-- **Math.** For a simply connected fiber, this is a genuine simply connected covering with integer-enumerated fibers. -/
theorem mappingTorus_universal_cover_data {X : Type*} [TopologicalSpace X]
    [SimplyConnectedSpace X] (phi : X ≃ₜ X) (L : ℝ) (hL : 0 < L) :
    IsCoveringMap (PoincareConjecture.Topology.FiberSaturation.MappingTorus.proj phi L) ∧
      SimplyConnectedSpace (X × ℝ) ∧
      ∀ p : X × ℝ, ∃ e : ℤ ≃ {q : X × ℝ //
        PoincareConjecture.Topology.FiberSaturation.MappingTorus.proj phi L q =
          PoincareConjecture.Topology.FiberSaturation.MappingTorus.proj phi L p},
        ∀ n : ℤ, (e n).1 = PoincareConjecture.Topology.FiberSaturation.MappingTorus.deck phi L n p :=
/- SWARM_PROOF_BEGIN -/
by
  refine ⟨mappingTorus_projection_isCoveringMap phi L hL, ?sc,
    mappingTorus_fiber_equiv_integers phi L hL⟩
  case sc =>
    haveI : ContractibleSpace ℝ := inferInstance
    obtain ⟨e⟩ := ContractibleSpace.hequiv_unit ℝ
    exact ((ContinuousMap.HomotopyEquiv.refl X).prodCongr e).trans
      (Homeomorph.prodUnique X Unit).toHomotopyEquiv |>.simplyConnectedSpace
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transport
