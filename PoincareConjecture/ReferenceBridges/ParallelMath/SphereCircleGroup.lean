import HatcherLib.Ch1.Circle
import HatcherLib.Ch1.Sphere
import PoincareConjecture.Topology.FiberSaturation.Sphere
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Reference
open Set Function Filter
open scoped BigOperators Topology Manifold ContDiff Bundle RealInnerProductSpace

/-- The product sphere bundle over the circle has infinite cyclic fundamental group. -/
theorem sphere2_circle_fundamentalGroup
    (x : PoincareConjecture.Topology.FiberSaturation.Sphere2) :
    Nonempty (FundamentalGroup
      (PoincareConjecture.Topology.FiberSaturation.Sphere2 × HatcherLib.UnitCircle)
      (x,0) ≃* Multiplicative ℤ) :=
/- SWARM_PROOF_BEGIN -/
by
  letI : SimplyConnectedSpace
      PoincareConjecture.Topology.FiberSaturation.Sphere2 :=
    HatcherLib.standardSphereSimplyConnected 0
  letI : Unique
      (FundamentalGroup PoincareConjecture.Topology.FiberSaturation.Sphere2 x) :=
    uniqueOfSubsingleton 1
  exact ⟨(HatcherLib.fundamentalGroupProdMulEquiv x (0 : HatcherLib.UnitCircle)).symm.trans
    (MulEquiv.uniqueProd.trans HatcherLib.circleFundamentalGroupMulEquiv)⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Reference
