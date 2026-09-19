import ReferenceBridges.WidthTorus.AxialLoop
import ReferenceBridges.WidthTorus.CircleProjection
import PoincareConjecture.Topology.FiberSaturation.MappingTorus
import PoincareConjecture.Topology.FiberSaturation.Sphere
import HatcherLib.Ch1.Circle
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.TorusObstruction
open Set Function
open scoped Topology unitInterval
open PoincareConjecture.Topology.FiberSaturation

/-- Every nonempty path-connected mapping torus surjects onto the circle
winding generator, so it is not simply connected; no trivial monodromy is required. -/
theorem mappingTorus_not_simplyConnected {X : Type*} [TopologicalSpace X]
    [Nonempty X] [PathConnectedSpace X] (φ : X ≃ₜ X) :
    ¬ SimplyConnectedSpace (MappingTorus.Space φ 1) :=
/- SWARM_PROOF_BEGIN -/
by
  intro hsc
  haveI := hsc
  inhabit X
  let x : X := default
  let γ : Path x (φ x) := PathConnectedSpace.somePath x (φ x)
  obtain ⟨q, hq⟩ := mappingTorus_axial_loop φ x γ
  obtain ⟨P, hP⟩ := mappingTorus_circle_projection φ
  let x₀ : MappingTorus.Space φ 1 := MappingTorus.proj φ 1 (x, 0)
  have hsrc : P x₀ = (0 : HatcherLib.UnitCircle) := by
    simpa [x₀] using hP x 0
  have himg :
      (q.map P.continuous).cast hsrc.symm hsrc.symm =
        HatcherLib.unitCircleWindingLoop 1 := by
    ext t
    change P (q t) = HatcherLib.unitCircleWindingLoop 1 t
    rw [hq t, hP]
    simp [HatcherLib.unitCircleWindingLoop]
  have hrefl :
      ((Path.refl x₀).map P.continuous).cast hsrc.symm hsrc.symm =
        Path.refl (0 : HatcherLib.UnitCircle) := by
    ext t
    exact hsrc
  have hnull :
      Path.Homotopic (HatcherLib.unitCircleWindingLoop 1)
        (Path.refl (0 : HatcherLib.UnitCircle)) := by
    rw [← himg, ← hrefl]
    exact Path.Homotopic.pathCast
      (Path.Homotopic.map (SimplyConnectedSpace.paths_homotopic q (Path.refl x₀)) P)
      hsrc.symm hsrc.symm
  have hw1 :
      FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (HatcherLib.unitCircleWindingLoop 1)) =
        FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (Path.refl (0 : HatcherLib.UnitCircle))) :=
    congrArg _ (Path.Homotopic.Quotient.eq.mpr hnull)
  have hrefleq :
      FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (Path.refl (0 : HatcherLib.UnitCircle))) =
        1 :=
    rfl
  have hcontr := HatcherLib.circleFundamentalGroupMulEquiv_windingLoop (1 : ℤ)
  rw [hw1, hrefleq, map_one] at hcontr
  exact (one_ne_zero : (1 : ℤ) ≠ 0)
    (congrArg Multiplicative.toAdd hcontr).symm
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.TorusObstruction
