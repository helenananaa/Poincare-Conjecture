import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.ComplementClosure
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothNeck
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- The one-dimensional Euclidean neck axis, not a replacement topology. -/
abbrev NativeAxis := EuclideanSpace ℝ (Fin 1)
abbrev NativeCylinder := Sphere2 × NativeAxis
abbrev NativeProductModel := (𝓡 2).prod (𝓡 1)
abbrev nativeModelEquiv :
    (EuclideanSpace ℝ (Fin 2) × NativeAxis) ≃L[ℝ] EuclideanSpace ℝ (Fin (2+1)) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)).symm
abbrev NativeCylinderModel := NativeProductModel.transContinuousLinearEquiv nativeModelEquiv

/-- This is the same finite open-cylinder predicate as the reference epsilon-neck API.
The Riemannian metric estimates are intentionally not assumed by this topological adapter. -/
def nativeNeckDomain (epsilon : ℝ) : TopologicalSpace.Opens NativeCylinder where
  carrier := {p | -epsilon⁻¹ < p.2 0 ∧ p.2 0 < epsilon⁻¹}
  is_open' := by
    have h : Continuous (fun p : NativeCylinder => p.2 0) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp continuous_snd
    exact (isOpen_lt continuous_const h).inter (isOpen_lt h continuous_const)

def scalarNeckDomain (epsilon : ℝ) : TopologicalSpace.Opens (Sphere2 × ℝ) where
  carrier := (univ : Set Sphere2) ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹
  is_open' := isOpen_univ.prod isOpen_Ioo

def nativeAxis (t : ℝ) : NativeAxis :=
  (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).symm t

@[simp] theorem nativeAxis_zero (t : ℝ) : nativeAxis t 0 = t := rfl

def scalarToNative {epsilon : ℝ} (z : scalarNeckDomain epsilon) : nativeNeckDomain epsilon :=
  ⟨(z.1.1, nativeAxis z.1.2), z.2.2⟩

end PoincareConjecture.Topology.FiberSaturation.SmoothNeck
