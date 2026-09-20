import PoincareConjecture.Topology.FiberSaturation.Sphere

set_option autoImplicit false

namespace PoincareConjecture.Topology.FiberSaturation
open Set

/-- The antipodal map of the unit two-sphere is a homeomorphism. This does not
classify `Diff(S²)` and does not construct the nonorientable circle bundle. -/
def sphere2Antipodal : Sphere2 ≃ₜ Sphere2 where
  toFun x := ⟨-x.1, by simp⟩
  invFun x := ⟨-x.1, by simp⟩
  left_inv x := by
    apply Subtype.ext
    exact neg_neg (x.1 : EuclideanSpace ℝ (Fin 3))
  right_inv x := by
    apply Subtype.ext
    exact neg_neg (x.1 : EuclideanSpace ℝ (Fin 3))
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem sphere2Antipodal_apply (x : Sphere2) :
    (sphere2Antipodal x : EuclideanSpace ℝ (Fin 3)) = -x.1 :=
  rfl

@[simp] theorem sphere2Antipodal_symm :
    (sphere2Antipodal.symm : Sphere2 ≃ₜ Sphere2) = sphere2Antipodal :=
  rfl

end PoincareConjecture.Topology.FiberSaturation
