import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

namespace LeeVerifiedLie

variable {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]

/-- A central commutator has no nonzero eigenvalue in a finite-dimensional representation.
This is the trace obstruction to extending arbitrary nonzero central characters. -/
theorem central_commutator_eigenvector_eq_zero
    (X Y Z : Module.End 𝕜 V) (hXY : X * Y - Y * X = Z)
    (hXZ : Commute X Z) (hYZ : Commute Y Z)
    {a : 𝕜} (ha : a ≠ 0) {v : V} (hv : Z v = a • v) : v = 0 := by
  let W : Submodule 𝕜 V := (Z - a • LinearMap.id).ker
  have hmem (w : V) : w ∈ W ↔ Z w = a • w := by
    simp [W, LinearMap.mem_ker, sub_eq_zero]
  have hX (w : V) (hw : w ∈ W) : X w ∈ W := by
    apply (hmem _).mpr
    have hc := congrArg (fun L : Module.End 𝕜 V ↦ L w) hXZ.eq.symm
    change Z (X w) = X (Z w) at hc
    rw [hc, (hmem w).mp hw, map_smul]
  have hY (w : V) (hw : w ∈ W) : Y w ∈ W := by
    apply (hmem _).mpr
    have hc := congrArg (fun L : Module.End 𝕜 V ↦ L w) hYZ.eq.symm
    change Z (Y w) = Y (Z w) at hc
    rw [hc, (hmem w).mp hw, map_smul]
  let XW : Module.End 𝕜 W := X.restrict hX
  let YW : Module.End 𝕜 W := Y.restrict hY
  have hcomm : XW * YW - YW * XW = a • LinearMap.id := by
    ext w
    change X (Y (w : V)) - Y (X (w : V)) = a • (w : V)
    have hc := congrArg (fun L : Module.End 𝕜 V ↦ L (w : V)) hXY
    exact hc.trans ((hmem (w : V)).mp w.property)
  have htrace := congrArg (LinearMap.trace 𝕜 W) hcomm
  rw [map_sub, map_smul, LinearMap.trace_mul_comm, sub_self, LinearMap.trace_id] at htrace
  have hdimCast : (Module.finrank 𝕜 W : 𝕜) = 0 := by
    exact (mul_eq_zero.mp htrace.symm).resolve_left ha
  have hdim : Module.finrank 𝕜 W = 0 := Nat.cast_eq_zero.mp hdimCast
  have hW : W = ⊥ := Submodule.finrank_eq_zero.mp hdim
  have hvW : v ∈ W := (hmem v).mpr hv
  simpa [hW] using hvW

/-- In particular, a central commutator cannot act as the identity on a nonzero vector. -/
theorem central_commutator_fixedVector_eq_zero
    (X Y Z : Module.End 𝕜 V) (hXY : X * Y - Y * X = Z)
    (hXZ : Commute X Z) (hYZ : Commute Y Z)
    {v : V} (hv : Z v = v) : v = 0 := by
  exact central_commutator_eigenvector_eq_zero X Y Z hXY hXZ hYZ one_ne_zero
    (by simpa only [one_smul] using hv)

end LeeVerifiedLie
