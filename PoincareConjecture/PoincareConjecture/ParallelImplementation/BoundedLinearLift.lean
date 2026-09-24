import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.BoundedLinearLift
/-- Bounded preimages of a linear map lift linearly through an injective linear map. -/
theorem exists_bounded_linear_lift
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [AddCommGroup Z] [Module ℝ Z]
    (Q : Y →ₗ[ℝ] Z) (hQ : Function.Injective Q) (v : X →ₗ[ℝ] Z)
    (C : ℝ) (hC : 0 ≤ C)
    (hlift : ∀ x : X, ∃ y : Y, Q y = v x ∧ ‖y‖ ≤ C * ‖x‖) :
    ∃ D : X →L[ℝ] Y, ‖D‖ ≤ C ∧ ∀ x : X, Q (D x) = v x :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  choose f hf using hlift
  have hadd : ∀ x y : X, f (x + y) = f x + f y := by
    intro x y
    apply hQ
    calc
      Q (f (x + y)) = v (x + y) := (hf (x + y)).1
      _ = v x + v y := map_add v x y
      _ = Q (f x) + Q (f y) := by rw [(hf x).1, (hf y).1]
      _ = Q (f x + f y) := (map_add Q (f x) (f y)).symm
  have hsmul : ∀ (a : ℝ) (x : X), f (a • x) = a • f x := by
    intro a x
    apply hQ
    calc
      Q (f (a • x)) = v (a • x) := (hf (a • x)).1
      _ = a • v x := map_smul v a x
      _ = a • Q (f x) := by rw [(hf x).1]
      _ = Q (a • f x) := (map_smul Q a (f x)).symm
  let fLin : X →ₗ[ℝ] Y :=
    { toFun := f
      map_add' := hadd
      map_smul' := hsmul }
  have hbound : ∀ x : X, ‖fLin x‖ ≤ C * ‖x‖ := by
    intro x
    exact (hf x).2
  let D : X →L[ℝ] Y := fLin.mkContinuous C hbound
  refine ⟨D, ?_, ?_⟩
  · change ‖fLin.mkContinuous C hbound‖ ≤ C
    exact LinearMap.mkContinuous_norm_le fLin hC hbound
  · intro x
    change Q (f x) = v x
    exact (hf x).1
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.BoundedLinearLift
