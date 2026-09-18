import PoincareConjecture.Topology.FiberSaturation.SmoothPeriodicInverse

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothBundle
open Set Function Manifold
open scoped Manifold ContDiff
variable {V H M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ V H}

/-- All positive and negative iterates retain the given smooth structure. -/
theorem contMDiff_homeomorph_zpow (T : M ≃ₘ⟮I,I⟯ M) (n : ℤ) :
    ContMDiff I I ∞ (T.toHomeomorph ^ n) := by
  induction n using Int.induction_on with
  | zero =>
    have heq : (⇑(T.toHomeomorph ^ (0 : ℤ)) : M → M) = id := by funext x; simp
    rw [heq]
    exact contMDiff_id
  | succ n ih =>
    have heq : (⇑(T.toHomeomorph ^ ((n : ℤ)+1)) : M → M) =
        (T.toHomeomorph ^ (n : ℤ)) ∘ T := by
      funext x
      simp [zpow_add_one]
    rw [heq]
    exact ih.comp T.contMDiff
  | pred n ih =>
    have heq : (⇑(T.toHomeomorph ^ (-(n : ℤ)-1)) : M → M) =
        (T.toHomeomorph ^ (-(n : ℤ))) ∘ T.symm := by
      funext x
      simp [zpow_sub_one]
    rw [heq]
    exact ih.comp T.symm.contMDiff

/-- Smooth integer power, with the underlying map fixed by Homeomorph's group law. -/
def integerDiffeomorph (T : M ≃ₘ⟮I,I⟯ M) (n : ℤ) : M ≃ₘ⟮I,I⟯ M where
  toEquiv := (T.toHomeomorph ^ n).toEquiv
  contMDiff_toFun := contMDiff_homeomorph_zpow T n
  contMDiff_invFun := by
    apply (contMDiff_homeomorph_zpow T (-n)).congr
    intro x
    change (T.toHomeomorph ^ n).symm x = (T.toHomeomorph ^ (-n)) x
    simp [zpow_neg]

/-- The height identity extends to every integer, including negative periods. -/
theorem height_integer_iterate {p : M → ℝ} (T : M ≃ₘ⟮I,I⟯ M) {L : ℝ}
    (hT : ∀ z, p (T z) = p z + L) (n : ℤ) (z : M) :
    p ((T.toHomeomorph ^ n) z) = p z + (n : ℝ)*L := by
  have hTi (w : M) : p (T.symm w) = p w - L := by
    have hh := hT (T.symm w)
    rw [T.apply_symm_apply] at hh
    linarith
  induction n using Int.induction_on generalizing z with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, Homeomorph.mul_apply, ih]
    change p (T z) + (n : ℝ)*L = p z + ((n : ℤ)+1 : ℤ)*L
    rw [hT]
    push_cast
    ring
  | pred n ih =>
    rw [zpow_sub_one, Homeomorph.mul_apply, ih]
    change p (T.symm z) + ((-(n : ℤ) : ℤ) : ℝ)*L = p z + ((-(n : ℤ)-1 : ℤ) : ℝ)*L
    rw [hTi]
    push_cast
    ring

end PoincareConjecture.Topology.FiberSaturation.SmoothBundle
