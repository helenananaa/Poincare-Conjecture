import PoincareConjecture

open Set PoincareConjecture.Topology.FiberSaturation

-- These are actual sphere cylinders, not abstract assumed witnesses.
example : IsOpen ((univ : Set Sphere2) ×ˢ Ioo (-1 : ℝ) 1) :=
  isOpen_univ.prod isOpen_Ioo

example : IsConnected ((univ : Set Sphere2) ×ˢ Ioo (-1 : ℝ) 1) :=
  isConnected_univ.prod ⟨⟨0, by norm_num⟩, isPreconnected_Ioo⟩

example : FiberSaturated (frontier ((univ : Set Sphere2) ×ˢ Ioo (-1 : ℝ) 1)) :=
  frontier_fiberSaturated_univ_prod _

example : (frontier ((univ : Set Sphere2) ×ˢ Ioo (-1 : ℝ) 1)).Nonempty := by
  rw [frontier_univ_prod_eq, frontier_Ioo (by norm_num : (-1 : ℝ) < 1)]
  obtain ⟨x⟩ := (inferInstance : Nonempty Sphere2)
  exact ⟨(x, -1), mem_univ _, by simp⟩

-- The compact-closure hypothesis is inhabited by actual sphere cylinders.
example : IsCompact (closure ((univ : Set Sphere2) ×ˢ Ioo (-1 : ℝ) 1)) := by
  letI : CompactSpace Sphere2 :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
  rw [closure_prod_eq, closure_univ, closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
  exact isCompact_univ.prod isCompact_Icc

-- Empty connected-in-the-preconnected-sense regions are not silently excluded.
example : ∃ A : Set ℝ, IsOpen A ∧ OrdConnected A ∧ A ⊆ (univ : Set ℝ) ∧
    (∅ : Set (Sphere2 × (univ : Set ℝ))) =
      univ ×ˢ ((Subtype.val : ↥(univ : Set ℝ) → ℝ) ⁻¹' A) := by
  apply (fiber_saturation_from_spherical_frontier isOpen_univ
    isOpen_empty isPreconnected_empty ?_).1
  simp [FiberSaturated]
