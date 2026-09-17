import PoincareConjecture

open Set PoincareConjecture.Topology.FiberSaturation

-- Both endpoint fibers occur in an actual sphere cylinder.
example (x : Sphere2) :
    connectedComponentIn ((univ : Set Sphere2) ×ˢ ({(-1 : ℝ), 1} : Set ℝ)) (x, -1) =
      univ ×ˢ ({(-1 : ℝ)} : Set ℝ) :=
  componentIn_two_fibers (-1 : ℝ) 1 (by norm_num) x

-- The normalization is constructed, not merely assumed to exist.
example : Nonempty
    (↥((univ : Set Sphere2) ×ˢ
      ((Subtype.val : Ioo (-2 : ℝ) 2 → ℝ) ⁻¹' Icc (-1 : ℝ) 1)) ≃ₜ
      (Sphere2 × Icc (0 : ℝ) 1)) := by
  refine ⟨relativeClosedCylinderUnitHomeomorph ?_ (by norm_num : (-1 : ℝ) < 1)⟩
  intro x hx
  constructor <;> linarith [hx.1, hx.2]

-- A finite disjoint closed family has the advertised genuine components.
example : connectedComponentIn (⋃ i : Bool, if i then ({1} : Set ℝ) else {0}) 0 = {0} := by
  let F : Bool → Set ℝ := fun i => if i then {1} else {0}
  have hclosed : ∀ i, IsClosed (F i) := by intro i; cases i <;> exact isClosed_singleton
  have hconn : ∀ i, IsPreconnected (F i) := by intro i; cases i <;> exact isPreconnected_singleton
  have hdis : Pairwise (fun i j => Disjoint (F i) (F j)) := by
    intro i j h
    cases i <;> cases j <;> simp_all [F]
  exact componentIn_finite_disjoint_closed F hclosed hconn hdis false (by simp [F])

-- Instantiate all hypotheses of the product-branch theorem on S² × (-1,1).
example : Nonempty
    (↥(closure ((univ : Set Sphere2) ×ˢ
      ((Subtype.val : ↥(univ : Set ℝ) → ℝ) ⁻¹' Ioo (-1 : ℝ) 1))) ≃ₜ
        (Sphere2 × Icc (0 : ℝ) 1)) := by
  let lift : Sphere2 × ℝ → Sphere2 × ↥(univ : Set ℝ) :=
    fun p => (p.1, ⟨p.2, mem_univ _⟩)
  have hlift : Continuous lift := by fun_prop
  have himage (A : Set ℝ) : lift '' ((univ : Set Sphere2) ×ˢ A) =
      (univ : Set Sphere2) ×ˢ ((Subtype.val : ↥(univ : Set ℝ) → ℝ) ⁻¹' A) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq
    · intro hp
      exact ⟨(p.1, (p.2 : ℝ)), hp, rfl⟩
  have ho : IsOpen ((univ : Set Sphere2) ×ˢ
      ((Subtype.val : ↥(univ : Set ℝ) → ℝ) ⁻¹' Ioo (-1 : ℝ) 1)) :=
    isOpen_univ.prod (isOpen_Ioo.preimage continuous_subtype_val)
  have hc : IsConnected ((univ : Set Sphere2) ×ˢ
      ((Subtype.val : ↥(univ : Set ℝ) → ℝ) ⁻¹' Ioo (-1 : ℝ) 1)) := by
    rw [← himage]
    exact (isConnected_univ.prod
      ⟨⟨0, by norm_num⟩, isPreconnected_Ioo⟩).image _ hlift.continuousOn
  have hk : IsCompact (closure ((univ : Set Sphere2) ×ˢ
      ((Subtype.val : ↥(univ : Set ℝ) → ℝ) ⁻¹' Ioo (-1 : ℝ) 1))) := by
    letI : CompactSpace Sphere2 := isCompact_iff_compactSpace.mp
      (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    rw [closure_prod_eq, closure_univ,
      ← isOpen_univ.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
        continuous_subtype_val, closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1), ← himage]
    exact (isCompact_univ.prod isCompact_Icc).image hlift
  exact (relative_fiber_boundary_pairing_product isOpen_univ ordConnected_univ
    ho hc (frontier_fiberSaturated_univ_prod _) hk).1
