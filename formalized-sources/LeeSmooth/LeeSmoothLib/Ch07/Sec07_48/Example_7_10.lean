import LeeSmoothLib.Ch04.Sec04_26.Definition_4_26_extra_1
import LeeSmoothLib.Ch04.Sec04_26.Exercise_4_38
import LeeSmoothLib.Ch04.Sec04_22.Example_4_11
import LeeSmoothLib.Ch04.Sec04_22.Theorem_4_5
import LeeSmoothLib.Ch07.Sec07_47.Example_7_4
-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold Torus ContDiff FourierTransform

-- `lean_leansearch` is unavailable in this session, so the statement below follows the canonical
-- repository owners already used for the torus and complex exponential covering maps.

/-- The one-dimensional Fourier character is a smooth covering map. -/
private theorem circle_fourier_isSmoothCoveringMap :
    Manifold.IsSmoothCoveringMap (𝓘(ℝ)) (𝓡 1) (𝐞 : ℝ → Circle) := by
  change Manifold.IsSmoothCoveringMap (𝓘(ℝ)) (𝓡 1)
    (fun t : ℝ ↦ Circle.exp (2 * Real.pi * t))
  have hne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · simpa [Real.fourierChar_apply', Function.comp_def, smul_eq_mul] using
      Circle.isCoveringMap_exp.comp_homeomorph
        (Homeomorph.smulOfNeZero (2 * Real.pi) hne)
  · simpa [Real.fourierChar_apply', Function.comp_def, smul_eq_mul] using
      Circle.exp_surjective.comp
        (Homeomorph.smulOfNeZero (2 * Real.pi) hne).surjective
  · simpa [Real.fourierChar_apply'] using circle_fourier_exp_isLocalDiffeomorph

/-- Example 7.10 (1): the coordinatewise character `εⁿ : ℝⁿ → 𝕋ⁿ` is a universal smooth covering
map, so the additive Lie group `ℝⁿ` is the universal covering group of the torus `𝕋ⁿ`. -/
theorem torus_epsilon_add_char_isUniversalSmoothCoveringMap (n : ℕ) :
    Manifold.IsUniversalSmoothCoveringMap
      (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓘(ℝ)))
      (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓡 1))
      (ε^{n}) := by
  refine ⟨?_, inferInstance⟩
  simpa [torus_epsilon_add_char] using
    (Manifold.IsSmoothCoveringMap.pi
      (π := fun _ : Fin n ↦ (𝐞 : ℝ → Circle))
      (fun _ ↦ circle_fourier_isSmoothCoveringMap))

/-- The ordinary complex exponential is a local diffeomorphism of the real manifold `ℂ`. -/
private theorem complex_exp_isLocalDiffeomorph_self :
    IsLocalDiffeomorph (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) ∞ Complex.exp := by
  intro z
  refine isLocalDiffeomorphAt_of_contMDiffAt_mfderiv_isInvertible
    (by simp) BoundarylessManifold.isInteriorPoint Complex.contDiff_exp.contMDiff ?_
  rw [mfderiv_eq_fderiv,
    (Complex.hasStrictFDerivAt_exp_real z).hasFDerivAt.fderiv]
  refine ContinuousLinearMap.IsInvertible.of_inverse
    (g := (Complex.exp z)⁻¹ • (1 : ℂ →L[ℝ] ℂ)) ?_ ?_
  · ext w
    unfold TangentSpace at w ⊢
    change Complex.exp z * ((Complex.exp z)⁻¹ * w) = w
    simp [Complex.exp_ne_zero]
  · ext w
    unfold TangentSpace at w ⊢
    change (Complex.exp z)⁻¹ * (Complex.exp z * w) = w
    simp [Complex.exp_ne_zero]

/-- The units inclusion, restricted to its open image, as a partial diffeomorphism. -/
private noncomputable def complexUnitsValPartialDiffeomorph :
    PartialDiffeomorph (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) ℂˣ ℂ ∞ where
  toPartialEquiv :=
    (Units.isOpenEmbedding_val.toOpenPartialHomeomorph (Units.val : ℂˣ → ℂ)).toPartialEquiv
  open_source := isOpen_univ
  open_target := by
    simpa only [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] using
      Units.isOpenEmbedding_val.isOpen_range
  contMDiffOn_toFun := Units.contMDiff_val.contMDiffOn
  contMDiffOn_invFun := by
    unfold Units.instChartedSpace
    convert
      (contMDiffOn_isOpenEmbedding_symm Units.isOpenEmbedding_val :
        ContMDiffOn (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) ∞
          (Units.isOpenEmbedding_val.toOpenPartialHomeomorph
            (Units.val : ℂˣ → ℂ)).symm
          (Set.range (Units.val : ℂˣ → ℂ))) using 1
    · exact OpenPartialHomeomorph.invFun_eq_coe _
    · exact Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target _ _

/-- The units-valued complex exponential is a local diffeomorphism. -/
private theorem complexExpUnits_isLocalDiffeomorph :
    IsLocalDiffeomorph (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) ∞ complexExpUnits := by
  have heq :
      (complexUnitsValPartialDiffeomorph.symm : ℂ → ℂˣ) ∘ Complex.exp =
        complexExpUnits := by
    funext z
    simp only [complexUnitsValPartialDiffeomorph, PartialDiffeomorph.symm,
      Function.comp_apply]
    change
      (Units.isOpenEmbedding_val.toOpenPartialHomeomorph (Units.val : ℂˣ → ℂ)).symm
          (Complex.exp z) = complexExpUnits z
    rw [show Complex.exp z = (complexExpUnits z : ℂ) by rfl]
    exact Units.isOpenEmbedding_val.toOpenPartialHomeomorph_left_inv
  rw [← heq]
  intro z
  exact (complex_exp_isLocalDiffeomorph_self z).comp (𝓘(ℝ, ℂ)) ℂˣ
    (complexUnitsValPartialDiffeomorph.symm.isLocalDiffeomorphAt _ _ _
      (by
        simp only [complexUnitsValPartialDiffeomorph, PartialDiffeomorph.symm]
        rw [PartialEquiv.symm_source,
          Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
        exact ⟨complexExpUnits z, rfl⟩))

/-- The units-valued complex exponential is a topological covering map. -/
private theorem complexExpUnits_isCoveringMap : IsCoveringMap complexExpUnits := by
  have h := Complex.isCoveringMap_exp.homeomorph_comp
    (unitsHomeomorphNeZero (G₀ := ℂ)).symm
  have heq :
      (unitsHomeomorphNeZero (G₀ := ℂ)).symm ∘
          (fun z : ℂ ↦ (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) =
        complexExpUnits := by
    funext z
    apply (unitsHomeomorphNeZero (G₀ := ℂ)).injective
    change
      (unitsHomeomorphNeZero (G₀ := ℂ))
          ((unitsHomeomorphNeZero (G₀ := ℂ)).symm
            ⟨Complex.exp z, Complex.exp_ne_zero z⟩) =
        (unitsHomeomorphNeZero (G₀ := ℂ)) (complexExpUnits z)
    rw [Homeomorph.apply_symm_apply]
    symm
    apply Subtype.ext
    rfl
  rwa [heq] at h

/-- Example 7.10 (2): the complex exponential `ℂ → ℂˣ`, realized by
`complex_exp_units_add_char`, is a universal smooth covering map, so `ℂ` is the universal
covering group of `ℂˣ`. -/
theorem complex_exp_units_add_char_isUniversalSmoothCoveringMap :
    Manifold.IsUniversalSmoothCoveringMap
      (𝓘(ℝ, ℂ))
      (𝓘(ℝ, ℂ))
      complex_exp_units_add_char := by
  refine ⟨⟨?_, complex_exp_units_add_char_surjective, ?_⟩, inferInstance⟩
  · simpa [complex_exp_units_add_char] using complexExpUnits_isCoveringMap
  · simpa [complex_exp_units_add_char] using complexExpUnits_isLocalDiffeomorph
