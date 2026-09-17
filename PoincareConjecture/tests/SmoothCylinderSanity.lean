import PoincareConjecture

open Set Manifold PoincareConjecture.Topology.FiberSaturation
open scoped Manifold ContDiff
noncomputable section

local instance : Fact ((-2 : ℝ) < 3) := ⟨by norm_num⟩
local instance : Fact ((3 : ℝ) < 4) := ⟨by norm_num⟩

-- The interval keeps its standard left and right boundary charts.
example : IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞
    (Subtype.val : Icc (-2 : ℝ) 3 → ℝ) := Icc_subtype_smoothEmbedding (-2) 3

example : ((iccDiffeomorphUnit (-2) 3 ⟨-2, by norm_num⟩ : Icc (0 : ℝ) 1) : ℝ) = 0 := by
  change ((-2 : ℝ) - (-2)) / (3 - (-2)) = 0
  norm_num

example : ((iccDiffeomorphUnit (-2) 3 ⟨3, by norm_num⟩ : Icc (0 : ℝ) 1) : ℝ) = 1 := by
  change ((3 : ℝ) - (-2)) / (3 - (-2)) = 1
  norm_num

example : ((iccDiffeomorphUnit (-2) 3).symm ⟨1, by norm_num⟩ : ℝ) = 3 := by
  change (3 - (-2 : ℝ)) * 1 + (-2) = 3
  norm_num

-- A genuine sphere cylinder, with the ordinary sphere and interval structures.
example : (Sphere2 × Icc (-2 : ℝ) 3) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1),
    (𝓡 2).prod (𝓡∂ 1)⟯ (Sphere2 × Icc (0 : ℝ) 1) :=
  cylinderDiffeomorphUnit (𝓡 2) (-2) 3

-- A nonidentity local diffeomorphism connects two different embedded intervals.
example : Icc (0 : ℝ) 1 ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc (3 : ℝ) 4 := by
  let e := (iccHomeoI (3 : ℝ) 4 (by norm_num)).symm
  apply diffeomorphOfLocalDiffeomorphComparison
    (Icc_subtype_smoothEmbedding 0 1) (Icc_subtype_smoothEmbedding 3 4)
    (realTranslation 3).isLocalDiffeomorph e
  intro p
  change (4 - (3 : ℝ)) * (p : ℝ) + 3 = (p : ℝ) + 3
  ring

-- The resulting diffeomorphism carries the intrinsic boundary onto both ends.
example : (cylinderDiffeomorphUnit (𝓡 2) (-2) 3) ''
    ((𝓡 2).prod (𝓡∂ 1)).boundary (Sphere2 × Icc (-2 : ℝ) 3) =
    (univ : Set Sphere2) ×ˢ ({⊥, ⊤} : Set (Icc (0 : ℝ) 1)) := by
  rw [(cylinderDiffeomorphUnit (𝓡 2) (-2) 3).image_boundary (by simp)]
  exact boundary_product (𝓡 2)

-- The equal-image comparison works with the standard nonempty half-space.
example : EuclideanHalfSpace 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ EuclideanHalfSpace 3 :=
  diffeomorphOfEqualEmbeddingRange (model_inclusion_smoothEmbedding (𝓡∂ 3))
    (model_inclusion_smoothEmbedding (𝓡∂ 3)) rfl

-- A smooth map can have a nonsmooth inverse: the local-diffeomorphism input
-- cannot be replaced by continuity or forward smoothness alone.
example : ContDiff ℝ ∞ (fun x : ℝ => x^3) := by fun_prop

example : ¬ IsLocalDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun x : ℝ => x^3) := by
  intro h
  let l := (h 0).mfderivToContinuousLinearEquiv (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hz : fderiv ℝ (fun x : ℝ => x^3) 0 = 0 := by
    have hd : HasDerivAt (fun x : ℝ => x^3) 0 0 := by
      simpa using! (hasDerivAt_id (0 : ℝ)).pow 3
    simpa using hd.hasFDerivAt.fderiv
  have heq : l 1 = l 0 := by
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun x : ℝ => x^3) 0 1 =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun x : ℝ => x^3) 0 0
    rw [mfderiv_eq_fderiv, hz]
    rfl
  exact (one_ne_zero : (1 : ℝ) ≠ 0) (l.injective heq)
