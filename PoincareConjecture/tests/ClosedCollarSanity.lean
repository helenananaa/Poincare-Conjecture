import PoincareConjecture

set_option autoImplicit false

open Set PoincareConjecture.Topology.FiberSaturation
namespace ClosedCollarSanity

private def collar : Sphere2 × Icc (-2 : ℝ) 2 → Sphere2 × ℝ :=
  Prod.map id Subtype.val

private theorem collar_embedding : Topology.IsEmbedding collar :=
  Topology.IsEmbedding.id.prodMap Topology.IsEmbedding.subtypeVal

private def band : Set (Sphere2 × ℝ) := univ ×ˢ Ioo (-1) 1

private theorem band_open : IsOpen band := isOpen_univ.prod isOpen_Ioo

private theorem band_displayed :
    ∃ T : Set (Icc (-2 : ℝ) 2), collar ⁻¹' frontier band = univ ×ˢ T := by
  refine ⟨(Subtype.val : Icc (-2 : ℝ) 2 → ℝ) ⁻¹' {(-1 : ℝ), 1}, ?_⟩
  simp only [band, frontier_univ_prod_eq, frontier_Ioo (by norm_num : (-1 : ℝ) < 1)]
  ext q
  simp [collar]

/-- A genuine embedded sphere collar and a nonempty proper ambient band
instantiate the full component statement, not merely its conclusion. -/
theorem concrete_component_case (x : Sphere2) :
    ∃ A : Set ℝ, IsOpen A ∧ OrdConnected A ∧ A.Nonempty ∧ A ⊆ Ioo (-2) 2 ∧
      connectedComponentIn (band ∩ range (collarInteriorMap collar)) (x, 0) =
        collarInteriorMap collar ''
          (univ ×ˢ ((Subtype.val : Ioo (-2 : ℝ) 2 → ℝ) ⁻¹' A)) := by
  have hp : collarInteriorMap collar (x, ⟨0, by norm_num⟩) ∈ band := by
    simp [collarInteriorMap, collar, band]
  exact (sphere_closed_collar_saturation collar_embedding band_open band_displayed hp).1

-- The actual ambient frontier consists of the two displayed interior fibers.
example (x : Sphere2) : (x, (-1 : ℝ)) ∈ frontier band := by
  simp [band, frontier_Ioo (by norm_num : (-1 : ℝ) < 1)]

-- Both closed-collar endpoints lie outside the closure in this example.
example (x : Sphere2) : (x, (-2 : ℝ)) ∉ closure band := by
  simp [band, closure_prod_eq, closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]

example (x : Sphere2) : (x, (2 : ℝ)) ∉ closure band := by
  simp [band, closure_prod_eq, closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]

end ClosedCollarSanity
