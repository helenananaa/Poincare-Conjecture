import Mathlib
import LeeSmoothLib.Ch05.Sec05_28.Definition_5_28_extra_1
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_3

open scoped Manifold ContDiff

namespace LeeLevelSetEmptyFiber

abbrev PointModel := EuclideanSpace ℝ (Fin 0)

def avoidsZero (_ : PointModel) : ℝ := 1

theorem avoidsZero_contMDiff : ContMDiff (𝓡 0) 𝓘(ℝ, ℝ) ∞ avoidsZero :=
  contMDiff_const

theorem avoidsZero_fiber_empty : avoidsZero ⁻¹' ({0} : Set ℝ) = ∅ := by
  ext x
  simp [avoidsZero]

theorem avoidsZero_zero_regular : Manifold.IsRegularValue (𝓡 0) 𝓘(ℝ, ℝ) avoidsZero 0 := by
  intro x hx
  norm_num [avoidsZero] at hx

/-- Regularity on an empty fiber does not imply that target dimension is at most source dimension. -/
theorem regular_value_does_not_force_dimension_bound :
    ∃ f : PointModel → ℝ, ContMDiff (𝓡 0) 𝓘(ℝ, ℝ) ∞ f ∧
      Manifold.IsRegularValue (𝓡 0) 𝓘(ℝ, ℝ) f 0 ∧ f ⁻¹' {0} = ∅ ∧
      Module.finrank ℝ PointModel < Module.finrank ℝ ℝ := by
  exact ⟨avoidsZero, avoidsZero_contMDiff, avoidsZero_zero_regular,
    avoidsZero_fiber_empty, by simp⟩

/-- In a zero-dimensional ambient manifold every natural-number codimension is zero,
including for an empty embedded subtype. -/
theorem empty_embedded_codimension_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (J : ModelWithCorners ℝ E H)
    [ChartedSpace H (∅ : Set PointModel)]
    (h : IsEmbeddedSubmanifold (𝓡 0) J (∅ : Set PointModel)) :
    h.codimension = 0 := by
  simp [IsEmbeddedSubmanifold.codimension]

/-- The exact empty-fiber codimension bundle requested by the uncorrected regular-level
statement cannot exist, although the map is smooth and zero is a regular value. -/
theorem no_codimension_one_bundle_for_avoidsZero :
    ¬ (∃ (cs : ChartedSpace PointModel (avoidsZero ⁻¹' ({0} : Set ℝ)))
      (hs : IsManifold (𝓡 0) ∞ (avoidsZero ⁻¹' ({0} : Set ℝ))),
      let _ := cs
      let _ := hs
      ∃ h : IsEmbeddedSubmanifold (𝓡 0) (𝓡 0) (avoidsZero ⁻¹' ({0} : Set ℝ)),
        h.codimension = 1) := by
  rintro ⟨cs, hs, h, hcodim⟩
  simpa [IsEmbeddedSubmanifold.codimension] using hcodim

/-- A point of a regular fiber supplies the missing dimension bound. No smoothness of the
map is needed beyond the surjectivity already present in regularity. -/
theorem model_finrank_le_of_nonempty_regular_fiber
    {E F H G M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] [TopologicalSpace G]
    (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F G)
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace G N]
    {f : M → N} {c : N} (hc : Manifold.IsRegularValue I J f c)
    (hne : (f ⁻¹' {c}).Nonempty) :
    Module.finrank ℝ F ≤ Module.finrank ℝ E := by
  obtain ⟨x, hx⟩ := hne
  have hsurj := hc x (Set.mem_singleton_iff.mp hx)
  letI : FiniteDimensional ℝ (TangentSpace I x) := by
    change FiniteDimensional ℝ E
    infer_instance
  have hle := LinearMap.finrank_le_finrank_of_surjective hsurj
  simpa only [TangentSpace] using hle

end LeeLevelSetEmptyFiber
