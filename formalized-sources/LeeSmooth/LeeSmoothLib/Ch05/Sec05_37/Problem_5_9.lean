import Mathlib
import LeeSmoothLib.Ch03.Sec03_20.Problem_3_5
import LeeSmoothLib.Ch03.Sec03_17.Proposition_3_24
import LeeSmoothLib.Ch03.Sec03_18.Definition_3_18_extra_3
import LeeSmoothLib.Ch04.Sec04_21.ImmersionDerivative
-- Declarations for this item will be appended below by the statement pipeline.

open Manifold
open scoped ContDiff Manifold Topology

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

-- `lean_leansearch` was unavailable in this environment, so this item follows the local immersed
-- curve API pattern already used in `Problem_5_10` and `Problem_5_11`.

/-- The velocity of a smooth curve in an immersed plane subset is the differential of the
subtype inclusion applied to its intrinsic tangent vector. -/
private lemma problem_5_9_ambient_velocity_eq_mfderiv
    {S : Set Plane} [TopologicalSpace S] [ChartedSpace ℝ S]
    [IsManifold 𝓘(ℝ) ∞ S]
    (hImm : IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) ∞ (Subtype.val : S → Plane))
    {p : S} (γ : SmoothCurveAt 𝓘(ℝ) p) :
    γ.source ▸ curve_velocityWithin 𝓘(ℝ, Plane)
        (((↑) : S → Plane) ∘ γ) γ.sourceSet 0 =
      mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : S → Plane) p γ.tangentVector := by
  rcases γ with ⟨r, f, hs, hsm⟩
  let γ0 : SmoothCurveAt 𝓘(ℝ) p := ⟨r, f, hs, hsm⟩
  have hsub :
      MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : S → Plane) (f 0) := by
    simpa [hs] using hImm.contMDiff.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hγ : MDifferentiableWithinAt 𝓘(ℝ) 𝓘(ℝ) f γ0.sourceSet 0 :=
    (γ0.smooth.mdifferentiableOn (by simp)) 0 γ0.zero_mem_sourceSet
  have hcomp :
      curve_velocityWithin 𝓘(ℝ, Plane) (((↑) : S → Plane) ∘ f) γ0.sourceSet 0 =
        mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : S → Plane) (f 0)
          (curve_velocityWithin 𝓘(ℝ) f γ0.sourceSet 0) :=
    composite_curve_velocity
      (I := 𝓘(ℝ)) (I' := 𝓘(ℝ, Plane)) (J := γ0.sourceSet) (t₀ := 0)
      (F := (Subtype.val : S → Plane)) (γ := f)
      γ0.uniqueMDiffWithinAt_sourceSet hsub hγ
  cases hs
  simpa [γ0, SmoothCurveAt.tangentVector, Function.comp] using hcomp

/-- A one-dimensional boundaryless manifold has a nonzero tangent vector at every point. -/
private lemma problem_5_9_exists_nonzero_tangent
    {S : Type*} [TopologicalSpace S] [ChartedSpace ℝ S]
    [IsManifold 𝓘(ℝ) ∞ S] (p : S) :
    ∃ w : TangentSpace 𝓘(ℝ) p, w ≠ 0 := by
  let x : ℝ := extChartAt 𝓘(ℝ) p p
  let u : TangentSpace 𝓘(ℝ) x := (NormedSpace.fromTangentSpace x).symm 1
  obtain ⟨w, hw⟩ :=
    (isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ)) (x := p) (y := p)
      (mem_extChartAt_source p)).surjective u
  refine ⟨w, ?_⟩
  intro hw0
  have hu_zero : u = 0 := by
    calc
      u = (mfderiv 𝓘(ℝ) 𝓘(ℝ) (extChartAt 𝓘(ℝ) p) p) 0 := by
        simpa [hw0] using hw.symm
      _ = 0 := by
        simpa using (mfderiv 𝓘(ℝ) 𝓘(ℝ) (extChartAt 𝓘(ℝ) p) p).map_zero
  have hone_zero : (1 : ℝ) = 0 := by
    simpa [u] using congrArg (NormedSpace.fromTangentSpace x) hu_zero
  exact one_ne_zero hone_zero

/-- Problem 5-9: the boundary of the square of side length `2` centered at the origin in `ℝ²`
does not admit any topology and smooth structure for which the inclusion into `ℝ²` is a smooth
immersion. -/
theorem squareBoundary_not_admits_immersed_curve_structure :
    ¬ ∃ t : TopologicalSpace squareBoundary,
        let _ : TopologicalSpace squareBoundary := t
        ∃ _ : ChartedSpace ℝ squareBoundary,
          ∃ _ : IsManifold 𝓘(ℝ) ∞ squareBoundary,
            IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) ∞
              (Subtype.val : squareBoundary → Plane) := by
  rintro ⟨t, h⟩
  letI : TopologicalSpace squareBoundary := t
  rcases h with ⟨cs, hs, hImm⟩
  letI : ChartedSpace ℝ squareBoundary := cs
  letI : IsManifold 𝓘(ℝ) ∞ squareBoundary := hs
  let p : squareBoundary := ⟨squareCorner, squareCorner_mem_squareBoundary⟩
  obtain ⟨w, hw⟩ := problem_5_9_exists_nonzero_tangent p
  obtain ⟨γ, hγ⟩ := exists_smoothCurveAt_tangentVector_eq (I := 𝓘(ℝ)) p w
  let v : TangentSpace 𝓘(ℝ, Plane) (p : Plane) :=
    mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : squareBoundary → Plane) p w
  have hv_ne : v ≠ 0 := by
    intro hv
    apply hw
    apply hImm.mfderiv_injective p
    simpa [v] using hv
  have hvelocity :
      γ.source ▸ curve_velocityWithin 𝓘(ℝ, Plane)
          (((↑) : squareBoundary → Plane) ∘ γ) γ.sourceSet 0 = v := by
    calc
      γ.source ▸ curve_velocityWithin 𝓘(ℝ, Plane)
          (((↑) : squareBoundary → Plane) ∘ γ) γ.sourceSet 0 =
          mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane)
            (Subtype.val : squareBoundary → Plane) p γ.tangentVector :=
        problem_5_9_ambient_velocity_eq_mfderiv hImm γ
      _ = v := by rw [hγ]
  rcases γ with ⟨r, f, hsource, hsm⟩
  let γ0 : SmoothCurveAt 𝓘(ℝ) p := ⟨r, f, hsource, hsm⟩
  let g : ℝ → Plane := fun x ↦ (f x : Plane)
  have hzero : (0 : ℝ) ∈ Set.Ioo (-(r : ℝ)) (r : ℝ) := by
    exact ⟨neg_lt_zero.mpr r.2, r.2⟩
  have hsNhds : Set.Ioo (-(r : ℝ)) (r : ℝ) ∈ 𝓝 (0 : ℝ) :=
    isOpen_Ioo.mem_nhds hzero
  have hgSmooth :
      ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, Plane) ∞ g (Set.Ioo (-(r : ℝ)) (r : ℝ)) := by
    change ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, Plane) ∞
      ((Subtype.val : squareBoundary → Plane) ∘ f) (Set.Ioo (-(r : ℝ)) (r : ℝ))
    exact hImm.contMDiff.comp_contMDiffOn hsm
  have hgDiff0 : DifferentiableAt ℝ g 0 := by
    have hgContDiffOn :
        ContDiffOn ℝ ∞ g (Set.Ioo (-(r : ℝ)) (r : ℝ)) := by
      rw [← contMDiffOn_iff_contDiffOn]
      exact hgSmooth
    exact (hgContDiffOn.contDiffAt hsNhds).differentiableAt (by simp)
  have hg0 : g 0 = squareCorner := by
    simpa [g, p] using congrArg Subtype.val hsource
  have hgSq : ∀ᶠ x in 𝓝 (0 : ℝ), g x ∈ squareBoundary :=
    Filter.Eventually.of_forall fun x ↦ (f x).property
  have hgDeriv : HasDerivAt g (deriv g 0) 0 := hgDiff0.hasDerivAt
  have hderiv_zero : deriv g 0 = 0 :=
    squareBoundary_curve_deriv_eq_zero_at_corner hgDeriv hg0 hgSq
  have hzero_velocity :
      curve_velocityWithin 𝓘(ℝ, Plane) g (Set.Ioo (-(r : ℝ)) (r : ℝ)) 0 = 0 := by
    have hgMDiff0 : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, Plane) g 0 :=
      hgDiff0.mdifferentiableAt
    rw [curve_velocityWithin_eq_curve_velocity
      (isOpen_Ioo.uniqueMDiffWithinAt hzero) hgMDiff0]
    apply (NormedSpace.fromTangentSpace (g 0)).injective
    have hpair : HasDerivAt g 0 0 := by
      simpa [hderiv_zero] using hgDiff0.hasDerivAt
    have happly : fderiv ℝ g 0 1 = 0 := by
      simpa using DFunLike.congr_fun hpair.hasFDerivAt.fderiv 1
    simpa [curve_velocity, mfderiv_eq_fderiv] using! happly
  have hv_zero : v = 0 := by
    have hv_velocity :
        hsource ▸ curve_velocityWithin 𝓘(ℝ, Plane) g
          (Set.Ioo (-(r : ℝ)) (r : ℝ)) 0 = v := by
      simpa [γ0, g, Function.comp, SmoothCurveAt.sourceSet] using! hvelocity
    rw [hzero_velocity] at hv_velocity
    simpa using hv_velocity.symm
  exact hv_ne hv_zero
