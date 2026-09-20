import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Analysis.Normed.Module.FiniteDimension

-- Declarations for this item will be appended below by the statement pipeline.

universe uM uN uE uH uE' uH'

open scoped Manifold ContDiff Topology

section ContinuousPullback

variable {M : Type uM} [TopologicalSpace M]
variable {N : Type uN} [TopologicalSpace N]

/- Problem 2-10 (1): pullback along a continuous map is the canonical `ℝ`-algebra homomorphism on
continuous real-valued functions, namely `ContinuousMap.compRightAlgHom ℝ ℝ`. Its linearity is
derived from this owner rather than exposed through a parallel `IsLinearMap` wrapper. -/
#check (ContinuousMap.compRightAlgHom ℝ ℝ : C(M, N) → C(N, ℝ) →ₐ[ℝ] C(M, ℝ))

end ContinuousPullback

section SmoothPullback

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners ℝ E' H'}
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

-- Proof sketch: If `F` is smooth, compose any bundled smooth function `f : C^∞⟮J, N; ℝ⟯` with
-- `F`. Conversely, apply the hypothesis to enough smooth coordinate functions and use the standard
-- smoothness criterion in charts.  The finite-dimensional Hausdorff assumptions are the standard
-- hypotheses under which Mathlib supplies the required smooth bump functions.
omit [IsManifold I ∞ M] in
/-- Problem 2-10 (2): A map between smooth manifolds is smooth exactly when pullback along it sends
every smooth real-valued function on the target to a smooth real-valued function on the source. -/
theorem smooth_iff_pullback_preserves_smooth_real_functions
    [FiniteDimensional ℝ E'] [T2Space N] {F : M → N} :
    ContMDiff I J ∞ F ↔
      ∀ f : C^∞⟮J, N; ℝ⟯, ContMDiff I 𝓘(ℝ) ∞ (f ∘ F) := by
  constructor
  · intro hF f
    exact f.contMDiff.comp hF
  · intro h x
    classical
    let y : N := F x
    let b : SmoothBumpFunction J y := Classical.choice inferInstance
    let G : N → E' := fun z ↦ b z • extChartAt J y z
    have hG : ContMDiff J 𝓘(ℝ, E') ∞ G := by
      exact b.contMDiff_smul (contMDiffOn_extChartAt (I := J) (x := y))

    let ι := Fin (Module.finrank ℝ E')
    let A : E' ≃L[ℝ] (ι → ℝ) :=
      (Module.finBasis ℝ E').equivFun.toContinuousLinearEquiv
    have hGF : ContMDiff I 𝓘(ℝ, E') ∞ (G ∘ F) := by
      have hAG : ContMDiff J 𝓘(ℝ, ι → ℝ) ∞ (A ∘ G) :=
        A.toContinuousLinearMap.contMDiff.comp hG
      have hAGF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ (A ∘ G ∘ F) := by
        rw [contMDiff_pi_space]
        intro i
        let fi : C^∞⟮J, N; ℝ⟯ :=
          ⟨fun z ↦ A (G z) i, (contDiff_apply ℝ ℝ i).contMDiff.comp hAG⟩
        simpa [fi, Function.comp_def] using h fi
      simpa [Function.comp_def] using
        A.symm.toContinuousLinearMap.contMDiff.comp hAGF

    let fb : C^∞⟮J, N; ℝ⟯ := ⟨b, b.contMDiff⟩
    let bF : M → ℝ := fun z ↦ b (F z)
    have hbF : ContMDiff I 𝓘(ℝ) ∞ bF := by
      simpa [fb, bF, Function.comp_def] using h fb
    have hbFx : bF x ≠ 0 := by
      simp [bF, y, b]
    have hbF_support : Function.support bF ∈ 𝓝 x :=
      hbF.continuous.isOpen_support.mem_nhds hbFx
    have hF_source : ∀ᶠ z in 𝓝 x, F z ∈ (chartAt H' y).source := by
      filter_upwards [hbF_support] with z hz
      apply b.support_subset_source
      simpa [bF, Function.mem_support] using hz

    have hcoord : ContMDiffAt I 𝓘(ℝ, E') ∞ (extChartAt J y ∘ F) x := by
      have hrescaled :
          ContMDiffAt I 𝓘(ℝ, E') ∞
            (fun z ↦ (bF z)⁻¹ • (G ∘ F) z) x :=
        (hbF.contMDiffAt.inv₀ hbFx).smul hGF.contMDiffAt
      refine hrescaled.congr_of_eventuallyEq ?_
      filter_upwards [hbF_support] with z hz
      have hz0 : bF z ≠ 0 := hz
      simp [G, bF, Function.comp_def, hz0]

    have hF_continuous : ContinuousAt F x := by
      have hrec :
          ContinuousAt ((extChartAt J y).symm ∘ (extChartAt J y ∘ F)) x :=
        by
          simpa [y] using
            ContinuousAt.comp (f := extChartAt J (F x) ∘ F)
              (continuousAt_extChartAt_symm (I := J) (F x))
              (show ContinuousAt (extChartAt J (F x) ∘ F) x by
                simpa [y] using hcoord.continuousAt)
      refine hrec.congr_of_eventuallyEq ?_
      filter_upwards [hF_source] with z hz
      have hz' : F z ∈ (extChartAt J y).source := by
        simpa only [extChartAt_source] using hz
      simpa [Function.comp_def] using ((extChartAt J y).left_inv hz').symm
    simpa [y] using
      (contMDiffAt_iff_target.2 ⟨hF_continuous, hcoord⟩)

-- Proof sketch: Apply part (2) to the forward map of the homeomorphism.
omit [IsManifold I ∞ M] in
/-- Problem 2-10 (3): For a homeomorphism `F`, smoothness of the forward map is equivalent to
pullback by `F` preserving smooth real-valued functions. -/
theorem homeomorph_contMDiff_iff_pullback_preserves_smooth_real_functions
    [FiniteDimensional ℝ E'] [T2Space N] (F : M ≃ₜ N) :
    ContMDiff I J ∞ F ↔
      ∀ f : C^∞⟮J, N; ℝ⟯, ContMDiff I 𝓘(ℝ) ∞ (f ∘ F) :=
  smooth_iff_pullback_preserves_smooth_real_functions

-- Proof sketch: Apply part (2) to the inverse homeomorphism `F.symm`.
omit [IsManifold J ∞ N] in
/-- Problem 2-10 (4): For a homeomorphism `F`, smoothness of the inverse map is equivalent to
pullback by `F.symm` preserving smooth real-valued functions. -/
theorem homeomorph_symm_contMDiff_iff_pullback_preserves_smooth_real_functions
    [FiniteDimensional ℝ E] [T2Space M] (F : M ≃ₜ N) :
    ContMDiff J I ∞ F.symm ↔
      ∀ g : C^∞⟮I, M; ℝ⟯, ContMDiff J 𝓘(ℝ) ∞ (g ∘ F.symm) :=
  smooth_iff_pullback_preserves_smooth_real_functions

end SmoothPullback
