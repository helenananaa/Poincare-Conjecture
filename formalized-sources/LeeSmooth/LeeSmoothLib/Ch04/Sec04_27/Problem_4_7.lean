import Mathlib.Geometry.Manifold.Diffeomorph
import LeeSmoothLib.Ch04.Sec04_25.Theorem_4_29
-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool unavailable in this environment; the statements below use the local
-- `Manifold.contMDiff_iff_comp_of_surjective_smooth_submersion` API from Theorem 4.29.

open scoped ContDiff Manifold

namespace Manifold

universe uE uE1 uE2 uE3 uE4 uH uH1 uH2 uH3 uH4 uM uN uN2 uP uQ

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {E1 : Type uE1} [NormedAddCommGroup E1] [NormedSpace ℝ E1] [FiniteDimensional ℝ E1]
variable {E2 : Type uE1} [NormedAddCommGroup E2] [NormedSpace ℝ E2] [FiniteDimensional ℝ E2]
variable {H : Type uH} [TopologicalSpace H]
variable {H1 : Type uH1} [TopologicalSpace H1]
variable {H2 : Type uH1} [TopologicalSpace H2]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H1 N]
variable {N2 : Type uN} [TopologicalSpace N2] [ChartedSpace H2 N2]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
variable {J : ModelWithCorners ℝ E1 H1} [IsManifold J ∞ N]
variable {J2 : ModelWithCorners ℝ E2 H2} [IsManifold J2 ∞ N2]

variable [I.Boundaryless]

section

variable {E3 : Type uE3} [NormedAddCommGroup E3] [NormedSpace ℝ E3]
variable {H3 : Type uH3} [TopologicalSpace H3]
variable {P : Type uP} [TopologicalSpace P] [ChartedSpace H3 P]
variable {K : ModelWithCorners ℝ E3 H3} [IsManifold K ∞ P]

/-- If `N2` has the same characteristic property as `N` for a surjective smooth submersion with
boundaryless source model, then smoothness of maps out of `N2` is detected by precomposing with
the underlying identification `e : N ≃ N2`. -/
theorem contMDiff_iff_comp_equiv_of_submersion_characteristic_property {π : M → N}
    (hpi : IsSmoothSubmersion I J π) (h_surj : Function.Surjective π) (e : N ≃ N2)
    (hchar :
      ∀ ⦃E4 : Type uE3⦄ [NormedAddCommGroup E4] [NormedSpace ℝ E4]
        ⦃H4 : Type uH3⦄ [TopologicalSpace H4]
        ⦃Q : Type uP⦄ [TopologicalSpace Q] [ChartedSpace H4 Q]
        ⦃L : ModelWithCorners ℝ E4 H4⦄ [IsManifold L ∞ Q] {F : N2 → Q},
        ContMDiff J2 L ∞ F ↔ ContMDiff I L ∞ (F ∘ e ∘ π))
    {F : N2 → P} :
    ContMDiff J2 K ∞ F ↔ ContMDiff J K ∞ (F ∘ e) := by
  constructor
  · intro hF
    apply
      (contMDiff_iff_comp_of_surjective_smooth_submersion
        (F := F ∘ e) hpi h_surj).mpr
    simpa [Function.comp_def] using (hchar (F := F)).mp hF
  · intro hFe
    apply (hchar (F := F)).mpr
    simpa [Function.comp_def] using
      (contMDiff_iff_comp_of_surjective_smooth_submersion
        (F := F ∘ e) hpi h_surj).mp hFe

/-- Problem 4-7: if `π : M → N` is a surjective smooth submersion with boundaryless source model
and `N2` is another smooth manifold on the same underlying set, represented here by an equivalence
`e : N ≃ N2`, such that for every smooth manifold `P` a map `F : N2 → P` is smooth if and only if
`F ∘ e ∘ π` is smooth, then the identity-on-points identification is a diffeomorphism. -/
theorem exists_diffeomorph_of_submersion_characteristic_property {π : M → N}
    (hpi : IsSmoothSubmersion I J π) (h_surj : Function.Surjective π) (e : N ≃ N2)
    (hchar :
      ∀ ⦃E3 : Type uE1⦄ [NormedAddCommGroup E3] [NormedSpace ℝ E3]
        ⦃H3 : Type uH1⦄ [TopologicalSpace H3]
        ⦃P : Type uN⦄ [TopologicalSpace P] [ChartedSpace H3 P]
        ⦃K : ModelWithCorners ℝ E3 H3⦄ [IsManifold K ∞ P] {F : N2 → P},
        ContMDiff J2 K ∞ F ↔ ContMDiff I K ∞ (F ∘ e ∘ π)) :
    ∃ Φ : N ≃ₘ⟮J, J2⟯ N2, Φ.toEquiv = e := by
  have he : ContMDiff J J2 ∞ e := by
    apply
      (contMDiff_iff_comp_of_surjective_smooth_submersion
        (F := e) hpi h_surj).mpr
    simpa [Function.comp_def] using
      (hchar (K := J2) (F := id)).mp
        (contMDiff_id : ContMDiff J2 J2 ∞ (id : N2 → N2))
  have he_symm : ContMDiff J2 J ∞ e.symm := by
    apply (hchar (K := J) (F := e.symm)).mpr
    simpa [Function.comp_def] using hpi.contMDiff
  let Φ : N ≃ₘ⟮J, J2⟯ N2 :=
    { toEquiv := e
      contMDiff_toFun := he
      contMDiff_invFun := he_symm }
  exact ⟨Φ, rfl⟩

end

end Manifold
