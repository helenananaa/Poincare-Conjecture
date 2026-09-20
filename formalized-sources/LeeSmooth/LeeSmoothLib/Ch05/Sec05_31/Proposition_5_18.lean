import LeeSmoothLib.Ch05.Sec05_31.Definition_5_31_extra_1
-- Declarations for this item will be appended below by the statement pipeline.

open Manifold
open scoped Manifold ContDiff

universe u𝕜 uE uH uM uE' uN uE'' uS

section

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I (⊤ : WithTop ℕ∞) M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace E' N]
variable [IsManifold (modelWithCornersSelf 𝕜 E') (⊤ : WithTop ℕ∞) N]

-- Semantic recall note: `lean_leansearch` was unavailable in this session, so the statement
-- surface was chosen from the local `Manifold.ImmersedSubmanifold` and
-- `IsImmersion.toImmersedSubmanifold` API in §5.31.
/-- Proposition 5.18 (1), at the analytic regularity required by the current
`ImmersedSubmanifold` owner: an injective immersion `F : N → M` determines an immersed
submanifold of `M` whose carrier is exactly `Set.range F`, and `F` identifies `N` diffeomorphically
with that immersed-submanifold image. -/
theorem injective_immersion_range_has_immersed_submanifold_structure {F : N → M}
    (hF : IsImmersion (modelWithCornersSelf 𝕜 E') I (⊤ : WithTop ℕ∞) F)
    (hFinj : Function.Injective F) :
    ∃ T : Manifold.ImmersedSubmanifold.{u𝕜, uE, uH, uE', uM, uN} I M,
      T.carrier = Set.range F ∧
        ∃ Φ : N ≃ₘ⟮modelWithCornersSelf 𝕜 E', modelWithCornersSelf 𝕜 T.ModelSpace⟯ T,
          ∀ x : N, T.inclusion (Φ x) = F x := by
  refine ⟨hF.toImmersedSubmanifold hFinj, rfl, ?_⟩
  exact ⟨Diffeomorph.refl (modelWithCornersSelf 𝕜 E') N ∞, fun _ ↦ rfl⟩

/-- Proposition 5.18 (2), corrected: if two analytic injective immersions induce their source
topologies from the ambient manifold and have the same image, then their sources are smoothly
diffeomorphic through the ambient maps. The inducing hypotheses are essential: equal ranges of
bare injective immersions do not determine the source topologies. -/
theorem injective_immersion_range_immersed_submanifold_structure_unique {F : N → M}
    (hF : IsImmersion (modelWithCornersSelf 𝕜 E') I (⊤ : WithTop ℕ∞) F)
    (hFinj : Function.Injective F)
    (hFInducing : Topology.IsInducing F)
    {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {S : Type uS} [TopologicalSpace S] [ChartedSpace E'' S]
    [IsManifold (modelWithCornersSelf 𝕜 E'') (⊤ : WithTop ℕ∞) S]
    {ι : S → M}
    (hιinj : Function.Injective ι)
    (hι : IsImmersion (modelWithCornersSelf 𝕜 E'') I (⊤ : WithTop ℕ∞) ι)
    (hιInducing : Topology.IsInducing ι)
    (hRange : Set.range ι = Set.range F) :
    ∃ Φ : N ≃ₘ⟮modelWithCornersSelf 𝕜 E', modelWithCornersSelf 𝕜 E''⟯ S,
      ∀ x : N, ι (Φ x) = F x := by
  have hFEmbedding : Topology.IsEmbedding F := ⟨hFInducing, hFinj⟩
  have hιEmbedding : Topology.IsEmbedding ι := ⟨hιInducing, hιinj⟩
  let e : N ≃ₜ S :=
    (hFEmbedding.toHomeomorph.trans (Homeomorph.setCongr hRange.symm)).trans
      hιEmbedding.toHomeomorph.symm
  have he_apply (x : N) : ι (e x) = F x := by
    change ι (hιEmbedding.toHomeomorph.symm
      ((Homeomorph.setCongr hRange.symm) (hFEmbedding.toHomeomorph x))) = F x
    rw [show ι (hιEmbedding.toHomeomorph.symm
        ((Homeomorph.setCongr hRange.symm) (hFEmbedding.toHomeomorph x))) =
          (((Homeomorph.setCongr hRange.symm) (hFEmbedding.toHomeomorph x) :
            Set.range ι) : M) by
      exact congrArg Subtype.val (hιEmbedding.toHomeomorph.apply_symm_apply _)]
    rfl
  have he_symm_apply (s : S) : F (e.symm s) = ι s := by
    exact (he_apply (e.symm s)).symm.trans (congrArg ι (e.apply_symm_apply s))
  let Φ : Diffeomorph (modelWithCornersSelf 𝕜 E')
      (modelWithCornersSelf 𝕜 E'') N S ∞ :=
    { toEquiv := e.toEquiv
      contMDiff_toFun := by
        exact ((ContMDiff.iff_comp_isImmersion hι).2 ⟨e.continuous, by
          rw [show ι ∘ (e : N → S) = F by
            funext x
            exact he_apply x]
          exact hF.contMDiff⟩).of_le (by simp)
      contMDiff_invFun := by
        exact ((ContMDiff.iff_comp_isImmersion hF).2 ⟨e.symm.continuous, by
          rw [show F ∘ (e.symm : S → N) = ι by
            funext s
            exact he_symm_apply s]
          exact hι.contMDiff⟩).of_le (by simp) }
  exact ⟨Φ, he_apply⟩

end
