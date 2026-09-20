import LeeSmoothLib.Ch02.Sec02_11.Definition_2_11_extra_2
import LeeSmoothLib.Ch02.Sec02_11.Proposition_2_25
import Mathlib.Geometry.Manifold.PartitionOfUnity

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold Topology
open Set Function

universe uE uH uM

variable
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H]
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- Lemma 2.26 (Extension Lemma for Smooth Functions): if `A` is a closed subset of a smooth
manifold `M`, `f : A → EuclideanSpace ℝ (Fin k)` is smooth in the sense of
`Function.IsSmoothOn`, and `U` is an open set containing `A`, then `f` extends to a global smooth
map on `M` whose topological support is contained in `U`. -/
theorem exists_supported_contMDiffMap_extension_of_isClosed
    {A U : Set M} (hA : IsClosed A) (hU : IsOpen U) (hAU : A ⊆ U)
    {k : ℕ} (f : A → EuclideanSpace ℝ (Fin k))
    (hf : f.IsSmoothOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin k))) :
    ∃ F : C^∞⟮I, M; 𝓘(ℝ, EuclideanSpace ℝ (Fin k)), EuclideanSpace ℝ (Fin k)⟯,
      (∀ x : A, F x = f x) ∧ tsupport F ⊆ U := by
  classical
  -- Glue the local ambient extensions promised by `IsSmoothOn` to a globally smooth map
  -- that agrees with `f` on `A`.
  let t : M → Set (EuclideanSpace ℝ (Fin k)) := fun x ↦
    if hx : x ∈ A then {f ⟨x, hx⟩} else univ
  have ht : ∀ x, Convex ℝ (t x) := by
    intro x
    unfold t
    split_ifs
    · exact convex_singleton _
    · exact convex_univ
  have hloc :
      ∀ x : M,
        ∃ V ∈ 𝓝 x, ∃ g : M → EuclideanSpace ℝ (Fin k),
          ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (⊤ : ℕ∞) g V ∧
            ∀ y ∈ V, g y ∈ t y := by
    intro x
    by_cases hx : x ∈ A
    · obtain ⟨V, hV_open, hxV, Fext, hFext, hFeq⟩ := hf ⟨x, hx⟩
      refine ⟨V, hV_open.mem_nhds hxV, Fext, hFext, ?_⟩
      intro y hy
      by_cases hyA : y ∈ A
      · simpa [t, dif_pos hyA] using hFeq ⟨y, hyA⟩ hy
      · simp [t, dif_neg hyA]
    · refine ⟨Aᶜ, hA.isOpen_compl.mem_nhds (by simp [hx]), fun _ ↦ 0, contMDiffOn_const, ?_⟩
      intro y hy
      have hyA : y ∉ A := hy
      simp [t, dif_neg hyA]
  obtain ⟨G, hG⟩ :=
    exists_contMDiffMap_forall_mem_convex_of_local (I := I) (n := (⊤ : ℕ∞)) ht hloc
  -- Cut off away from `A` by a bump that is identically `1` on `A` and supported in `U`.
  obtain ⟨ψ, -, hψA, hψU⟩ := exists_smooth_bump_function_for I hA hU hAU
  refine ⟨⟨fun x ↦ ψ x • G x, ψ.contMDiff.smul G.contMDiff⟩, ?_, ?_⟩
  · intro x
    have hψx : ψ (x : M) = 1 := hψA x.property
    have hGx : G (x : M) = f x := by
      have := hG (x : M)
      simpa [t, dif_pos x.property] using this
    simp [hψx, hGx]
  · exact (tsupport_smul_subset_left (ψ : M → ℝ) (G : M → EuclideanSpace ℝ (Fin k))).trans hψU
