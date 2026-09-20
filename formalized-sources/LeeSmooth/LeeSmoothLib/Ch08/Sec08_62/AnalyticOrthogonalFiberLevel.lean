import LeeSmoothLib.Ch01.Sec01.Definition_1_extra_1
import LeeSmoothLib.Ch05.Sec05_28.Definition_5_28_extra_1
import LeeSmoothLib.Ch05.Sec05_29.Definition_5_29_extra_1
import LeeSmoothLib.Ch05.Sec05_29.Theorem_5_8
import LeeSmoothLib.Ch08.Sec08_62.AnalyticOrthogonalFiberNormalForm

/-!
Analytic regular-level atlas: IFT charts, Euclidean slices, then Theorem 5.8's analytic
embedded-submanifold packaging.  Used only for the Gram fiber of Example 8.47.
-/

open scoped ContDiff Manifold
open Set

noncomputable section

namespace AnalyticOrthogonalFiberLevel

open AnalyticOrthogonalFiberNormalForm Manifold

/-- Corollary 5.14 at analytic order, for Euclidean source and target.  Regularity of the
value is the honest surjectivity of `mfderiv`; the source polynomial in Example 8.47 is
analytic, so no extra normal-form hypothesis is used. -/
theorem analytic_regular_level_set_has_embedded_submanifold_structure
    {m n : ℕ} {M N : Type*}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    [IsManifold (𝓡 m) (⊤ : WithTop ℕ∞) M]
    [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) N]
    {Φ : M → N} {c : N}
    (hΦ : ContMDiff (𝓡 m) (𝓡 n) (⊤ : WithTop ℕ∞) Φ)
    (hc : ∀ p : M, Φ p = c → Function.Surjective (mfderiv (𝓡 m) (𝓡 n) Φ p))
    (hnm : n ≤ m) :
    let k : ℕ := m - n
    let S : Set M := Φ ⁻¹' {c}
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin k)) S,
      ∃ hs : IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S,
        let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) S := cs
        let _ : IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S := hs
        IsEmbeddedSubmanifold (𝓡 m) (𝓡 k) S := by
  dsimp
  let S : Set M := Φ ⁻¹' {c}
  let _ : TopologicalManifold m M := topologicalManifoldOfChartedSpace m M
  have hSlice : Set.SatisfiesLocalSliceCondition m S (m - n) := by
    refine ⟨?_⟩
    intro p hp
    have hpc : Φ p = c := Set.mem_singleton_iff.mp hp
    rcases AnalyticOrthogonalFiberNormalForm.at_of_surjective_mfderiv hΦ p (hc p hpc)
      with ⟨h, _⟩
    exact analytic_rankNormalForm_fiber_hasSliceChart h hpc hnm
  rcases local_slice_condition_has_embedded_submanifold_structure (S := S) hSlice with
    ⟨tm, hs, hEmb⟩
  letI : TopologicalManifold (m - n) S := tm
  let cs : ChartedSpace (EuclideanSpace ℝ (Fin (m - n))) S := inferInstance
  refine ⟨cs, hs, ?_⟩
  simpa [S] using hEmb

end AnalyticOrthogonalFiberLevel
