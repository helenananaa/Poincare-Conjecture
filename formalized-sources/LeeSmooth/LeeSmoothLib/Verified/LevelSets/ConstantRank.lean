import Mathlib
import LeeSmoothLib.Ch04.Sec04_21.Exercise_4_4
import LeeSmoothLib.Ch04.Sec04_23.Theorem_4_12
import LeeSmoothLib.Ch05.Sec05_28.Definition_5_28_extra_1
import LeeSmoothLib.Ch05.Sec05_28.Definition_5_28_extra_2
import LeeSmoothLib.Ch05.Sec05_30.SmoothLocalSlice

open scoped ContDiff Manifold

noncomputable section

namespace LeeVerifiedLevelSets

section ConstantRankLevelSets

open Manifold Set

private def constantRankFiberPermIndex (m r : ℕ) (hr : r ≤ m) : Fin m ≃ Fin m :=
  (finCongr (Nat.sub_add_cancel hr).symm).trans <|
    finAddFlip.trans (finCongr (Nat.add_sub_of_le hr))

private def constantRankFiberPerm (m r : ℕ) (hr : r ≤ m) :
    EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (constantRankFiberPermIndex m r hr).symm

private theorem constantRankFiberPerm_tail {m r : ℕ} (hr : r ≤ m)
    (z : EuclideanSpace ℝ (Fin m)) (i : Fin r) :
    constantRankFiberPerm m r hr z
      (Fin.cast (Nat.sub_add_cancel hr) (Fin.natAdd (m - r) i)) =
        z (Fin.castLE hr i) := by
  have hidx :
      constantRankFiberPermIndex m r hr
          (Fin.cast (Nat.sub_add_cancel hr) (Fin.natAdd (m - r) i)) =
        Fin.castLE hr i := by
    apply Fin.ext
    simp [constantRankFiberPermIndex]
  simpa [constantRankFiberPerm] using congrArg (fun j : Fin m => z j) hidx

private theorem constantRankFiberPerm_mem_groupoid {m r : ℕ} (hr : r ≤ m) :
    (constantRankFiberPerm m r hr).toHomeomorph.toOpenPartialHomeomorph ∈
      contDiffGroupoid (∞ : WithTop ℕ∞) (𝓡 m) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  constructor
  · simpa [modelWithCornersSelf_coe] using
      (constantRankFiberPerm m r hr).contDiff.contDiffOn
  · simpa [modelWithCornersSelf_coe] using
      (constantRankFiberPerm m r hr).symm.contDiff.contDiffOn

private theorem constantRankNormalForm_apply_of_lt
    {m n r : ℕ} (i : Fin n) (hri : (i : ℕ) < r) (hmi : (i : ℕ) < m)
    (x : EuclideanSpace ℝ (Fin m)) :
    rank_normal_form m n r x i = x ⟨i, hmi⟩ := by
  simp [rank_normal_form, hri, hmi]

/-- A genuine smooth rank-normal-form chart cuts its fiber out as a smooth Euclidean slice. -/
theorem smooth_rankNormalForm_fiber_isSliceChart
    {m n r : ℕ} {M N : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    [IsManifold (𝓡 m) ∞ M]
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ N]
    {F : M → N} {p : M} {c : N}
    (h : LocalCoordinateNormalFormAt F p (rank_normal_form m n r))
    (hpc : F p = c) (hrm : r ≤ m) (hrn : r ≤ n) :
    (h.domChart.trans
      (constantRankFiberPerm m r hrm).toHomeomorph.toOpenPartialHomeomorph).IsSmoothSliceChart
        (F ⁻¹' {c}) (m - r) := by
  let chi := (constantRankFiberPerm m r hrm).toHomeomorph.toOpenPartialHomeomorph
  let e := h.domChart.trans chi
  have hchi : chi ∈ contDiffGroupoid ∞ (𝓡 m) := by
    exact constantRankFiberPerm_mem_groupoid hrm
  refine ⟨?_, ?_⟩
  · rw [IsManifold.mem_maximalAtlas_iff]
    intro e' he'
    have he'max : e' ∈ IsManifold.maximalAtlas (𝓡 m) ∞ M :=
      IsManifold.subset_maximalAtlas he'
    have hleft : h.domChart.symm.trans e' ∈
        contDiffGroupoid ∞ (𝓡 m) :=
      IsManifold.compatible_of_mem_maximalAtlas h.domChart_mem_maximalAtlas he'max
    have hright : e'.symm.trans h.domChart ∈
        contDiffGroupoid ∞ (𝓡 m) :=
      IsManifold.compatible_of_mem_maximalAtlas he'max h.domChart_mem_maximalAtlas
    constructor
    · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc]
      exact (contDiffGroupoid ∞ (𝓡 m)).trans
        ((contDiffGroupoid ∞ (𝓡 m)).symm hchi) hleft
    · have hright' : (e'.symm.trans h.domChart).trans chi ∈
          contDiffGroupoid ∞ (𝓡 m) :=
        (contDiffGroupoid ∞ (𝓡 m)).trans hright hchi
      simpa [e, OpenPartialHomeomorph.trans_assoc] using hright'
  · rw [Set.IsSliceInChart, Set.IsEuclideanSlice]
    refine ⟨Nat.sub_le m r, fun _ : Fin (m - (m - r)) ↦ (0 : ℝ), ?_⟩
    ext z
    constructor
    · rintro ⟨x, ⟨hxF, hxe⟩, rfl⟩
      refine ⟨e.map_source hxe, ?_⟩
      intro i
      have hxd : x ∈ h.domChart.source := by
        simpa [e, chi, OpenPartialHomeomorph.trans_source] using hxe
      have hnormal : rank_normal_form m n r (h.domChart x) = 0 := by
        calc
          rank_normal_form m n r (h.domChart x) = h.codChart (F x) := by
            simpa [Function.comp, h.domChart.left_inv hxd] using
              (h.eqOn (h.domChart.map_source hxd)).symm
          _ = h.codChart c := by simpa using congrArg h.codChart hxF
          _ = h.codChart (F p) := by rw [hpc]
          _ = 0 := h.codChart_centered.2
      let j : Fin r := Fin.cast (Nat.sub_sub_self hrm) i
      have hold : h.domChart x (Fin.castLE hrm j) = 0 := by
        have happ := constantRankNormalForm_apply_of_lt
          (m := m) (n := n) (r := r) (i := Fin.castLE hrn j)
          (by simpa using j.isLt) (by simpa using lt_of_lt_of_le j.isLt hrm)
          (h.domChart x)
        rw [hnormal] at happ
        have hidx :
            (⟨(Fin.castLE hrn j : Fin n).val,
              by simpa using lt_of_lt_of_le j.isLt hrm⟩ : Fin m) =
              Fin.castLE hrm j := by
          apply Fin.ext
          rfl
        rw [← hidx]
        exact happ.symm
      change constantRankFiberPerm m r hrm (h.domChart x)
          (Fin.cast (Nat.sub_add_cancel hrm) (Fin.natAdd (m - r) j)) = 0
      rw [constantRankFiberPerm_tail hrm (h.domChart x) j]
      exact hold
    · intro hz
      let x : M := e.symm z
      have hzTarget : z ∈ e.target := hz.1
      have hxSource : x ∈ e.source := e.symm.map_source hzTarget
      have hxd : x ∈ h.domChart.source := by
        simpa [x, e, chi, OpenPartialHomeomorph.trans_source] using hxSource
      have hex : e x = z := e.right_inv hzTarget
      have hold (j : Fin r) : h.domChart x (Fin.castLE hrm j) = 0 := by
        let i : Fin (m - (m - r)) := Fin.cast (Nat.sub_sub_self hrm).symm j
        have htail := hz.2 i
        rw [← hex] at htail
        change constantRankFiberPerm m r hrm (h.domChart x)
            (Fin.cast (Nat.sub_add_cancel hrm) (Fin.natAdd (m - r) j)) = 0 at htail
        rw [constantRankFiberPerm_tail hrm (h.domChart x) j] at htail
        exact htail
      have hnormal : rank_normal_form m n r (h.domChart x) = 0 := by
        ext q
        by_cases hqr : (q : ℕ) < r
        · have hqm : (q : ℕ) < m := lt_of_lt_of_le hqr hrm
          have happ := constantRankNormalForm_apply_of_lt
            (m := m) (n := n) (r := r) (i := q) hqr hqm (h.domChart x)
          rw [happ]
          let j : Fin r := ⟨q, hqr⟩
          have hj := hold j
          have hidx : (⟨(q : ℕ), hqm⟩ : Fin m) = Fin.castLE hrm j := by
            apply Fin.ext
            rfl
          rw [hidx]
          exact hj
        · simp [rank_normal_form, hqr]
      have hxF : F x = c := by
        have hFsource : F x ∈ h.codChart.source := h.mapsTo hxd
        have hcsource : c ∈ h.codChart.source := by
          rw [← hpc]
          exact h.codChart_centered.1
        apply h.codChart.injOn hFsource hcsource
        calc
          h.codChart (F x) = rank_normal_form m n r (h.domChart x) := by
            simpa [Function.comp, h.domChart.left_inv hxd] using
              h.eqOn (h.domChart.map_source hxd)
          _ = 0 := hnormal
          _ = h.codChart (F p) := h.codChart_centered.2.symm
          _ = h.codChart c := by rw [hpc]
      exact ⟨x, ⟨hxF, hxSource⟩, hex⟩

/-- A public existential wrapper around `smooth_rankNormalForm_fiber_isSliceChart`.  It hides the
coordinate permutation used internally while retaining exactly the local chart data needed by the
smooth local-slice atlas constructor. -/
theorem smooth_rankNormalForm_fiber_hasSliceChart
    {m n r : ℕ} {M N : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    [IsManifold (𝓡 m) ∞ M]
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ N]
    {F : M → N} {p : M} {c : N}
    (h : LocalCoordinateNormalFormAt F p (rank_normal_form m n r))
    (hpc : F p = c) (hrm : r ≤ m) (hrn : r ≤ n) :
    ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin m)),
      p ∈ e.source ∧ e.IsSmoothSliceChart (F ⁻¹' {c}) (m - r) := by
  let e := h.domChart.trans
    (constantRankFiberPerm m r hrm).toHomeomorph.toOpenPartialHomeomorph
  refine ⟨e, ?_, ?_⟩
  · simpa [e, OpenPartialHomeomorph.trans_source] using h.domChart_centered.1
  · exact smooth_rankNormalForm_fiber_isSliceChart h hpc hrm hrn

/-- Theorem 5.12 (1), with an honest `C∞` bundled output.

The old project owner `IsEmbeddedSubmanifold` is intentionally not returned because it stores an
outer-top (`ω`, analytic) inclusion.  Smoothness cannot supply that field: the graph of
`x ↦ if x ≤ 0 then 0 else exp (-1 / x)` is the standard smooth nonanalytic counterexample.
The explicit rank bounds make the dimension convention safe even when the source or fiber is
empty.  The only normal-form input is the genuine rank theorem derived from `hFsmooth` and
`hFrank`; there is no additional normal-form hypothesis. -/
theorem constant_rank_level_set_has_embedded_submanifold_structure
    {m n r : ℕ} {M N : Type*}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    [IsManifold (𝓡 m) ∞ M]
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ N]
    {F : M → N}
    (hFsmooth : ContMDiff (𝓡 m) (𝓡 n) ∞ F)
    (hFrank : HasConstantRank (𝓡 m) (𝓡 n) F r)
    (c : N) (hrm : r ≤ m) (hrn : r ≤ n) :
    let k : ℕ := m - r
    let S : Set M := F ⁻¹' {c}
    let K := 𝓡 k
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin k)) S,
        ∃ hs : IsManifold K ∞ S,
        let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) S := cs
        let _ : IsManifold K ∞ S := hs
        IsSmoothEmbedding K (𝓡 m) ∞ (Subtype.val : S → M) := by
  dsimp
  let S : Set M := F ⁻¹' {c}
  let _ : TopologicalManifold m M := topologicalManifoldOfChartedSpace m M
  have hSlice : Set.SatisfiesLocalSmoothSliceCondition m S (m - r) := by
    refine ⟨?_⟩
    intro p hp
    have hpc : F p = c := Set.mem_singleton_iff.mp hp
    rcases constant_rank_local_coordinate_normal_form hFsmooth hFrank p with ⟨h, _⟩
    exact smooth_rankNormalForm_fiber_hasSliceChart h hpc hrm hrn
  exact LevelSetSmoothSlice.local_smooth_slice_condition_has_smooth_embedded_structure S hSlice

section ProperEmbedding

universe uK uE uE' uH uH' uM uN

variable {𝕜 : Type uK} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ∞ M]
variable {J : ModelWithCorners 𝕜 E' H'} [IsManifold J ∞ N]

/-- Theorem 5.12 (2): a constant-rank level set is closed, hence properly embedded as a subset. -/
theorem constant_rank_level_set_isProperlyEmbedded [T1Space N] {r : ℕ} {F : M → N}
    (hFsmooth : ContMDiff I J ∞ F) (hFrank : HasConstantRank I J F r) (c : N) :
    (F ⁻¹' {c}).IsProperlyEmbedded := by
  exact (isClosed_singleton.preimage hFsmooth.continuous).isProperlyEmbedded

end ProperEmbedding

end ConstantRankLevelSets

end LeeVerifiedLevelSets
