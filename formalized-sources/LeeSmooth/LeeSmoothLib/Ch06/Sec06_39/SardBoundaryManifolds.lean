import LeeSmoothLib.Ch06.Sec06_39.SardStandardModels

noncomputable section

open MeasureTheory
open Manifold
open scoped ContDiff Manifold Topology

namespace SardBoundaryManifolds

universe uM uN

variable {n k : ℕ} [NeZero n]
variable {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (𝓡∂ n) ∞ M] [T2Space M] [SecondCountableTopology M]
variable {N : Type uN} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin k)) N]
  [IsManifold (𝓡 k) ∞ N] [T2Space N] [SecondCountableTopology N]

omit [T2Space M] [SecondCountableTopology M]
  [IsManifold (𝓡 k) ∞ N] [T2Space N] [SecondCountableTopology N] in
private theorem sardBoundary_coordinateRepresentative_not_surjective
    {F : M → N} (hF : ContMDiff (𝓡∂ n) (𝓡 k) ∞ F)
    {e : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin k))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡 k) ∞ N)
    {p x : M} (hx : x ∈ (extChartAt (𝓡∂ n) p).source)
    (hy : F x ∈ e.source)
    (hcrit : ¬ Function.Surjective
      (mfderiv (𝓡∂ n) (𝓡 k) F x)) :
    ¬ Function.Surjective
      (fderivWithin ℝ
        (e.extend (𝓡 k) ∘ F ∘ (extChartAt (𝓡∂ n) p).symm)
        (Set.range (𝓡∂ n)) ((extChartAt (𝓡∂ n) p) x)) := by
  let I := 𝓡∂ n
  let J := 𝓡 k
  let φ := extChartAt I p
  let ψ := e.extend J
  let z := φ x
  have hzTarget : z ∈ φ.target := φ.map_source hx
  have hφdiff :
      MDifferentiableWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ.symm
        (Set.range I) z :=
    by simpa [φ, z] using mdifferentiableWithinAt_extChartAt_symm hzTarget
  have hFdiff : MDifferentiableAt I J F x :=
    hF.contMDiffAt.mdifferentiableAt (by simp)
  have hψdiff :
      MDifferentiableAt J 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ψ (F x) := by
    exact mdifferentiableAt_extend_of_mem_maximalAtlas he hy
  have hUnique :
      UniqueMDiffWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (Set.range I) z := by
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact I.uniqueDiffOn.uniqueDiffWithinAt (by
      exact ⟨(chartAt (EuclideanHalfSpace n) p) x, rfl⟩)
  have hxleft : φ.symm z = x := φ.left_inv hx
  have hFφdiff :
      MDifferentiableWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) J
        (F ∘ φ.symm) (Set.range I) z := by
    exact hFdiff.comp_mdifferentiableWithinAt_of_eq z hφdiff hxleft
  have hcoordDiff :
      MDifferentiableWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin k))
        (ψ ∘ F ∘ φ.symm) (Set.range I) z := by
    simpa [hxleft] using
      hψdiff.comp_mdifferentiableWithinAt_of_eq z hFφdiff
        (by simp [hxleft])
  have hFφderiv :=
    mfderiv_comp_mfderivWithin_of_eq hFdiff hφdiff hUnique hxleft
  have hcoordderiv :=
    mfderiv_comp_mfderivWithin_of_eq hψdiff hFφdiff hUnique
      (by simp [hxleft])
  have hformula :
      fderivWithin ℝ (ψ ∘ F ∘ φ.symm) (Set.range I) z =
        (mfderiv J 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ψ (F x)) ∘L
          (mfderiv I J F x) ∘L
          (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ.symm
            (Set.range I) z) := by
    rw [← mfderivWithin_eq_fderivWithin]
    calc
      mfderiv[Set.range I] (ψ ∘ F ∘ φ.symm) z =
          mfderiv% ψ (F x) ∘SL mfderiv[Set.range I] (F ∘ φ.symm) z := by
            exact hcoordderiv
      _ = mfderiv% ψ (F x) ∘SL
          (mfderiv% F x ∘SL mfderiv[Set.range I] φ.symm z) := by
            rw [hFφderiv]
      _ = (mfderiv J 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ψ (F x)) ∘L
          (mfderiv I J F x) ∘L
          (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ.symm
            (Set.range I) z) := by
            rfl
  have hψinv :
      (mfderiv J 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ψ (F x)).IsInvertible := by
    exact isInvertible_mfderiv_extend_of_mem_maximalAtlas he hy
  intro hsurj
  have hcomp : Function.Surjective
      ((mfderiv J 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ψ (F x)) ∘L
        (mfderiv I J F x) ∘L
        (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ.symm
          (Set.range I) z)) := by
    rw [← hformula]
    exact hsurj
  apply hcrit
  intro y
  obtain ⟨w, hw⟩ := hcomp
    ((mfderiv J 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ψ (F x)) y)
  refine ⟨(mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ.symm
    (Set.range I) z) w, ?_⟩
  change
    (mfderiv J 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ψ (F x))
        ((mfderiv I J F x)
          ((mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ.symm
            (Set.range I) z) w)) =
      (mfderiv J 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ψ (F x)) y at hw
  exact hψinv.injective hw

theorem criticalValues_has_measure_zero_in_manifold_of_contMDiff_halfSpace
    {F : M → N} (hF : ContMDiff (𝓡∂ n) (𝓡 k) ∞ F) :
    has_measure_zero_in_manifold (𝓡 k)
      {y : N | IsCriticalValue (𝓡∂ n) (𝓡 k) F y} := by
  classical
  intro μ hμ e he
  letI : μ.IsAddHaarMeasure := hμ
  let I := 𝓡∂ n
  let J := 𝓡 k
  let s : Set M :=
    {x : M | IsCriticalPoint I J F x ∧ F x ∈ e.source}
  let V : s → Set s := fun p ↦
    Subtype.val ⁻¹' (extChartAt I p.1).source
  have hV_nhds : ∀ p : s, V p ∈ 𝓝 p := by
    intro p
    exact preimage_coe_mem_nhds_subtype.2 <|
      mem_nhdsWithin_of_mem_nhds (extChartAt_source_mem_nhds (I := I) p.1)
  obtain ⟨t, ht_countable, ht_cover⟩ :=
    LindelofSpace.elim_nhds_subcover V hV_nhds
  let sourceSet : s → Set M := fun p ↦
    (extChartAt I p.1).source ∩ F ⁻¹' e.source
  let U : s → Set (EuclideanHalfSpace n) := fun p ↦
    (chartAt (EuclideanHalfSpace n) p.1) '' sourceSet p
  let rep : s → EuclideanHalfSpace n → EuclideanSpace ℝ (Fin k) := fun p ↦
    e.extend J ∘ F ∘ (chartAt (EuclideanHalfSpace n) p.1).symm
  have hpiece_zero : ∀ p ∈ t,
      μ (rep p '' {z ∈ U p | ¬ Function.Surjective
        (fderivWithin ℝ
          (fun w : EuclideanSpace ℝ (Fin n) ↦
            rep p ((𝓡∂ n).symm w))
          (Set.range (𝓡∂ n)) z.1)}) = 0 := by
    intro p hp
    have hsourceSet_open : IsOpen (sourceSet p) := by
      exact (isOpen_extChartAt_source (I := I) p.1).inter
        (e.open_source.preimage hF.continuous)
    have hsource_subset : sourceSet p ⊆
        (chartAt (EuclideanHalfSpace n) p.1).source := by
      intro x hx
      simpa [sourceSet, extChartAt_source] using hx.1
    have hmapsTo : Set.MapsTo F (sourceSet p) e.source := by
      intro x hx
      exact hx.2
    have hU_open : IsOpen (U p) := by
      exact (chartAt (EuclideanHalfSpace n) p.1).isOpen_image_of_subset_source
        hsourceSet_open hsource_subset
    have hcoord :
        ContDiffOn ℝ ∞
          (e.extend J ∘ F ∘ (extChartAt I p.1).symm)
          ((extChartAt I p.1) '' sourceSet p) := by
      have hJid : ∀ z : EuclideanSpace ℝ (Fin k), J z = z := by
        intro z
        rfl
      simpa [extChartAt, OpenPartialHomeomorph.extend_coe, Function.comp_def,
        hJid] using
        ((contMDiffOn_iff_of_mem_maximalAtlas'
          (show chartAt (EuclideanHalfSpace n) p.1 ∈
            IsManifold.maximalAtlas I ∞ M from
              IsManifold.chart_mem_maximalAtlas p.1)
          he hsource_subset hmapsTo).1 hF.contMDiffOn)
    have himage_eq :
        (𝓡∂ n) '' U p = (extChartAt I p.1) '' sourceSet p := by
      ext z
      constructor
      · rintro ⟨u, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨(chartAt (EuclideanHalfSpace n) p.1) x,
          ⟨x, hx, rfl⟩, rfl⟩
    have hrep_contMDiff :
        ContMDiffOn I J ∞ (rep p) (U p) := by
      rw [contMDiffOn_halfSpace_iff_contDiffOn_image]
      rw [himage_eq]
      apply hcoord.congr
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      simp only [rep, Function.comp_apply]
      have hchart :
          (extChartAt I p.1) x =
            I ((chartAt (EuclideanHalfSpace n) p.1) x) := by
        rfl
      have hI :
          (𝓡∂ n).symm (I ((chartAt (EuclideanHalfSpace n) p.1) x)) =
            (chartAt (EuclideanHalfSpace n) p.1) x := by
        exact I.left_inv _
      rw [hchart, hI, ← hchart,
        (chartAt (EuclideanHalfSpace n) p.1).left_inv (hsource_subset hx),
        (extChartAt I p.1).left_inv hx.1]
    exact SardStandardModels.halfSpace_criticalImage_measureZero
      hU_open hrep_contMDiff μ
  have hsubset :
      (e.extend J ''
        ({y : N | IsCriticalValue I J F y} ∩ e.source)) ⊆
      ⋃ p ∈ t, rep p '' {z ∈ U p | ¬ Function.Surjective
        (fderivWithin ℝ
          (fun w : EuclideanSpace ℝ (Fin n) ↦
            rep p (I.symm w))
          (Set.range I) z.1)} := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    rcases (isCriticalValue_iff_exists_critical_point F y).1 hy.1 with
      ⟨x, rfl, hcrit⟩
    let xs : s := ⟨x, ⟨hcrit, hy.2⟩⟩
    have hxs_cover : xs ∈ ⋃ p ∈ t, V p := by
      rw [ht_cover]
      simp
    rcases Set.mem_iUnion₂.1 hxs_cover with ⟨p, hp, hxp⟩
    have hx_source : x ∈ (extChartAt I p.1).source := by
      simpa [V] using hxp
    have hEqOn :
        Set.EqOn
          (fun w : EuclideanSpace ℝ (Fin n) ↦ rep p (I.symm w))
          (e.extend J ∘ F ∘ (extChartAt I p.1).symm)
          (Set.range I) := by
      intro w hw
      rcases hw with ⟨u, rfl⟩
      simp [rep, Function.comp_def]
    have hderiv_eq :
        fderivWithin ℝ
            (fun w : EuclideanSpace ℝ (Fin n) ↦ rep p (I.symm w))
            (Set.range I) ((extChartAt I p.1) x) =
          fderivWithin ℝ
            (e.extend J ∘ F ∘ (extChartAt I p.1).symm)
            (Set.range I) ((extChartAt I p.1) x) := by
      apply fderivWithin_congr hEqOn
      exact hEqOn ⟨(chartAt (EuclideanHalfSpace n) p.1) x, by rfl⟩
    have hnot :
        ¬ Function.Surjective
          (fderivWithin ℝ
            (fun w : EuclideanSpace ℝ (Fin n) ↦
              rep p (I.symm w))
            (Set.range I) ((extChartAt I p.1) x)) := by
      rw [hderiv_eq]
      exact sardBoundary_coordinateRepresentative_not_surjective
        hF he hx_source hy.2 hcrit
    refine Set.mem_iUnion₂.2 ⟨p, hp, ?_⟩
    refine ⟨(chartAt (EuclideanHalfSpace n) p.1) x, ?_, ?_⟩
    · refine ⟨⟨x, ⟨hx_source, hy.2⟩, rfl⟩, ?_⟩
      have hcoord_point :
          (extChartAt I p.1) x =
            ((chartAt (EuclideanHalfSpace n) p.1) x).1 := by
        rfl
      rw [hcoord_point] at hnot
      exact hnot
    · change (e.extend J)
        (F ((chartAt (EuclideanHalfSpace n) p.1).symm
          ((chartAt (EuclideanHalfSpace n) p.1) x))) =
          (e.extend J) (F x)
      have hx_chart : x ∈ (chartAt (EuclideanHalfSpace n) p.1).source := by
        simpa [extChartAt_source] using hx_source
      rw [(chartAt (EuclideanHalfSpace n) p.1).left_inv hx_chart]
  exact measure_mono_null hsubset <|
    (measure_biUnion_null_iff ht_countable).2 hpiece_zero

end SardBoundaryManifolds
