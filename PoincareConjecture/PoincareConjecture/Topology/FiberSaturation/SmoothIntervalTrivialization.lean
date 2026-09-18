import PoincareConjecture.Topology.FiberSaturation.SmoothTrivializationSplice
import Mathlib.Topology.FiberBundle.Basic

/-!
The interval exhaustion argument adapts Mathlib's
`FiberBundle.exists_trivialization_Icc_subset` (Apache-2.0), replacing its
pointwise topological splice by the proved collar-matching smooth splice.
-/
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothBundle
open Set Bundle Manifold Filter
open scoped Manifold ContDiff Topology
variable {V W H G M F : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace F] [ChartedSpace G F]
  {I : ModelWithCorners ℝ V H} {J : ModelWithCorners ℝ W G}
  {p : M → ℝ}

/-- Local smooth bundle charts produce a smooth trivialization over every
closed real interval. No global trivialization or smoothness of a previously
chosen topological interval chart is assumed. -/
theorem exists_smooth_trivialization_Icc (hp : Continuous p)
    (hloc : ∀ x : ℝ, ∃ e : Trivialization F p,
      x ∈ e.baseSet ∧ IsSmoothTrivialization I J e) (a b : ℝ) :
    ∃ e : Trivialization F p, IsSmoothTrivialization I J e ∧ Icc a b ⊆ e.baseSet := by
  obtain ⟨ea,hea,hsa⟩ := hloc a
  rcases lt_or_ge b a with hba | hab
  · exact ⟨ea,hsa,by simp [hba]⟩
  let s : Set ℝ := {x ∈ Icc a b | ∃ e : Trivialization F p,
    IsSmoothTrivialization I J e ∧ Icc a x ⊆ e.baseSet}
  have ha : a ∈ s := ⟨left_mem_Icc.mpr hab,ea,hsa,by simp [hea]⟩
  have hsb : b ∈ upperBounds s := fun _ hx => hx.1.2
  let c := sSup s
  have hsc : IsLUB s c := isLUB_csSup ⟨a,ha⟩ ⟨b,hsb⟩
  have hc : c ∈ Icc a b := ⟨hsc.1 ha,hsc.2 hsb⟩
  obtain ⟨_,ec,hsec,hec⟩ : c ∈ s := by
    rcases hc.1.eq_or_lt with heq | hlt
    · rwa [← heq]
    refine ⟨hc,?_⟩
    obtain ⟨e,hce,hse⟩ := hloc c
    obtain ⟨c',hc',hce'⟩ : ∃ c' ∈ Ico a c, Ioc c' c ⊆ e.baseSet :=
      (mem_nhdsLE_iff_exists_mem_Ico_Ioc_subset hlt).mp
        (mem_nhdsWithin_of_mem_nhds (e.open_baseSet.mem_nhds hce))
    obtain ⟨d,⟨hdab,ead,hsad,had⟩,hd⟩ : ∃ d ∈ s, d ∈ Ioc c' c :=
      hsc.exists_between hc'.2
    obtain ⟨k,hsk,hbase,_⟩ := exists_smooth_splice hsad hse hp
      (had ⟨hdab.1,le_rfl⟩) (hce' hd)
    refine ⟨k,hsk,?_⟩
    rw [hbase]
    apply subset_ite.mpr
    exact ⟨fun x hx => had ⟨hx.1.1,hx.2⟩,
      fun x hx => hce' ⟨hd.1.trans (not_le.mp hx.2),hx.1.2⟩⟩
  rcases hc.2.eq_or_lt with heq | hlt
  · exact ⟨ec,hsec,heq ▸ hec⟩
  obtain ⟨d,hdcb,hd⟩ : ∃ d ∈ Ioc c b, Ico c d ⊆ ec.baseSet :=
    (mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset hlt).mp
      (mem_nhdsWithin_of_mem_nhds (ec.open_baseSet.mem_nhds (hec ⟨hc.1,le_rfl⟩)))
  have had : Ico a d ⊆ ec.baseSet :=
    Ico_subset_Icc_union_Ico.trans (union_subset hec hd)
  obtain ⟨d',hcd',hd'd⟩ := exists_between hdcb.1
  have hnew : d' ∈ s := ⟨⟨hc.1.trans hcd'.le, hd'd.le.trans hdcb.2⟩,
    ec,hsec,(Icc_subset_Ico_right hd'd).trans had⟩
  exact ((hsc.1 hnew).not_gt hcd').elim

/-- A standard FiberBundle with a smooth chosen atlas satisfies the local
input above; the output chart need not be one of the original atlas charts. -/
theorem fiberBundle_exists_smooth_trivialization_Icc
    (E : ℝ → Type*) [∀ x, TopologicalSpace (E x)]
    [TopologicalSpace (TotalSpace F E)] [ChartedSpace H (TotalSpace F E)]
    [FiberBundle F E]
    (hs : ∀ x, IsSmoothTrivialization I J (trivializationAt F E x)) (a b : ℝ) :
    ∃ e : Trivialization F (TotalSpace.proj (F := F) (E := E)),
      IsSmoothTrivialization I J e ∧ Icc a b ⊆ e.baseSet :=
  exists_smooth_trivialization_Icc (FiberBundle.continuous_proj F E)
    (fun x => ⟨trivializationAt F E x,mem_baseSet_trivializationAt F E x,hs x⟩) a b

end PoincareConjecture.Topology.FiberSaturation.SmoothBundle
