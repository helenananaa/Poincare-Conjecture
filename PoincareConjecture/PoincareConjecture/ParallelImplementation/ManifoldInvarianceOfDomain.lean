import LeeSmoothLib.External.InvarianceOfDomain.Unconditional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ManifoldInvarianceOfDomain
/-- Actual openness of a continuous injection between same-model topological
manifolds, with no smoothness or pre-existing open-image hypothesis. -/
theorem isOpenEmbedding_of_continuous_injective
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace E M] [ChartedSpace E N]
    (f : M → N) (hf : Continuous f) (hinj : Function.Injective f) :
    Topology.IsOpenEmbedding f :=
/- SWARM_PROOF_BEGIN -/
by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hf hinj
  intro s hs
  let U : M → Set M := fun x =>
    (chartAt E x).source ∩ f ⁻¹' (chartAt E (f x)).source ∩ s
  have hlocal : ∀ x, x ∈ s → IsOpen (f '' U x) := by
    intro x hx
    let e := chartAt E x
    let e' := chartAt E (f x)
    have hxU : x ∈ U x := by
      simp only [U, Set.mem_inter_iff, Set.mem_preimage]
      exact ⟨⟨mem_chart_source E x, mem_chart_source E (f x)⟩, hx⟩
    have hU : IsOpen (U x) := by
      apply IsOpen.inter
      · exact IsOpen.inter e.open_source (e'.open_source.preimage hf)
      · exact hs
    have hUs : U x ⊆ e.source := by
      intro z hz
      exact hz.1.1
    let V : Set E := e '' U x
    have hV : IsOpen V := (e.isOpen_image_iff_of_subset_source hUs).2 hU
    have hVt : V ⊆ e.target := by
      rintro z ⟨w, hw, rfl⟩
      exact e.map_source (hUs hw)
    let g : E → E := fun z => e' (f (e.symm z))
    have hcont₁ : ContinuousOn (fun z : E => f (e.symm z)) V := by
      exact hf.comp_continuousOn (e.continuousOn_symm.mono hVt)
    have hcont₂ : ContinuousOn g V := by
      apply e'.continuousOn.comp hcont₁
      intro z hz
      rcases hz with ⟨w, hw, rfl⟩
      have hfw : f w ∈ e'.source := by
        change w ∈ e.source ∩ f ⁻¹' e'.source ∩ s at hw
        exact hw.1.2
      simpa only [e.left_inv (hUs hw)] using hfw
    have hinj' : Set.InjOn g V := by
      intro a ha b hb hab
      have ha' : f (e.symm a) ∈ e'.source := by
        rcases ha with ⟨w, hw, rfl⟩
        have hfw : f w ∈ e'.source := by
          change w ∈ e.source ∩ f ⁻¹' e'.source ∩ s at hw
          exact hw.1.2
        simpa only [e.left_inv (hUs hw)] using hfw
      have hb' : f (e.symm b) ∈ e'.source := by
        rcases hb with ⟨w, hw, rfl⟩
        have hfw : f w ∈ e'.source := by
          change w ∈ e.source ∩ f ⁻¹' e'.source ∩ s at hw
          exact hw.1.2
        simpa only [e.left_inv (hUs hw)] using hfw
      have hfa : f (e.symm a) = f (e.symm b) := e'.injOn ha' hb' hab
      have hab' : e.symm a = e.symm b := hinj hfa
      have haV : a ∈ e.target := hVt ha
      have hbV : b ∈ e.target := hVt hb
      calc
        a = e (e.symm a) := (e.right_inv haV).symm
        _ = e (e.symm b) := congrArg e hab'
        _ = b := e.right_inv hbV
    have hcoord : IsOpen (g '' V) :=
      LeeSmooth.External.InvarianceOfDomain.Unconditional.invariance_of_domain_open_map
        g V hV hcont₂ hinj'
    have himage : e' '' (f '' U x) = g '' V := by
      ext z
      constructor
      · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
        refine ⟨e w, ⟨w, hw, rfl⟩, ?_⟩
        simp only [g]
        rw [e.left_inv (hUs hw)]
      · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
        refine ⟨f w, ⟨w, hw, rfl⟩, ?_⟩
        simp only [g]
        rw [e.left_inv (hUs hw)]
    have htarget : f '' U x ⊆ e'.source := by
      rintro y ⟨w, hw, rfl⟩
      change w ∈ e.source ∩ f ⁻¹' e'.source ∩ s at hw
      exact hw.1.2
    exact (e'.isOpen_image_iff_of_subset_source htarget).1 (by simpa [himage] using hcoord)
  have himage_union : f '' s = ⋃ x : s, f '' U x.1 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
      exact ⟨x, ⟨⟨mem_chart_source E x, mem_chart_source E (f x)⟩, hx⟩, rfl⟩
    · rw [Set.mem_iUnion]
      intro h
      rcases h with ⟨x, hy⟩
      rcases hy with ⟨w, hw, rfl⟩
      exact ⟨w, hw.2, rfl⟩
  rw [himage_union]
  exact isOpen_iUnion (fun x : s => hlocal x.1 x.2)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ManifoldInvarianceOfDomain
