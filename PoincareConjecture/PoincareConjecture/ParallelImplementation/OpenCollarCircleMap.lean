import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.OpenCollarCircleMap
open Set
/-- An actual continuous circle-valued map supported in the smaller collar.
Crossing from normal coordinate -1 to 1 traverses the circle once. -/
theorem exists_collar_circle_map
    {Y M : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [TopologicalSpace M] [T2Space M]
    (f : Y × Set.Ioo (-2 : ℝ) 2 → M) (hf : Topology.IsOpenEmbedding f) :
    let O : Set M := f '' {q : Y × Set.Ioo (-2 : ℝ) 2 | |(q.2 : ℝ)| < 1}
    ∃ c : M → AddCircle (1 : ℝ), Continuous c ∧
      (∀ x : M, x ∉ O → c x = 0) ∧
      (∀ (y : Y) (t : Set.Ioo (-2 : ℝ) 2), |(t : ℝ)| ≤ 1 →
        c (f (y,t)) = (((((t : ℝ) + 1) / 2) : ℝ) : AddCircle (1 : ℝ))) :=
/- SWARM_PROOF_BEGIN -/
by
  dsimp only
  classical
  let O : Set M := f '' {q : Y × Set.Ioo (-2 : ℝ) 2 | |(q.2 : ℝ)| < 1}
  let J : Set ℝ := Set.Icc (-1 : ℝ) 1
  let j : J → Set.Ioo (-2 : ℝ) 2 := fun t =>
    ⟨(t : ℝ), by
      constructor
      · have ht := t.property.1
        linarith
      · have ht := t.property.2
        linarith⟩
  have hj : Continuous j := by
    fun_prop
  let g : Y × J → M := fun p => f (p.1, j p.2)
  have hg : Continuous g := by
    exact hf.continuous.comp (Continuous.prodMk continuous_fst (hj.comp continuous_snd))
  have hj_inj : Function.Injective j := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun t : Set.Ioo (-2 : ℝ) 2 => (t : ℝ)) h
  have hg_inj : Function.Injective g := by
    intro a b h
    have hp : (a.1, j a.2) = (b.1, j b.2) := hf.injective h
    rcases Prod.mk.inj hp with ⟨hy, ht⟩
    exact Prod.ext hy (hj_inj ht)
  let e0 : (Y × J) ≃ Set.range g :=
    Equiv.ofBijective (fun p => (⟨g p, ⟨p, rfl⟩⟩ : Set.range g))
      ⟨(fun a b h => hg_inj (congrArg Subtype.val h)), fun z => by
        rcases z with ⟨x, ⟨p, rfl⟩⟩
        exact ⟨p, rfl⟩⟩
  let hrange : Continuous fun p : Y × J => (⟨g p, ⟨p, rfl⟩⟩ : Set.range g) :=
    Continuous.subtype_mk hg (fun _ => Set.mem_range_self _)
  let e : (Y × J) ≃ₜ Set.range g :=
    Continuous.homeoOfEquivCompactToT2 (f := e0) hrange
  let C : Set M := Set.range g
  have hCcompact : IsCompact C := by
    simpa [C, Set.range] using (isCompact_univ.image hg)
  have hCclosed : IsClosed C := hCcompact.isClosed
  have hUopen : IsOpen {q : Y × Set.Ioo (-2 : ℝ) 2 | |(q.2 : ℝ)| < 1} := by
    have hnorm : Continuous fun q : Y × Set.Ioo (-2 : ℝ) 2 => |(q.2 : ℝ)| := by
      fun_prop
    exact isOpen_lt hnorm continuous_const
  have hOopen : IsOpen O := by
    exact hf.isOpenMap _ hUopen
  let E : Set M := Oᶜ
  have hEclosed : IsClosed E := by
    exact hOopen.isClosed_compl
  have hcoverCore : O ⊆ C := by
    intro x hx
    rcases hx with ⟨q, hq, rfl⟩
    have hq' : |(q.2 : ℝ)| < 1 := hq
    let t : J := ⟨(q.2 : ℝ), by
      constructor
      · have habs := abs_lt.mp hq'
        linarith
      · have habs := abs_lt.mp hq'
        linarith⟩
    have hjt : j t = q.2 := by
      apply Subtype.ext
      rfl
    exact ⟨(q.1, t), by simp [g, hjt]⟩
  have hcover : C ∪ E = Set.univ := by
    ext x
    simp only [mem_union, mem_univ, iff_true, E]
    by_cases hx : x ∈ O
    · exact Or.inl (hcoverCore hx)
    · exact Or.inr hx
  let phase : ℝ → AddCircle (1 : ℝ) := fun u => (u : AddCircle (1 : ℝ))
  let ψ : Set.range g → AddCircle (1 : ℝ) := fun z =>
    phase ((((e.symm z).2 : ℝ) + 1) / 2)
  have hψ : Continuous ψ := by
    dsimp [ψ, phase]
    fun_prop
  let c : M → AddCircle (1 : ℝ) := fun x =>
    if hx : x ∈ C then ψ ⟨x, hx⟩ else 0
  have hboundary : ∀ x ∈ E, ∀ hx : x ∈ C, ψ ⟨x, hx⟩ = 0 := by
    intro x hxE hxC
    rcases hxC with ⟨p, hp⟩
    have hp' : e.symm ⟨x, ⟨p, hp⟩⟩ = p := by
      have hz : (⟨x, ⟨p, hp⟩⟩ : Set.range g) = e p := by
        apply Subtype.ext
        exact hp.symm
      rw [hz, e.symm_apply_apply]
    have hnot : ¬ |(p.2 : ℝ)| < 1 := by
      intro hlt
      apply hxE
      rw [Set.mem_image]
      refine ⟨(p.1, j p.2), ?_, ?_⟩
      · simpa using hlt
      · simpa [g] using hp
    have habs : |(p.2 : ℝ)| = 1 := by
      apply le_antisymm
      · exact abs_le.mpr ⟨by linarith [p.2.property.1], by linarith [p.2.property.2]⟩
      · exact le_of_not_gt hnot
    rcases le_total (0 : ℝ) (p.2 : ℝ) with ht0 | ht0
    · have ht : (p.2 : ℝ) = 1 := by
        rw [abs_of_nonneg ht0] at habs
        linarith
      simp [ψ, phase, hp', ht]
    · have ht : (p.2 : ℝ) = -1 := by
        rw [abs_of_nonpos ht0] at habs
        linarith
      simp [ψ, phase, hp', ht]
  have hcC : ContinuousOn c C := by
    rw [continuousOn_iff_continuous_restrict]
    have hrestrict : C.restrict c = ψ := by
      funext z
      simp [c]
    rw [hrestrict]
    exact hψ
  have hcE : ContinuousOn c E := by
    rw [continuousOn_iff_continuous_restrict]
    have hrestrict : E.restrict c = fun _ => (0 : AddCircle (1 : ℝ)) := by
      funext z
      by_cases hx : (z : M) ∈ C
      · simp [c, hx, hboundary z z.property hx]
      · simp [c, hx]
    rw [hrestrict]
    exact continuous_const
  have hc : Continuous c := by
    apply continuousOn_univ.mp
    rw [← hcover]
    exact hcC.union_of_isClosed hcE hCclosed hEclosed
  refine ⟨c, hc, ?_, ?_⟩
  · intro x hx
    have hxE : x ∈ E := hx
    by_cases hxC : x ∈ C
    · simp [c, hxC, hboundary x hxE hxC]
    · simp [c, hxC]
  · intro y t ht
    let p : Y × J := (y, ⟨(t : ℝ), abs_le.mp ht⟩)
    have hpt : j p.2 = t := by
      apply Subtype.ext
      rfl
    have hxC : f (y, t) ∈ C := ⟨p, by simp [p, g, hpt]⟩
    have heq : e.symm ⟨f (y, t), hxC⟩ = p := by
      have hz : (⟨f (y, t), hxC⟩ : Set.range g) = e p := by
        apply Subtype.ext
        change f (y, t) = g p
        simp [p, g, hpt]
      rw [hz, e.symm_apply_apply]
    simp [c, hxC, ψ, phase, heq, p]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.OpenCollarCircleMap
