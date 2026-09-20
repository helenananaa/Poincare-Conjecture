import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Manifold

section Composition

universe u𝕜 uE uF uG uH uH' uH'' uM uN uP

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type uG} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H : Type uH} [TopologicalSpace H]
  {H' : Type uH'} [TopologicalSpace H']
  {H'' : Type uH''} [TopologicalSpace H'']
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
  {P : Type uP} [TopologicalSpace P] [ChartedSpace H'' P]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
  {K : ModelWithCorners 𝕜 G H''}
  {n : WithTop ℕ∞} {f : M → N} {g : N → P}

-- Proof sketch: choose local partial diffeomorphisms for `f` and `g` at each point and compose
-- them to obtain a local partial diffeomorphism for `g ∘ f`.
/-- Proposition 4.6 (1): part (a), the composition of two local diffeomorphisms is a local
diffeomorphism. -/
theorem isLocalDiffeomorph_comp (hg : IsLocalDiffeomorph J K n g)
    (hf : IsLocalDiffeomorph I J n f) : IsLocalDiffeomorph I K n (g ∘ f) :=
  fun x ↦ (hf x).comp (K := K) (P := P) (hg (f x))

end Composition

section FiniteProducts

universe u𝕜 uι uE uF uH uG uM uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {ι : Type uι} [Fintype ι]
  {E : ι → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  {F : ι → Type uF} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
  {H : ι → Type uH} [∀ i, TopologicalSpace (H i)]
  {G : ι → Type uG} [∀ i, TopologicalSpace (G i)]
  {M : ι → Type uM} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (H i) (M i)]
  {N : ι → Type uN} [∀ i, TopologicalSpace (N i)] [∀ i, ChartedSpace (G i) (N i)]
  {I : ∀ i, ModelWithCorners 𝕜 (E i) (H i)}
  {J : ∀ i, ModelWithCorners 𝕜 (F i) (G i)}
  {n : WithTop ℕ∞} {f : ∀ i, M i → N i}

private theorem contMDiffOn_pi_iff {A : Type*} [TopologicalSpace A]
    {L : Type*} [NormedAddCommGroup L] [NormedSpace 𝕜 L]
    {Q : Type*} [TopologicalSpace Q] {K : ModelWithCorners 𝕜 L Q}
    [ChartedSpace Q A] {s : Set A} {g : A → ∀ i, N i} :
    ContMDiffOn K (ModelWithCorners.pi J) n g s ↔
      ∀ i, ContMDiffOn K (J i) n (fun x ↦ g x i) s := by
  constructor
  · intro hg i x hx
    have h := hg x hx
    rw [contMDiffWithinAt_iff_target] at h ⊢
    exact ⟨(continuous_apply i).continuousWithinAt.comp h.1
        (fun _ _ ↦ Set.mem_univ _),
      contMDiffWithinAt_pi_space.mp h.2 i⟩
  · intro hg x hx
    rw [contMDiffWithinAt_iff_target]
    refine ⟨continuousWithinAt_pi.mpr (fun i ↦ (hg i x hx).continuousWithinAt), ?_⟩
    exact contMDiffWithinAt_pi_space.mpr fun i ↦
      (contMDiffWithinAt_iff_target.mp (hg i x hx)).2

private theorem contMDiff_pi_projection (i : ι) :
    ContMDiff (ModelWithCorners.pi I) (I i) n (fun x : ∀ j, M j ↦ x i) := by
  have hId : ContMDiff (ModelWithCorners.pi I) (ModelWithCorners.pi I) n
      (id : (∀ j, M j) → ∀ j, M j) := contMDiff_id
  intro x
  have hx := hId x
  rw [contMDiffAt_iff_target] at hx ⊢
  exact ⟨(continuous_apply i).continuousAt.comp hx.1,
    contMDiffAt_pi_space.mp hx.2 i⟩

-- Proof sketch: prove the statement pointwise using the local product charts on finite products of
-- manifolds and the coordinatewise product of the local inverses.
/-- Proposition 4.6 (2): part (b), a finite product of local diffeomorphisms is a local
diffeomorphism. -/
theorem isLocalDiffeomorph_pi (hf : ∀ i, IsLocalDiffeomorph (I i) (J i) n (f i)) :
    IsLocalDiffeomorph (ModelWithCorners.pi I) (ModelWithCorners.pi J) n
      (fun x : ∀ i, M i ↦ fun i ↦ f i (x i)) := by
  intro x
  choose Φ hx hΦ using fun i ↦ hf i (x i)
  let Ψ : PartialDiffeomorph (ModelWithCorners.pi I) (ModelWithCorners.pi J)
      (∀ i, M i) (∀ i, N i) n :=
    { __ := OpenPartialHomeomorph.pi (fun i ↦ (Φ i).toOpenPartialHomeomorph)
      contMDiffOn_toFun := by
        apply contMDiffOn_pi_iff.mpr
        intro i
        simpa [Function.comp_def] using
          (Φ i).contMDiffOn_toFun.comp
            (contMDiff_pi_projection (I := I) (n := n) i).contMDiffOn
            (by
              intro y hy
              simpa [OpenPartialHomeomorph.pi] using hy i (Set.mem_univ i))
      contMDiffOn_invFun := by
        apply contMDiffOn_pi_iff.mpr
        intro i
        simpa [Function.comp_def] using
          (Φ i).contMDiffOn_invFun.comp
            (contMDiff_pi_projection (I := J) (n := n) i).contMDiffOn
            (by
              intro y hy
              simpa [OpenPartialHomeomorph.pi] using hy i (Set.mem_univ i)) }
  refine ⟨Ψ, ?_, ?_⟩
  · simpa [Ψ, OpenPartialHomeomorph.pi] using fun i ↦ hx i
  · intro y hy
    funext i
    exact hΦ i (by simpa [Ψ, OpenPartialHomeomorph.pi] using hy i (Set.mem_univ i))

end FiniteProducts

/- Proposition 4.6 (3): part (c), every local diffeomorphism is a local homeomorphism. -/
#check IsLocalDiffeomorph.isLocalHomeomorph

/- Proposition 4.6 (4): part (c), every local diffeomorphism is an open map. -/
#check IsLocalDiffeomorph.isOpenMap

/- Proposition 4.6 (5): part (d), the restriction of a local diffeomorphism to an open
submanifold is encoded by the canonical owner-level restriction statement
`IsLocalDiffeomorph.isLocalDiffeomorphOn`. -/
#check IsLocalDiffeomorph.isLocalDiffeomorphOn

/- Proposition 4.6 (6): part (e), every diffeomorphism is a local diffeomorphism. -/
#check Diffeomorph.isLocalDiffeomorph

/- Proposition 4.6 (7): part (f), a bijective local diffeomorphism canonically upgrades to a
diffeomorphism. -/
#check IsLocalDiffeomorph.diffeomorphOfBijective

section Coordinates

universe u𝕜 uE uF uH uG uM uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type uH} [TopologicalSpace H]
  {G : Type uG} [TopologicalSpace G]
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type uN} [TopologicalSpace N] [ChartedSpace G N]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {n : WithTop ℕ∞} {f : M → N}

private def extChartAtPartialDiffeomorph (I : ModelWithCorners 𝕜 E H)
    [I.Boundaryless] [IsManifold I n M] (x : M) :
    PartialDiffeomorph I 𝓘(𝕜, E) M E n where
  toPartialEquiv := extChartAt I x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target x
  contMDiffOn_toFun := by
    simpa [extChartAt_source] using (contMDiffOn_extChartAt (I := I) (n := n) (x := x))
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm x

private def PartialDiffeomorph.restrOpen
    (e : PartialDiffeomorph I J M N n) (s : Set M) (hs : IsOpen s) :
    PartialDiffeomorph I J M N n where
  __ := e.toOpenPartialHomeomorph.restrOpen s hs
  contMDiffOn_toFun := e.contMDiffOn_toFun.mono Set.inter_subset_left
  contMDiffOn_invFun := e.contMDiffOn_invFun.mono Set.inter_subset_left

private theorem IsLocalDiffeomorphAt.congr_of_eventuallyEq {g : M → N} {x : M}
    (hg : IsLocalDiffeomorphAt I J n g x) (hfg : f =ᶠ[nhds x] g) :
    IsLocalDiffeomorphAt I J n f x := by
  rcases mem_nhds_iff.mp hfg with ⟨s, hs, hsOpen, hxs⟩
  rcases hg with ⟨e, hxe, he⟩
  refine ⟨e.restrOpen s hsOpen, ⟨hxe, hxs⟩, ?_⟩
  intro y hy
  exact (hs hy.2).trans (he hy.1)

-- Proof sketch: transport the local diffeomorphism data to the preferred extended charts and use
-- compatibility of local diffeomorphisms with chart changes in both directions.
/-- Proposition 4.6 (3): part (g), a map is a local diffeomorphism exactly when each preferred
coordinate representative is a local diffeomorphism at the corresponding chart point.
This formulation uses boundaryless models, compatible `C^n` atlases, and a continuous map.
Continuity keeps the map inside the chosen chart source; totalized chart functions alone do not
encode that source condition. -/
theorem isLocalDiffeomorph_iff_writtenInExtChartAt
    [I.Boundaryless] [J.Boundaryless]
    [IsManifold I n M] [IsManifold J n N] (hf : Continuous f) :
    IsLocalDiffeomorph I J n f ↔
      ∀ x : M,
        IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, F) n
          (writtenInExtChartAt I J x f) (extChartAt I x x) := by
  constructor
  · intro h x
    let eI := extChartAtPartialDiffeomorph (n := n) I x
    let eJ := extChartAtPartialDiffeomorph (n := n) J (f x)
    have hI : IsLocalDiffeomorphAt 𝓘(𝕜, E) I n (extChartAt I x).symm
        (extChartAt I x x) :=
      eI.symm.isLocalDiffeomorphAt _ _ _ (mem_extChartAt_target x)
    have hx : (extChartAt I x).symm (extChartAt I x x) = x :=
      (extChartAt I x).left_inv (mem_extChartAt_source x)
    have hJ : IsLocalDiffeomorphAt J 𝓘(𝕜, F) n (extChartAt J (f x))
        (f ((extChartAt I x).symm (extChartAt I x x))) := by
      simpa [eJ, extChartAtPartialDiffeomorph, hx] using
        eJ.isLocalDiffeomorphAt _ _ _ (mem_extChartAt_source (f x))
    have hIf := hI.comp (K := J) (P := N)
      (h ((extChartAt I x).symm (extChartAt I x x)))
    simpa only [writtenInExtChartAt, Function.comp_assoc] using
      hIf.comp (K := 𝓘(𝕜, F)) (P := F) hJ
  · intro h x
    let eI := extChartAtPartialDiffeomorph (n := n) I x
    let eJ := extChartAtPartialDiffeomorph (n := n) J (f x)
    have hI : IsLocalDiffeomorphAt I 𝓘(𝕜, E) n (extChartAt I x) x :=
      eI.isLocalDiffeomorphAt _ _ _ (mem_extChartAt_source x)
    have hbase :
        writtenInExtChartAt I J x f (extChartAt I x x) = extChartAt J (f x) (f x) := by
      simp [writtenInExtChartAt]
    have hJ : IsLocalDiffeomorphAt 𝓘(𝕜, F) J n (extChartAt J (f x)).symm
        (writtenInExtChartAt I J x f (extChartAt I x x)) := by
      rw [hbase]
      exact eJ.symm.isLocalDiffeomorphAt _ _ _ (mem_extChartAt_target (f x))
    have hcomp : IsLocalDiffeomorphAt I J n
        ((extChartAt J (f x)).symm ∘ writtenInExtChartAt I J x f ∘ extChartAt I x) x :=
      (hI.comp (K := 𝓘(𝕜, F)) (P := F) (h x)).comp (K := J) (P := N) hJ
    apply hcomp.congr_of_eventuallyEq
    apply Filter.EventuallyEq.symm
    apply Filter.eventuallyEq_of_mem
      (((isOpen_extChartAt_source (I := I) x).inter
        ((isOpen_extChartAt_source (I := J) (f x)).preimage hf)).mem_nhds
          ⟨mem_extChartAt_source (I := I) x, mem_extChartAt_source (I := J) (f x)⟩)
    intro y hy
    simp only [Function.comp_apply, writtenInExtChartAt]
    rw [(extChartAt I x).left_inv hy.1, (extChartAt J (f x)).left_inv hy.2]

end Coordinates
