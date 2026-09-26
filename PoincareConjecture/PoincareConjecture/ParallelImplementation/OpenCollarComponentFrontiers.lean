import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.OpenCollarComponentFrontiers
open Set
/-- The actual two collar-side components have the entire central slice as
frontier. This does not assume or assert that the two components are distinct. -/
theorem collar_component_frontiers
    {Y M : Type*} [TopologicalSpace Y] [CompactSpace Y] [PathConnectedSpace Y]
    [TopologicalSpace M] [T2Space M] [LocallyPathConnectedSpace M]
    (p : Y) (f : Y × Set.Ioo (-2 : ℝ) 2 → M)
    (hf : Topology.IsOpenEmbedding f) :
    let S : Set M := Set.range (fun y : Y => f (y, ⟨0, by norm_num⟩))
    frontier (pathComponentIn Sᶜ (f (p, ⟨(-1 : ℝ), by norm_num⟩))) = S ∧
    frontier (pathComponentIn Sᶜ (f (p, ⟨(1 : ℝ), by norm_num⟩))) = S :=
/- SWARM_PROOF_BEGIN -/
by
  dsimp
  let I : Type := Set.Ioo (-2 : ℝ) 2
  let Jp : Type := Set.Ioo (0 : ℝ) 2
  let Jm : Type := Set.Ioo (-2 : ℝ) 0
  let z0 : I := ⟨0, by norm_num⟩
  let zp : I := ⟨1, by norm_num⟩
  let zm : I := ⟨-1, by norm_num⟩
  let S : Set M := Set.range (fun y : Y => f (y, z0))
  let O : Set M := Sᶜ
  let ip : Jp → I := fun t => ⟨t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩
  let im : Jm → I := fun t => ⟨t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩
  let gp : Y × Jp → M := fun z => f (z.1, ip z.2)
  let gm : Y × Jm → M := fun z => f (z.1, im z.2)
  have hcentral : IsClosed S := by
    apply (isCompact_range ?_).isClosed
    fun_prop
  have hO : IsOpen O := hcentral.isOpen_compl
  haveI hpJ : PathConnectedSpace Jp := by
    exact isPathConnected_iff_pathConnectedSpace.mp <|
      (convex_Ioo (0 : ℝ) 2).isPathConnected ⟨1, by norm_num⟩
  haveI hmJ : PathConnectedSpace Jm := by
    exact isPathConnected_iff_pathConnectedSpace.mp <|
      (convex_Ioo (-2 : ℝ) 0).isPathConnected ⟨-1, by norm_num⟩
  have hgp : Continuous gp := by
    apply hf.continuous.comp
    fun_prop
  have hgm : Continuous gm := by
    apply hf.continuous.comp
    fun_prop
  have hgp_disj : Set.range gp ⊆ O := by
    intro q hq
    rcases hq with ⟨a, rfl⟩
    change f (a.1, ip a.2) ∉ Set.range (fun y : Y => f (y, z0))
    rintro ⟨y, hy⟩
    have heq := hf.injective hy
    have hcoord : ip a.2 = z0 := (congrArg Prod.snd heq).symm
    have hval : (a.2 : ℝ) = 0 := by
      simpa [ip, z0] using congrArg (fun t : I => (t : ℝ)) hcoord
    exact (ne_of_gt a.2.2.1) hval
  have hgm_disj : Set.range gm ⊆ O := by
    intro q hq
    rcases hq with ⟨a, rfl⟩
    change f (a.1, im a.2) ∉ Set.range (fun y : Y => f (y, z0))
    rintro ⟨y, hy⟩
    have heq := hf.injective hy
    have hcoord : im a.2 = z0 := (congrArg Prod.snd heq).symm
    have hval : (a.2 : ℝ) = 0 := by
      simpa [im, z0] using congrArg (fun t : I => (t : ℝ)) hcoord
    exact (ne_of_lt a.2.2.2) hval
  have hpSeed : f (p, zp) ∈ Set.range gp := by
    refine ⟨(p, ⟨1, by norm_num⟩), ?_⟩
    simp [gp, ip, zp]
  have hmSeed : f (p, zm) ∈ Set.range gm := by
    refine ⟨(p, ⟨-1, by norm_num⟩), ?_⟩
    simp [gm, im, zm]
  let Cp : Set M := pathComponentIn O (f (p, zp))
  let Cm : Set M := pathComponentIn O (f (p, zm))
  have hCp : Set.range gp ⊆ Cp :=
    (isPathConnected_range hgp).subset_pathComponentIn hpSeed hgp_disj
  have hCm : Set.range gm ⊆ Cm :=
    (isPathConnected_range hgm).subset_pathComponentIn hmSeed hgm_disj
  have hCpOpen : IsOpen Cp := hO.pathComponentIn _
  have hCmOpen : IsOpen Cm := hO.pathComponentIn _
  have hcentralClosureP (y : Y) : f (y, z0) ∈ closure Cp := by
    let line : I → M := fun t => f (y, t)
    have hline : Continuous line := by
      dsimp [line]
      fun_prop
    have hzero : z0 ∈ closure (Set.Ioi z0 : Set I) := by
      rw [closure_Ioi' (α := I) (a := z0) ⟨zp, by change (0 : ℝ) < 1; norm_num⟩]
      exact self_mem_Ici
    have hlineClose : line z0 ∈ closure (line '' (Set.Ioi z0 : Set I)) :=
      image_closure_subset_closure_image hline ⟨z0, hzero, rfl⟩
    apply closure_mono ?_ hlineClose
    rintro q ⟨t, ht, rfl⟩
    have htRange : f (y, t) ∈ Set.range gp := by
      refine ⟨(y, ⟨(t : ℝ), ht, t.2.2⟩), ?_⟩
      simp [gp, ip]
    exact hCp htRange
  have hcentralClosureM (y : Y) : f (y, z0) ∈ closure Cm := by
    let line : I → M := fun t => f (y, t)
    have hline : Continuous line := by
      dsimp [line]
      fun_prop
    have hzero : z0 ∈ closure (Set.Iio z0 : Set I) := by
      rw [closure_Iio' (α := I) (a := z0) ⟨zm, by change (-1 : ℝ) < 0; norm_num⟩]
      exact self_mem_Iic
    have hlineClose : line z0 ∈ closure (line '' (Set.Iio z0 : Set I)) :=
      image_closure_subset_closure_image hline ⟨z0, hzero, rfl⟩
    apply closure_mono ?_ hlineClose
    rintro q ⟨t, ht, rfl⟩
    have htRange : f (y, t) ∈ Set.range gm := by
      refine ⟨(y, ⟨(t : ℝ), t.2.1, ht⟩), ?_⟩
      simp [gm, im]
    exact hCm htRange
  have hSclosureP : S ⊆ closure Cp := by
    rintro q ⟨y, rfl⟩
    exact hcentralClosureP y
  have hSclosureM : S ⊆ closure Cm := by
    rintro q ⟨y, rfl⟩
    exact hcentralClosureM y
  have frontier_subset (x : M) (hx : x ∈ O) :
      frontier (pathComponentIn O x) ⊆ S := by
    intro q hq
    rw [← closure_sdiff_interior] at hq
    have hqcl : q ∈ closure (pathComponentIn O x) := hq.1
    by_contra hqS
    have hqO : q ∈ O := by simpa [O] using hqS
    rcases (path_connected_basis q).mem_iff.mp (hO.mem_nhds hqO) with
      ⟨V, ⟨hVn, hVpath⟩, hVO⟩
    have hqV : q ∈ V := mem_of_mem_nhds hVn
    obtain ⟨w, hwV, hwC⟩ := (mem_closure_iff_nhds.mp hqcl) V hVn
    have hqw : JoinedIn O q w := (hVpath.joinedIn q hqV w hwV).mono hVO
    have hqC : q ∈ pathComponentIn O x := by
      change JoinedIn O x q
      change JoinedIn O x w at hwC
      exact hwC.trans hqw.symm
    have hCinterior : pathComponentIn O x ⊆ interior (pathComponentIn O x) :=
      subset_interior_iff_isOpen.mpr (IsOpen.pathComponentIn hO x)
    exact hq.2 (hCinterior hqC)
  have hseedp : f (p, zp) ∈ O := hgp_disj hpSeed
  have hseedm : f (p, zm) ∈ O := hgm_disj hmSeed
  constructor
  · apply Set.Subset.antisymm
    · exact frontier_subset _ hseedm
    · intro q hq
      rw [frontier_eq_closure_inter_closure]
      refine ⟨?_, ?_⟩
      · exact hSclosureM hq
      · have hqnot : q ∉ Cm := by
          intro hqC
          change q ∈ pathComponentIn O (f (p, zm)) at hqC
          have hqO : q ∈ O := pathComponentIn_subset (F := O) hqC
          have hqnotS : q ∉ S := by
            simpa [O] using hqO
          exact hqnotS hq
        exact subset_closure hqnot
  · apply Set.Subset.antisymm
    · exact frontier_subset _ hseedp
    · intro q hq
      rw [frontier_eq_closure_inter_closure]
      refine ⟨?_, ?_⟩
      · exact hSclosureP hq
      · have hqnot : q ∉ Cp := by
          intro hqC
          change q ∈ pathComponentIn O (f (p, zp)) at hqC
          have hqO : q ∈ O := pathComponentIn_subset (F := O) hqC
          have hqnotS : q ∉ S := by
            simpa [O] using hqO
          exact hqnotS hq
        exact subset_closure hqnot
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.OpenCollarComponentFrontiers
