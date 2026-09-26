import PoincareConjecture.ParallelImplementation.OpenCollarSideSeparation
import PoincareConjecture.ParallelImplementation.OpenCollarComponentFrontiers
import PoincareConjecture.ParallelImplementation.OpenCollarComplementComponents
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.OpenCollarCutData
open Set
/-- Concrete two-sided cut data for the SAME given open collar. All component,
frontier and local closure conclusions are produced, none are assumed. -/
theorem simplyConnected_open_collar_cut_data
    {Y M : Type*} [TopologicalSpace Y] [CompactSpace Y] [PathConnectedSpace Y]
    [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [LocallyPathConnectedSpace M] [SimplyConnectedSpace M]
    (p : Y) (f : Y × Set.Ioo (-2 : ℝ) 2 → M) (hf : Topology.IsOpenEmbedding f) :
    let S : Set M := Set.range (fun y : Y => f (y, ⟨0, by norm_num⟩))
    let P := pathComponentIn Sᶜ (f (p, ⟨(1 : ℝ), by norm_num⟩))
    let N := pathComponentIn Sᶜ (f (p, ⟨(-1 : ℝ), by norm_num⟩))
    IsOpen P ∧ IsOpen N ∧ IsPathConnected P ∧ IsPathConnected N ∧
      Disjoint P N ∧ P ∪ N = Sᶜ ∧ frontier P = S ∧ frontier N = S ∧
      (∀ y : Y, ∀ t : Set.Ioo (-2 : ℝ) 2, 0 < (t : ℝ) → f (y,t) ∈ P) ∧
      (∀ y : Y, ∀ t : Set.Ioo (-2 : ℝ) 2, (t : ℝ) < 0 → f (y,t) ∈ N) ∧
      (∀ y : Y, ∀ t : Set.Ioo (-2 : ℝ) 2, f (y,t) ∈ closure P ↔ 0 ≤ (t : ℝ)) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  dsimp
  let I := Set.Ioo (-2 : ℝ) 2
  let z0 : I := ⟨0, by norm_num [I]⟩
  let zp : I := ⟨1, by norm_num [I]⟩
  let zm : I := ⟨-1, by norm_num [I]⟩
  let S : Set M := Set.range (fun y : Y => f (y, z0))
  let P : Set M := pathComponentIn Sᶜ (f (p, zp))
  let N : Set M := pathComponentIn Sᶜ (f (p, zm))

  have hfront := OpenCollarComponentFrontiers.collar_component_frontiers p f hf
  change frontier N = S ∧ frontier P = S at hfront
  rcases hfront with ⟨hfrontN, hfrontP⟩
  have hsep := OpenCollarSideSeparation.collar_sides_not_joined_in_complement p f hf
  change ¬ JoinedIn Sᶜ (f (p, zm)) (f (p, zp)) at hsep

  -- Rescale the smaller producer's collar by q ↦ 2q.
  let K := Set.Ioo (-1 : ℝ) 1
  let e : K → I := fun q => ⟨2 * (q : ℝ), by
    constructor <;> nlinarith [q.2.1, q.2.2]⟩
  let ei : I → K := fun t => ⟨(t : ℝ) / 2, by
    constructor <;> nlinarith [t.2.1, t.2.2]⟩
  have he_cont : Continuous e := by
    apply Continuous.subtype_mk
    fun_prop
  have hei_cont : Continuous ei := by
    apply Continuous.subtype_mk
    fun_prop
  have heei : Function.LeftInverse ei e := by
    intro q
    apply Subtype.ext
    dsimp [ei, e]
    ring
  have heie : Function.RightInverse ei e := by
    intro t
    apply Subtype.ext
    dsimp [ei, e]
    ring
  let eh : K ≃ₜ I :=
    { toEquiv := ⟨e, ei, heei, heie⟩
      continuous_toFun := he_cont
      continuous_invFun := hei_cont }
  let g : Y × K → Y × I := fun z => (z.1, e z.2)
  let gi : Y × I → Y × K := fun z => (z.1, ei z.2)
  have hg_left : Function.LeftInverse gi g := by
    intro z
    cases z with
    | mk y q =>
        simp only [gi, g, Prod.mk.injEq, true_and]
        exact heei q
  have hg_right : Function.RightInverse gi g := by
    intro z
    cases z with
    | mk y q =>
        simp only [gi, g, Prod.mk.injEq, true_and]
        exact heie q
  let gh : (Y × K) ≃ₜ (Y × I) :=
    { toEquiv := ⟨g, gi, hg_left, hg_right⟩
      continuous_toFun := by
        exact continuous_prodMk.mpr ⟨continuous_fst, he_cont.comp continuous_snd⟩
      continuous_invFun := by
        exact continuous_prodMk.mpr ⟨continuous_fst, hei_cont.comp continuous_snd⟩ }
  let f' : Y × K → M := fun z => f (g z)
  have hf' : Topology.IsOpenEmbedding f' := by
    dsimp [f', g]
    exact hf.comp gh.isOpenEmbedding
  have hsmall := OpenCollarComplementComponents.complement_joined_to_one_of_two_collar_sides p f' hf'
  have hscale (y : Y) (q : K) : f' (y, q) = f (y, e q) := rfl
  have hsmallS : (Set.range (fun y : Y => f' (y, ⟨0, by norm_num [K]⟩))) = S := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, by simp [hscale, e, z0, K]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, by simp [hscale, e, z0, K]⟩
  have hjoinedEither (x : M) (hx : x ∈ Sᶜ) :
      JoinedIn Sᶜ x (f (p, zp)) ∨ JoinedIn Sᶜ x (f (p, zm)) := by
    have hx' : x ∉ Set.range (fun y : Y => f' (y, ⟨0, by norm_num [K]⟩)) := by
      simpa [hsmallS] using hx
    have hh := hsmall x hx'
    change JoinedIn _ x (f' (p, ⟨(1 / 2 : ℝ), by norm_num [K]⟩)) ∨
      JoinedIn _ x (f' (p, ⟨(-1 / 2 : ℝ), by norm_num [K]⟩)) at hh
    have hpseed : f' (p, ⟨(1 / 2 : ℝ), by norm_num [K]⟩) = f (p, zp) := by
      change f (p, e ⟨(1 / 2 : ℝ), by norm_num [K]⟩) = f (p, zp)
      congr 1
      apply Prod.ext
      · rfl
      apply Subtype.ext
      norm_num [e, zp]
    have hmseed : f' (p, ⟨(-1 / 2 : ℝ), by norm_num [K]⟩) = f (p, zm) := by
      change f (p, e ⟨(-1 / 2 : ℝ), by norm_num [K]⟩) = f (p, zm)
      congr 1
      apply Prod.ext
      · rfl
      apply Subtype.ext
      norm_num [e, zm]
    rcases hh with hp | hm
    · rw [hsmallS] at hp
      exact Or.inl (by simpa [f', g, e, zp] using hp)
    · rw [hsmallS] at hm
      norm_num [f', g, e, zm] at hm
      exact Or.inr (by simpa [zm, I] using hm)

  -- The ambient complement is open, so its path components are open.
  have hSclosed : IsClosed S := by
    apply (isCompact_range ?_).isClosed
    fun_prop
  have hOopen : IsOpen Sᶜ := hSclosed.isOpen_compl
  have hPopen' : IsOpen P := by simpa [P] using hOopen.pathComponentIn (f (p, zp))
  have hNopen' : IsOpen N := by simpa [N] using hOopen.pathComponentIn (f (p, zm))
  have hseedP : f (p, zp) ∈ Sᶜ := by
    change f (p, zp) ∉ S
    rintro ⟨y, hy⟩
    have hpairs := hf.injective hy
    have hcoord := congrArg (fun a : Y × I => (a.2 : ℝ)) hpairs
    norm_num [z0, zp] at hcoord
  have hseedN : f (p, zm) ∈ Sᶜ := by
    change f (p, zm) ∉ S
    rintro ⟨y, hy⟩
    have hpairs := hf.injective hy
    have hcoord := congrArg (fun a : Y × I => (a.2 : ℝ)) hpairs
    norm_num [z0, zm] at hcoord
  have hPpath : IsPathConnected P := by
    simpa [P] using (isPathConnected_pathComponentIn hseedP)
  have hNpath : IsPathConnected N := by
    simpa [N] using (isPathConnected_pathComponentIn hseedN)
  have hdisj : Disjoint P N := by
    apply Set.disjoint_left.mpr
    intro x hxP hxN
    have hxp : JoinedIn Sᶜ (f (p, zp)) x := by change JoinedIn Sᶜ (f (p, zp)) x at hxP; exact hxP
    have hxn : JoinedIn Sᶜ (f (p, zm)) x := by change JoinedIn Sᶜ (f (p, zm)) x at hxN; exact hxN
    exact hsep (hxn.trans hxp.symm)
  have hunion : P ∪ N = Sᶜ := by
    apply Set.Subset.antisymm
    · rintro x (hx | hx)
      · exact pathComponentIn_subset hx
      · exact pathComponentIn_subset hx
    · intro x hx
      rcases hjoinedEither x hx with hp | hn
      · exact Or.inl hp.symm
      · exact Or.inr hn.symm

  have hpositive : ∀ y : Y, ∀ t : I, 0 < (t : ℝ) → f (y,t) ∈ P := by
    intro y t ht
    let J : Set.Ioo (0 : ℝ) 2 := ⟨t, ht, t.2.2⟩
    let ip : Set.Ioo (0 : ℝ) 2 → I := fun a => ⟨a, by exact ⟨by linarith [a.2.1], a.2.2⟩⟩
    let gp : Y × Set.Ioo (0 : ℝ) 2 → M := fun z => f (z.1, ip z.2)
    have hpcY : PathConnectedSpace Y := ‹PathConnectedSpace Y›
    haveI : PathConnectedSpace (Set.Ioo (0 : ℝ) 2) :=
      isPathConnected_iff_pathConnectedSpace.mp <| (convex_Ioo (0 : ℝ) 2).isPathConnected ⟨1, by norm_num⟩
    have hcont : Continuous gp := by fun_prop
    have hdisjRange : Set.range gp ⊆ Sᶜ := by
      intro x hx
      rcases hx with ⟨z, rfl⟩
      change f (z.1, ip z.2) ∉ S
      rintro ⟨y', hy'⟩
      have hpairs := hf.injective hy'
      have hzero := congrArg (fun a : Y × I => (a.2 : ℝ)) hpairs
      exact (ne_of_gt z.2.2.1) (by simpa [ip, z0] using hzero.symm)
    have hseed : f (p, zp) ∈ Set.range gp := by
      refine ⟨(p, ⟨1, by norm_num⟩), ?_⟩
      apply congrArg f
      apply Prod.ext rfl
      apply Subtype.ext
      rfl
    have hrange : Set.range gp ⊆ P :=
      (isPathConnected_range hcont).subset_pathComponentIn hseed hdisjRange
    exact hrange ⟨(y, J), by simp [gp, ip, J]⟩
  have hnegative : ∀ y : Y, ∀ t : I, (t : ℝ) < 0 → f (y,t) ∈ N := by
    intro y t ht
    let J : Set.Ioo (-2 : ℝ) 0 := ⟨t, t.2.1, ht⟩
    let im : Set.Ioo (-2 : ℝ) 0 → I := fun a => ⟨a, by exact ⟨a.2.1, by linarith [a.2.2]⟩⟩
    let gm : Y × Set.Ioo (-2 : ℝ) 0 → M := fun z => f (z.1, im z.2)
    haveI : PathConnectedSpace (Set.Ioo (-2 : ℝ) 0) :=
      isPathConnected_iff_pathConnectedSpace.mp <| (convex_Ioo (-2 : ℝ) 0).isPathConnected ⟨-1, by norm_num⟩
    have hcont : Continuous gm := by fun_prop
    have hdisjRange : Set.range gm ⊆ Sᶜ := by
      intro x hx
      rcases hx with ⟨z, rfl⟩
      change f (z.1, im z.2) ∉ S
      rintro ⟨y', hy'⟩
      have hpairs := hf.injective hy'
      have hzero := congrArg (fun a : Y × I => (a.2 : ℝ)) hpairs
      exact (ne_of_lt z.2.2.2) (by simpa [im, z0] using hzero.symm)
    have hseed : f (p, zm) ∈ Set.range gm := by
      refine ⟨(p, ⟨-1, by norm_num⟩), ?_⟩
      apply congrArg f
      apply Prod.ext rfl
      apply Subtype.ext
      rfl
    have hrange : Set.range gm ⊆ N :=
      (isPathConnected_range hcont).subset_pathComponentIn hseed hdisjRange
    exact hrange ⟨(y, J), by simp [gm, im, J]⟩

  have hclosure : ∀ y : Y, ∀ t : I, f (y,t) ∈ closure P ↔ 0 ≤ (t : ℝ) := by
    intro y t
    constructor
    · intro hcl
      by_contra hnot
      have hneg : (t : ℝ) < 0 := lt_of_not_ge hnot
      have hn : f (y,t) ∈ N := hnegative y t hneg
      obtain ⟨x, hxN, hxP⟩ := (mem_closure_iff_nhds.mp hcl) N (hNopen'.mem_nhds hn)
      exact (Set.disjoint_left.mp hdisj) hxP hxN
    · intro hnonneg
      rcases eq_or_lt_of_le hnonneg with hzero | hpos
      · have hz : f (y,t) ∈ S := by
          refine ⟨y, ?_⟩
          apply congrArg f
          apply Prod.ext
          · rfl
          · apply Subtype.ext
            exact hzero
        have hzfront : f (y,t) ∈ frontier P := by rw [hfrontP]; exact hz
        exact frontier_subset_closure hzfront
      · exact subset_closure (hpositive y t hpos)
  exact ⟨hPopen', hNopen', hPpath, hNpath, hdisj, hunion,
    hfrontP, hfrontN, hpositive, hnegative, hclosure⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.OpenCollarCutData
