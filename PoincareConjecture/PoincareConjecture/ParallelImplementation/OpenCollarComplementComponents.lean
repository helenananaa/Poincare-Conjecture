import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.OpenCollarComplementComponents
open Set
/-- Every complementary point of a compact connected two-sided open collar
joins one of its two fixed side seeds. The sides are not assumed distinct. -/
theorem complement_joined_to_one_of_two_collar_sides
    {Y M : Type*} [TopologicalSpace Y] [CompactSpace Y] [PathConnectedSpace Y]
    [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [LocallyPathConnectedSpace M]
    (p : Y) (f : Y × Set.Ioo (-1 : ℝ) 1 → M)
    (hf : Topology.IsOpenEmbedding f) :
    let S : Set M := Set.range (fun y : Y => f (y, ⟨0, by norm_num⟩))
    ∀ x : M, x ∉ S →
      JoinedIn Sᶜ x (f (p, ⟨(1/2 : ℝ), by norm_num⟩)) ∨
      JoinedIn Sᶜ x (f (p, ⟨(-1/2 : ℝ), by norm_num⟩)) :=
/- SWARM_PROOF_BEGIN -/
by
  dsimp only
  intro x hx
  let c : Set.Ioo (-1 : ℝ) 1 := ⟨0, by norm_num⟩
  let cplus : Set.Ioo (-1 : ℝ) 1 := ⟨(1 / 2 : ℝ), by norm_num⟩
  let cminus : Set.Ioo (-1 : ℝ) 1 := ⟨(-1 / 2 : ℝ), by norm_num⟩
  let S : Set M := Set.range (fun y : Y => f (y, c))
  let J : Set ℝ := Set.Ioo (-1 : ℝ) 1
  let Fplus : Set J := {r | (0 : ℝ) < (r : ℝ)}
  let Fminus : Set J := {r | (r : ℝ) < 0}
  let F : Set J := {r | (r : ℝ) ≠ 0}
  change x ∉ S at hx

  have hScompact : IsCompact S := by
    dsimp [S]
    exact isCompact_range
      (hf.continuous.comp (continuous_prodMk.mpr ⟨continuous_id, continuous_const⟩))
  have hSclosed : IsClosed S := hScompact.isClosed
  let U : Set M := Sᶜ
  have hU : IsOpen U := by
    dsimp [U]
    exact hSclosed.isOpen_compl
  have hxU : x ∈ U := by simpa [U] using hx
  let C : Set M := pathComponentIn U x
  have hxC : x ∈ C := mem_pathComponentIn_self hxU
  have hCU : C ⊆ U := pathComponentIn_subset
  have hCopen : IsOpen C := by
    dsimp [C]
    exact hU.pathComponentIn x

  have hs0 : f (p, c) ∈ S := ⟨p, rfl⟩
  have hs0notC : f (p, c) ∉ C := by
    intro hs
    have hsU := hCU hs
    have hsnot : f (p, c) ∉ S := by simpa [U] using hsU
    exact hsnot hs0
  have hCne : C ≠ univ := by
    intro heq
    have : f (p, c) ∈ C := by rw [heq]; simp
    exact hs0notC this
  have hfrontNonempty : (frontier C).Nonempty :=
    nonempty_frontier_iff.mpr ⟨⟨x, hxC⟩, hCne⟩
  obtain ⟨y, hyfront⟩ := hfrontNonempty
  have hynotC : y ∉ C := by
    exact (Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hCopen)) hyfront
  rw [frontier_eq_closure_inter_closure] at hyfront
  have hyclosure : y ∈ closure C := hyfront.1

  have hyS : y ∈ S := by
    by_contra hynotS
    have hyU : y ∈ U := by simpa [U] using hynotS
    obtain ⟨V, ⟨hVnhds, hVpc⟩, hVU⟩ :=
      (path_connected_basis y).mem_iff.mp (hU.mem_nhds hyU)
    have hyV : y ∈ V := mem_of_mem_nhds hVnhds
    obtain ⟨z, hzV, hzC⟩ := (mem_closure_iff_nhds.mp hyclosure) V hVnhds
    have hyz : JoinedIn U y z := (hVpc.joinedIn y hyV z hzV).mono hVU
    have hzjoin : JoinedIn U x z := by
      change z ∈ pathComponentIn U x at hzC
      exact hzC
    have hyC : y ∈ C := by
      change JoinedIn U x y
      exact (hyz.trans hzjoin.symm).symm
    exact hynotC hyC

  have hyW : y ∈ Set.range f := by
    rcases hyS with ⟨a, ha⟩
    exact ⟨(a, c), ha⟩
  obtain ⟨w, hwW, hwC⟩ :=
    (mem_closure_iff.mp hyclosure) (Set.range f) hf.isOpen_range hyW
  rcases hwW with ⟨q, rfl⟩
  have hqC : f q ∈ C := hwC
  have hqnotS : f q ∉ S := by
    have hqU := hCU hqC
    simpa [U] using hqU
  have hqne : (q.2 : ℝ) ≠ 0 := by
    intro hzero
    have hq2 : q.2 = c := Subtype.ext hzero
    have hqS : f q ∈ S := by
      refine ⟨q.1, ?_⟩
      change f (q.1, c) = f (q.1, q.2)
      rw [hq2]
    exact hqnotS hqS

  have hvalplus : Subtype.val '' Fplus = Set.Ioo (0 : ℝ) 1 := by
    ext r
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨ha, a.2.2⟩
    · intro hr
      refine ⟨⟨r, ?_⟩, hr.1, rfl⟩
      change (-1 : ℝ) < r ∧ r < 1
      exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hvalminus : Subtype.val '' Fminus = Set.Ioo (-1 : ℝ) 0 := by
    ext r
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.2.1, ha⟩
    · intro hr
      refine ⟨⟨r, ?_⟩, hr.2, rfl⟩
      change (-1 : ℝ) < r ∧ r < 1
      exact ⟨by linarith [hr.1], by linarith [hr.2]⟩

  have hjoinPlus : ∀ a b : J, 0 < (a : ℝ) → 0 < (b : ℝ) → JoinedIn Fplus a b := by
    intro a b ha hb
    have haF : a ∈ Fplus := ha
    have hbF : b ∈ Fplus := hb
    have haR : (a : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨ha, a.2.2⟩
    have hbR : (b : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨hb, b.2.2⟩
    have hpc : IsPathConnected (Set.Ioo (0 : ℝ) 1) :=
      (convex_Ioo (0 : ℝ) 1).isPathConnected ⟨(1 / 2 : ℝ), by norm_num⟩
    have hab : JoinedIn (Set.Ioo (0 : ℝ) 1) (a : ℝ) (b : ℝ) :=
      hpc.joinedIn (a : ℝ) haR (b : ℝ) hbR
    have himage : JoinedIn (Subtype.val '' Fplus) (a : ℝ) (b : ℝ) := by
      rw [hvalplus]
      exact hab
    exact (Topology.IsInducing.subtypeVal (t := J)).joinedIn_image haF hbF |>.mp himage
  have hjoinMinus : ∀ a b : J, (a : ℝ) < 0 → (b : ℝ) < 0 → JoinedIn Fminus a b := by
    intro a b ha hb
    have haF : a ∈ Fminus := ha
    have hbF : b ∈ Fminus := hb
    have haR : (a : ℝ) ∈ Set.Ioo (-1 : ℝ) 0 := ⟨a.2.1, ha⟩
    have hbR : (b : ℝ) ∈ Set.Ioo (-1 : ℝ) 0 := ⟨b.2.1, hb⟩
    have hpc : IsPathConnected (Set.Ioo (-1 : ℝ) 0) :=
      (convex_Ioo (-1 : ℝ) 0).isPathConnected ⟨(-1 / 2 : ℝ), by norm_num⟩
    have hab : JoinedIn (Set.Ioo (-1 : ℝ) 0) (a : ℝ) (b : ℝ) :=
      hpc.joinedIn (a : ℝ) haR (b : ℝ) hbR
    have himage : JoinedIn (Subtype.val '' Fminus) (a : ℝ) (b : ℝ) := by
      rw [hvalminus]
      exact hab
    exact (Topology.IsInducing.subtypeVal (t := J)).joinedIn_image haF hbF |>.mp himage

  have hY : JoinedIn (Set.univ : Set Y) q.1 p := by
    exact (isPathConnected_univ : IsPathConnected (Set.univ : Set Y)).joinedIn
      q.1 (Set.mem_univ _) p (Set.mem_univ _)
  have himageU : f '' (Set.univ ×ˢ F) ⊆ U := by
    intro m hm
    rcases hm with ⟨⟨a, b⟩, hab, rfl⟩
    change f (a, b) ∉ S
    intro hmS
    have hbne : (b : ℝ) ≠ 0 := hab.2
    rcases hmS with ⟨a', ha'⟩
    have hpairs : (a, b) = (a', c) := hf.injective ha'.symm
    have hbzero : (b : ℝ) = 0 := by
      have hsnd := congrArg Prod.snd hpairs
      exact congrArg Subtype.val hsnd
    exact hbne hbzero

  rcases lt_or_gt_of_ne (Ne.symm hqne) with hqpos | hqneg
  · left
    have hcoord : JoinedIn F q.2 cplus := by
      exact (hjoinPlus q.2 cplus hqpos (by norm_num)).mono (by
        intro r hr
        change 0 < (r : ℝ) at hr
        change (r : ℝ) ≠ 0
        exact ne_of_gt hr)
    have hprod : JoinedIn (Set.univ ×ˢ F) (q.1, q.2) (p, cplus) := hY.prod hcoord
    have hmap : JoinedIn U (f (q.1, q.2)) (f (p, cplus)) :=
      hprod.map hf.continuous |>.mono himageU
    have hfrom : JoinedIn U x (f (p, cplus)) := by
      change JoinedIn U x (f q) at hqC
      exact hqC.trans hmap
    exact hfrom
  · right
    have hcoord : JoinedIn F q.2 cminus := by
      exact (hjoinMinus q.2 cminus hqneg (by norm_num)).mono (by
        intro r hr
        change (r : ℝ) < 0 at hr
        change (r : ℝ) ≠ 0
        exact ne_of_lt hr)
    have hprod : JoinedIn (Set.univ ×ˢ F) (q.1, q.2) (p, cminus) := hY.prod hcoord
    have hmap : JoinedIn U (f (q.1, q.2)) (f (p, cminus)) :=
      hprod.map hf.continuous |>.mono himageU
    have hfrom : JoinedIn U x (f (p, cminus)) := by
      change JoinedIn U x (f q) at hqC
      exact hqC.trans hmap
    exact hfrom
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.OpenCollarComplementComponents
