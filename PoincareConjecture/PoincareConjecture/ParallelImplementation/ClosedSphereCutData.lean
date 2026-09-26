import PoincareConjecture.ParallelImplementation.ClosedSphereCollarOpen
import PoincareConjecture.ParallelImplementation.OpenCollarCutData
import PoincareConjecture.ProofContract.V1.Decomposition

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace PoincareConjecture.ParallelImplementation.ClosedSphereCutData
open Set
open PoincareConjecture.ProofContract.V1

/-- The actual central slice of a closed product collar. -/
def embeddedSphereCutSlice {M : ClosedThreeManifold}
    (f : Sphere2 × Icc (-1 : ℝ) 1 → M) : Set M :=
  Set.range (fun x : Sphere2 => f (x, ⟨0, by norm_num⟩))

def embeddedSphereCutPositiveSeed {M : ClosedThreeManifold}
    (f : Sphere2 × Icc (-1 : ℝ) 1 → M) (x₀ : Sphere2) : M :=
  f (x₀, ⟨(1 / 2 : ℝ), by norm_num⟩)

def embeddedSphereCutNegativeSeed {M : ClosedThreeManifold}
    (f : Sphere2 × Icc (-1 : ℝ) 1 → M) (x₀ : Sphere2) : M :=
  f (x₀, ⟨(-1 / 2 : ℝ), by norm_num⟩)

/--
A two-sided embedded sphere in a simply connected closed 3-manifold has two
actual complementary components. The conclusion fixes them as the components
meeting the positive and negative halves of the given collar, records their
frontiers, and gives the exact local half-space description needed by the
existing smooth-closure producer. This is the concrete separation data needed for subsequent cutting.
-/
theorem closed_embedded_sphere_cut_sides
    {M : ClosedThreeManifold} (hsc : SimplyConnectedSpace M)
    (f : Sphere2 × Icc (-1 : ℝ) 1 → M)
    (hf : Topology.IsEmbedding f) (x₀ : Sphere2) :
    let S := embeddedSphereCutSlice f
    let U := connectedComponentIn Sᶜ (embeddedSphereCutPositiveSeed f x₀)
    let V := connectedComponentIn Sᶜ (embeddedSphereCutNegativeSeed f x₀)
    IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
    U.Nonempty ∧ V.Nonempty ∧ Disjoint U V ∧ U ∪ V = Sᶜ ∧
    frontier U = S ∧ frontier V = S ∧
    (∀ (x : Sphere2) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1),
      f (x, ⟨t, ⟨by linarith, by linarith⟩⟩) ∈ U) ∧
    (∀ (x : Sphere2) (t : ℝ) (htm1 : -1 < t) (ht0 : t < 0),
      f (x, ⟨t, ⟨by linarith, by linarith⟩⟩) ∈ V) ∧
    (∀ (x : Sphere2) (t : ℝ) (htm1 : -1 < t) (ht1 : t < 1),
      f (x, ⟨t, ⟨by linarith, by linarith⟩⟩) ∈ closure U ↔ 0 ≤ t) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let I := Set.Ioo (-2 : ℝ) 2
  let g : Sphere2 × I → M := fun q =>
    f (q.1, ⟨(q.2 : ℝ) / 2, by constructor <;> linarith [q.2.2.1, q.2.2.2]⟩)
  have hg : Topology.IsOpenEmbedding g := by
    simpa only [I, g] using
      ClosedSphereCollarOpen.closed_sphere_collar_interior_isOpenEmbedding f hf
  haveI : PathConnectedSpace Sphere2 := by
    apply isPathConnected_iff_pathConnectedSpace.mp
    apply isPathConnected_sphere ?_ _ (by norm_num)
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    norm_num
  have hdata := OpenCollarCutData.simplyConnected_open_collar_cut_data
    x₀ g hg
  dsimp only at hdata
  let S : Set M := Set.range (fun y : Sphere2 => g (y, ⟨0, by norm_num [I]⟩))
  let P : Set M := pathComponentIn Sᶜ (g (x₀, ⟨1, by norm_num [I]⟩))
  let N : Set M := pathComponentIn Sᶜ (g (x₀, ⟨-1, by norm_num [I]⟩))
  have hS : S = embeddedSphereCutSlice f := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, by simp [g]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, by simp [g]⟩
  have hseedP : g (x₀, ⟨1, by norm_num [I]⟩) = embeddedSphereCutPositiveSeed f x₀ := by
    rfl
  have hseedN : g (x₀, ⟨-1, by norm_num [I]⟩) = embeddedSphereCutNegativeSeed f x₀ := by
    rfl
  have hSclosed : IsClosed S := by
    rw [hS]
    apply (isCompact_range ?_).isClosed
    fun_prop
  have hO : IsOpen Sᶜ := hSclosed.isOpen_compl
  have hcomp (x : M) (hx : x ∈ Sᶜ) :
      connectedComponentIn Sᶜ x = pathComponentIn Sᶜ x := by
    have hCopen : IsOpen (connectedComponentIn Sᶜ x) := hO.connectedComponentIn
    have hconn : IsConnected (connectedComponentIn Sᶜ x) :=
      isConnected_connectedComponentIn_iff.mpr hx
    have hpath : IsPathConnected (connectedComponentIn Sᶜ x) :=
      hCopen.isConnected_iff_isPathConnected.mp hconn
    apply Set.Subset.antisymm
    · exact hpath.subset_pathComponentIn (mem_connectedComponentIn hx)
        (connectedComponentIn_subset Sᶜ x)
    · exact (isPathConnected_pathComponentIn hx).isConnected.2.subset_connectedComponentIn
        (mem_pathComponentIn_self hx) (pathComponentIn_subset (F := Sᶜ))
  have hPseed : g (x₀, ⟨1, by norm_num [I]⟩) ∈ Sᶜ := by
    change g (x₀, ⟨1, by norm_num [I]⟩) ∉ S
    rintro ⟨y, hy⟩
    have hinj := hg.injective hy
    have hc := congrArg (fun q : Sphere2 × I => (q.2 : ℝ)) hinj
    norm_num [g] at hc
  have hNseed : g (x₀, ⟨-1, by norm_num [I]⟩) ∈ Sᶜ := by
    change g (x₀, ⟨-1, by norm_num [I]⟩) ∉ S
    rintro ⟨y, hy⟩
    have hinj := hg.injective hy
    have hc := congrArg (fun q : Sphere2 × I => (q.2 : ℝ)) hinj
    norm_num [g] at hc
  have hPU : connectedComponentIn Sᶜ (embeddedSphereCutPositiveSeed f x₀) = P := by
    rw [← hseedP]
    exact hcomp _ hPseed
  have hNV : connectedComponentIn Sᶜ (embeddedSphereCutNegativeSeed f x₀) = N := by
    rw [← hseedN]
    exact hcomp _ hNseed
  rcases hdata with ⟨hPopen, hNopen, hPpath, hNpath, hdisj, hunion,
    hfrontP, hfrontN, hpos, hneg, hclosure⟩
  have hposOrig : ∀ (x : Sphere2) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1),
      f (x, ⟨t, ⟨by linarith, by linarith⟩⟩) ∈ P := by
    intro x t ht0 ht1
    let u : I := ⟨2 * t, by constructor <;> linarith⟩
    have := hpos x u (by dsimp [u]; linarith)
    change g (x, u) ∈ P at this
    simpa [g, u] using this
  have hnegOrig : ∀ (x : Sphere2) (t : ℝ) (htm1 : -1 < t) (ht0 : t < 0),
      f (x, ⟨t, ⟨by linarith, by linarith⟩⟩) ∈ N := by
    intro x t htm1 ht0
    let u : I := ⟨2 * t, by constructor <;> linarith⟩
    have := hneg x u (by dsimp [u]; linarith)
    change g (x, u) ∈ N at this
    simpa [g, u] using this
  have hclosureOrig : ∀ (x : Sphere2) (t : ℝ) (htm1 : -1 < t) (ht1 : t < 1),
      f (x, ⟨t, ⟨by linarith, by linarith⟩⟩) ∈ closure P ↔ 0 ≤ t := by
    intro x t htm1 ht1
    let u : I := ⟨2 * t, by constructor <;> linarith⟩
    have := hclosure x u
    change g (x, u) ∈ closure P ↔ 0 ≤ (u : ℝ) at this
    simpa [g, u] using this
  change IsOpen (connectedComponentIn (embeddedSphereCutSlice f)ᶜ
      (embeddedSphereCutPositiveSeed f x₀)) ∧
    IsOpen (connectedComponentIn (embeddedSphereCutSlice f)ᶜ
      (embeddedSphereCutNegativeSeed f x₀)) ∧
    IsConnected (connectedComponentIn (embeddedSphereCutSlice f)ᶜ
      (embeddedSphereCutPositiveSeed f x₀)) ∧
    IsConnected (connectedComponentIn (embeddedSphereCutSlice f)ᶜ
      (embeddedSphereCutNegativeSeed f x₀)) ∧ _
  rw [← hS, hPU, hNV]
  refine ⟨hPopen, hNopen, hPpath.isConnected, hNpath.isConnected,
    hPpath.nonempty, hNpath.nonempty, hdisj, hunion,
    ?_, ?_, hposOrig, hnegOrig, hclosureOrig⟩
  · simpa [P, S] using hfrontP
  · simpa [N, S] using hfrontN
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ClosedSphereCutData
