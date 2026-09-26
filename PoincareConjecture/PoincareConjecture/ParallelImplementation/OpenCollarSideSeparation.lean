import PoincareConjecture.ParallelImplementation.CircleLiftObstruction
import PoincareConjecture.ParallelImplementation.OpenCollarCircleMap
import PoincareConjecture.ParallelImplementation.OpenCollarExteriorRetraction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.OpenCollarSideSeparation
open Set
open scoped unitInterval Topology
/-- Actual opposite collar sides cannot be joined avoiding the central slice
in a simply connected ambient space. No separation hypothesis is supplied. -/
theorem collar_sides_not_joined_in_complement
    {Y M : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [TopologicalSpace M] [T2Space M] [SimplyConnectedSpace M]
    (p : Y) (f : Y × Set.Ioo (-2 : ℝ) 2 → M)
    (hf : Topology.IsOpenEmbedding f) :
    let S : Set M := Set.range (fun y : Y => f (y, ⟨0, by norm_num⟩))
    ¬ JoinedIn Sᶜ (f (p, ⟨(-1 : ℝ), by norm_num⟩))
      (f (p, ⟨(1 : ℝ), by norm_num⟩)) :=
/- SWARM_PROOF_BEGIN -/
by
  dsimp only
  intro hjoined
  classical
  let S : Set M := Set.range (fun y : Y => f (y, ⟨0, by norm_num⟩))
  let O : Set M := f '' {q : Y × Set.Ioo (-2 : ℝ) 2 | |(q.2 : ℝ)| < 1}
  rcases OpenCollarCircleMap.exists_collar_circle_map f hf with
    ⟨c, hc, hcO, hcCollar⟩
  rcases OpenCollarExteriorRetraction.exists_collar_exterior_retraction f hf with
    ⟨r, hrcont, hrmap, hreq, hrcollar⟩

  let tm : Set.Ioo (-2 : ℝ) 2 := ⟨-1, by norm_num⟩
  let tp : Set.Ioo (-2 : ℝ) 2 := ⟨1, by norm_num⟩
  let a : M := f (p, tm)
  let b : M := f (p, tp)
  have hjoin : JoinedIn Sᶜ a b := by
    simpa [a, b, tm, tp] using hjoined

  have haO : a ∈ Oᶜ := by
    change a ∉ O
    rintro ⟨q, hq, heq⟩
    have hpq : q = (p, tm) := hf.injective heq
    have hcoord := congrArg (fun z : Y × Set.Ioo (-2 : ℝ) 2 => (z.2 : ℝ)) hpq
    change |(q.2 : ℝ)| < 1 at hq
    rw [hcoord] at hq
    norm_num [tm] at hq
  have hbO : b ∈ Oᶜ := by
    change b ∉ O
    rintro ⟨q, hq, heq⟩
    have hpq : q = (p, tp) := hf.injective heq
    have hcoord := congrArg (fun z : Y × Set.Ioo (-2 : ℝ) 2 => (z.2 : ℝ)) hpq
    change |(q.2 : ℝ)| < 1 at hq
    rw [hcoord] at hq
    norm_num [tp] at hq
  have hra : r a = a := by simpa using hreq haO
  have hrb : r b = b := by simpa using hreq hbO

  let u : unitInterval → Set.Ioo (-2 : ℝ) 2 := fun t =>
    ⟨2 * (t : ℝ) - 1, by
      have ht := t.property
      change 0 ≤ (t : ℝ) ∧ (t : ℝ) ≤ 1 at ht
      constructor <;> linarith⟩
  have hu : Continuous u := by
    apply Continuous.subtype_mk
    fun_prop
  have hu0 : u 0 = tm := by
    apply Subtype.ext
    simp [u, tm]
  have hu1 : u 1 = tp := by
    apply Subtype.ext
    norm_num [u, tp]
  have hcrossCont : Continuous (fun t : unitInterval => f (p, u t)) :=
    hf.continuous.comp (continuous_prodMk.mpr ⟨continuous_const, hu⟩)
  let crossing : Path a b :=
    { toContinuousMap := ⟨fun t => f (p, u t), hcrossCont⟩
      source' := by change f (p, u 0) = f (p, tm); rw [hu0]
      target' := by change f (p, u 1) = f (p, tp); rw [hu1] }
  have hcross : ∀ t : unitInterval,
      c (crossing t) = ((t : ℝ) : AddCircle (1 : ℝ)) := by
    intro t
    have ht : |(u t : ℝ)| ≤ 1 := by
      rw [abs_le]
      constructor
      · dsimp [u]
        have h := t.property
        change 0 ≤ (t : ℝ) ∧ (t : ℝ) ≤ 1 at h
        linarith
      · dsimp [u]
        have h := t.property
        change 0 ≤ (t : ℝ) ∧ (t : ℝ) ≤ 1 at h
        linarith
    have h := hcCollar p (u t) ht
    have hphase : (((((u t : Set.Ioo (-2 : ℝ) 2) : ℝ) + 1) / 2) : ℝ) = (t : ℝ) := by
      dsimp [u]
      ring
    simpa [crossing, hphase] using h

  have hmap : JoinedIn (r '' Sᶜ) (r a) (r b) := hjoin.map_continuousOn hrcont
  have hbackJoin : JoinedIn (r '' Sᶜ) b a := by
    simpa [hra, hrb] using hmap.symm
  let back : Path b a := hbackJoin.somePath
  have hRO : r '' Sᶜ ⊆ Oᶜ := by
    rintro x ⟨y, hy, rfl⟩
    exact hrmap hy
  have hback : ∀ t : unitInterval, c (back t) = 0 := by
    intro t
    apply hcO
    exact hRO (hbackJoin.somePath_mem t)

  have hnot : ¬ SimplyConnectedSpace M :=
    CircleLiftObstruction.not_simplyConnected_of_circle_crossing
      c hc crossing back hcross hback
  exact hnot ‹SimplyConnectedSpace M›
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.OpenCollarSideSeparation
