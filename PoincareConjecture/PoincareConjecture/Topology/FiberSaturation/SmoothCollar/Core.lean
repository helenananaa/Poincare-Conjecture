import PoincareConjecture.Topology.FiberSaturation.DomainAtlas.ClosedDomain
import PoincareConjecture.Topology.FiberSaturation.DomainAtlas.CollaredRegularOpen
import PoincareConjecture.Topology.FiberSaturation.CollarClosureHalfSpace
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothCollar
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- A fixed half-space in the ambient product vector space, with its induced topology. -/
abbrev HalfSpace (V : Type*) := {z : V × ℝ // 0 ≤ z.2}

/-- The standard inclusion/clamping partial equivalence. Clamping is only used
for the total inverse outside the model; no smoothness of max is asserted. -/
def halfSpacePartialEquiv (V : Type*) : PartialEquiv (HalfSpace V) (V × ℝ) where
  toFun := Subtype.val
  invFun z := ⟨(z.1, max z.2 0), le_max_right _ _⟩
  source := univ
  target := {z | 0 ≤ z.2}
  map_source' z _ := z.property
  map_target' _ _ := mem_univ _
  left_inv' z _ := by apply Subtype.ext; simp [max_eq_left z.property]
  right_inv' z hz := by
    change 0 ≤ z.2 at hz
    exact Prod.ext rfl (max_eq_left hz)

/-- A concrete common half-space model with vector space V × Real.
It does not transport or replace the topology of any geometric region. -/
def halfSpaceModel (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    ModelWithCorners ℝ (V × ℝ) (HalfSpace V) :=
  ModelWithCorners.ofConvexRange (halfSpacePartialEquiv V) rfl
    (by
      change Convex ℝ {z : V × ℝ | 0 ≤ z.2}
      have h : {z : V × ℝ | 0 ≤ z.2} = (univ : Set V) ×ˢ Ici (0 : ℝ) := by ext z; simp
      rw [h]
      exact convex_univ.prod (convex_Ici 0))
    continuous_subtype_val
    (by exact (continuous_fst.prodMk (continuous_snd.max continuous_const)).subtype_mk _)
    (by
      change (interior {z : V × ℝ | 0 ≤ z.2}).Nonempty
      have h : {z : V × ℝ | 0 ≤ z.2} = (univ : Set V) ×ˢ Ici (0 : ℝ) := by ext z; simp
      rw [h, interior_prod_eq, interior_univ, interior_Ici]
      exact ⟨(0, 1), mem_univ _, by norm_num⟩)

/-- Restrict a full open collar map to the normalized open-interval subtype. -/
def collarRestriction {X N : Type*} [TopologicalSpace X] [TopologicalSpace N]
    (F : OpenPartialHomeomorph (X × ℝ) N) : X × NeckParameter → N :=
  fun z => F (z.1, (z.2 : ℝ))

/-- The concrete environmental product coordinates associated to a collar and
one genuine cross-section chart. Smoothness is proved separately. -/
def collarCoordinates {X N V : Type*} [TopologicalSpace X] [TopologicalSpace N]
    [TopologicalSpace V] (F : OpenPartialHomeomorph (X × ℝ) N)
    (a : OpenPartialHomeomorph X V) : OpenPartialHomeomorph N (V × ℝ) :=
  F.symm.trans (a.prod (Homeomorph.refl ℝ).toOpenPartialHomeomorph)

end PoincareConjecture.Topology.FiberSaturation.SmoothCollar
