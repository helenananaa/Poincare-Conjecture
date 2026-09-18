import PoincareConjecture.Topology.FiberSaturation.CoverLiftAtlas
import Mathlib.Topology.Covering.AddCircle

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.CoverPullback
open Set Function
open scoped Topology Classical
variable {R B N : Type*} [TopologicalSpace R] [TopologicalSpace B]
  [TopologicalSpace N]

/-- The actual fiber product, with its subspace topology in the product. -/
abbrev Space (c : R → B) (p : N → B) := {z : R × N // c z.1 = p z.2}

variable {c : R → B} {p : N → B}

def forget (z : Space c p) : N := z.1.2
def height (z : Space c p) : R := z.1.1

omit [TopologicalSpace B] in
theorem continuous_forget : Continuous (forget : Space c p → N) :=
  continuous_snd.comp continuous_subtype_val

omit [TopologicalSpace B] in
theorem continuous_height : Continuous (height : Space c p → R) :=
  continuous_fst.comp continuous_subtype_val

/-- Local inverse of the forgetful projection, using an actual sheet of c. -/
def sheet (e : OpenPartialHomeomorph R B) (he : ∀ t, e t = c t)
    (hp : Continuous p) (z0 : Space c p) : OpenPartialHomeomorph (Space c p) N where
  toFun := forget
  invFun y := if h : p y ∈ e.target then
    ⟨(e.symm (p y), y), (he _).symm.trans (e.right_inv h)⟩ else z0
  source := height ⁻¹' e.source
  target := p ⁻¹' e.target
  map_source' z hz := by
    change p z.1.2 ∈ e.target
    rw [← z.2, ← he]
    exact e.map_source hz
  map_target' y hy := by
    change p y ∈ e.target at hy
    simp only [hy, dite_true]
    exact e.map_target hy
  left_inv' z hz := by
    have hy : p z.1.2 ∈ e.target := by
      rw [← z.2, ← he]; exact e.map_source hz
    simp only [forget, hy, dite_true]
    apply Subtype.ext
    apply Prod.ext
    · change e.symm (p z.1.2) = z.1.1
      rw [← z.2, ← he]
      exact e.left_inv hz
    · rfl
  right_inv' y hy := by
    change p y ∈ e.target at hy
    simp only [hy, dite_true, forget]
  open_source := e.open_source.preimage continuous_height
  open_target := e.open_target.preimage hp
  continuousOn_toFun := continuous_forget.continuousOn
  continuousOn_invFun := by
    apply continuousOn_iff_continuous_restrict.mpr
    have hcont : Continuous (fun y : ↥(p ⁻¹' e.target) => (e.symm (p y), (y : N))) :=
      (e.continuousOn_symm.comp_continuous (hp.comp continuous_subtype_val)
        (fun y => y.2)).prodMk continuous_subtype_val
    have hsub : Continuous (fun y : ↥(p ⁻¹' e.target) =>
        (⟨(e.symm (p y), (y : N)), (he _).symm.trans (e.right_inv y.2)⟩ : Space c p)) :=
      hcont.subtype_mk _
    convert hsub using 1
    funext y
    have hy : p (y : N) ∈ e.target := y.2
    simp only [restrict, hy, dite_true]

/-- Pullback preserves local homeomorphisms; the projection p only needs continuity. -/
theorem forget_isLocalHomeomorph (hc : IsLocalHomeomorph c) (hp : Continuous p) :
    IsLocalHomeomorph (forget : Space c p → N) := by
  intro z
  obtain ⟨e, hz, he⟩ := hc z.1.1
  exact ⟨sheet e (fun t => congrFun he.symm t) hp z, hz, rfl⟩

omit [TopologicalSpace R] [TopologicalSpace B] [TopologicalSpace N] in
/-- Surjectivity of the base covering gives surjectivity of the forgetful map. -/
theorem forget_surjective (hc : Surjective c) : Surjective (forget : Space c p → N) := by
  intro y
  obtain ⟨t, ht⟩ := hc (p y)
  exact ⟨⟨(t,y),ht⟩, rfl⟩

end PoincareConjecture.Topology.FiberSaturation.CoverPullback
