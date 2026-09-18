import PoincareConjecture.Topology.FiberSaturation.CoverPullbackTopology
import PoincareConjecture.Topology.FiberSaturation.SmoothLocalLift

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.CoverPullback
open Set
open scoped Manifold ContDiff
variable {N : Type*} [TopologicalSpace N] {L : ℝ} (p : N → AddCircle L)

/-- The canonical real pullback over the circle, as an actual fiber product. -/
abbrev CircleSpace := Space ((↑) : ℝ → AddCircle L) p

/-- The natural period translation changes the real lift but not the original point. -/
def circleDeck : CircleSpace p ≃ₜ CircleSpace p where
  toFun z := ⟨(z.1.1+L,z.1.2), by simpa only [AddCircle.coe_add_period] using z.2⟩
  invFun z := ⟨(z.1.1-L,z.1.2), by
    simpa only [AddCircle.coe_sub, AddCircle.coe_period, sub_zero] using z.2⟩
  left_inv z := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp
  continuous_toFun := by
    have h : Continuous (fun z : CircleSpace p => (z.1.1+L,z.1.2)) := by fun_prop
    exact h.subtype_mk _
  continuous_invFun := by
    have h : Continuous (fun z : CircleSpace p => (z.1.1-L,z.1.2)) := by fun_prop
    exact h.subtype_mk _

@[simp] theorem circleDeck_forget (z : CircleSpace p) : forget (circleDeck p z) = forget z := rfl
@[simp] theorem circleDeck_height (z : CircleSpace p) : height (circleDeck p z) = height z+L := rfl

variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] [ChartedSpace H N]

/-- The charted structure lifted only from the original total space. -/
@[implicit_reducible] def circleChartedSpace (hp : Continuous p) : ChartedSpace H (CircleSpace p) :=
  CoverLift.chartedSpace (H := H) (forget_isLocalHomeomorph (AddCircle.isLocalHomeomorph_coe L) hp)

variable (I : ModelWithCorners ℝ V H) [IsManifold I ∞ N]

theorem circle_isManifold (hp : Continuous p) :
    letI := circleChartedSpace (H := H) p hp; IsManifold I ∞ (CircleSpace p) :=
  CoverLift.isManifold I (forget_isLocalHomeomorph (AddCircle.isLocalHomeomorph_coe L) hp)

theorem circle_forget_isLocalDiffeomorph (hp : Continuous p) :
    letI := circleChartedSpace (H := H) p hp;
    IsLocalDiffeomorph I I ∞ (forget : CircleSpace p → N) :=
  CoverLift.isLocalDiffeomorph I (forget_isLocalHomeomorph (AddCircle.isLocalHomeomorph_coe L) hp)

/-- Smoothness of the natural deck map follows from its projection identity,
not from an additional smooth-deck premise. -/
def circleDeckDiffeomorph (hp : Continuous p) :
    letI := circleChartedSpace (H := H) p hp;
    (CircleSpace p) ≃ₘ⟮I,I⟯ (CircleSpace p) := by
  letI := circleChartedSpace (H := H) p hp
  exact deckDiffeomorph (circle_forget_isLocalDiffeomorph p I hp) (circleDeck p)
    (fun z => circleDeck_forget p z)

end PoincareConjecture.Topology.FiberSaturation.CoverPullback
