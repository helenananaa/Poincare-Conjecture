import PoincareConjecture.Topology.FiberSaturation.BundleCut

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.CircleBundle
open Set Bundle Function

/-- Equality transport preserves the given fiber topology. -/
def fiberTransport {B : Type*} (E : B → Type*) [∀ z, TopologicalSpace (E z)]
    {b c : B} (h : b = c) : E b ≃ₜ E c := by
  subst c
  exact Homeomorph.refl _

theorem fiberTransport_mk {B F : Type*} (E : B → Type*)
    [∀ z, TopologicalSpace (E z)] {b c : B} (h : b = c) (x : E b) :
    TotalSpace.mk' F c (fiberTransport E h x) = TotalSpace.mk b x := by
  subst c
  rfl

variable (F : Type*) [TopologicalSpace F] {L : ℝ}
  (E : AddCircle L → Type*) [∀ z, TopologicalSpace (E z)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [∀ z, Nonempty (E z)]

theorem cutMap_eq_fiberChart (x : F) (t : Icc (0 : ℝ) L) :
    cutMap F E (x,t) = TotalSpace.mk ((t : ℝ) : AddCircle L) ((cutFiberChart F E t).symm x) := by
  rw [cutFiberChart_symm]
  rfl

/-- At every cut height the entire original fiber is parametrized. -/
theorem cutMap_range_fiber (t : Icc (0 : ℝ) L) :
    range (fun x : F => cutMap F E (x,t)) =
      (TotalSpace.proj : TotalSpace F E → AddCircle L) ⁻¹' {((t : ℝ) : AddCircle L)} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rfl
  · rcases z with ⟨b,y⟩
    intro hz
    change b = ((t : ℝ) : AddCircle L) at hz
    subst b
    refine ⟨cutFiberChart F E t y, ?_⟩
    dsimp only
    rw [cutMap_eq_fiberChart, (cutFiberChart F E t).symm_apply_apply]

/-- Every point of the original bundle has a representative in one closed turn. -/
theorem surjective_cutMap (hL : 0 < L) : Surjective (cutMap F E) := by
  letI : Fact (0 < L) := ⟨hL⟩
  intro z
  let r := AddCircle.equivIco L 0 z.proj
  let t : Icc (0 : ℝ) L := ⟨r, r.2.1, by simpa using r.2.2.le⟩
  have ht : ((t : ℝ) : AddCircle L) = z.proj := AddCircle.coe_equivIco
  have hz : z ∈ range (fun x : F => cutMap F E (x,t)) := by
    rw [cutMap_range_fiber]
    exact ht.symm
  obtain ⟨x,hx⟩ := hz
  exact ⟨(x,t),hx⟩

/-- The endpoint gluing map is constructed from the two endpoint fiber charts.
It depends on the chosen cut trivialization and is not claimed canonical. -/
def monodromy (hL : 0 < L) : F ≃ₜ F :=
  ((cutFiberChart F E ⟨L, hL.le, le_rfl⟩).symm.trans
    (fiberTransport E (show (L : AddCircle L) = ((0 : ℝ) : AddCircle L) by
      simp [AddCircle.coe_period]))).trans
        (cutFiberChart F E ⟨0, le_rfl, hL.le⟩)

/-- Exactly the standard top-to-bottom gluing convention. -/
theorem cutMap_endpoints (hL : 0 < L) (x : F) :
    cutMap F E (x, ⟨L, hL.le, le_rfl⟩) =
      cutMap F E (monodromy F E hL x, ⟨0, le_rfl, hL.le⟩) := by
  rw [cutMap_eq_fiberChart, cutMap_eq_fiberChart]
  simp only [monodromy, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
  exact (fiberTransport_mk E _ _).symm

/-- Once the cut parametrization is fixed, its endpoint twist is forced. -/
theorem monodromy_unique (hL : 0 < L) (ψ : F ≃ₜ F)
    (hψ : ∀ x, cutMap F E (x, ⟨L,hL.le,le_rfl⟩) =
      cutMap F E (ψ x, ⟨0,le_rfl,hL.le⟩)) : ψ = monodromy F E hL := by
  apply Homeomorph.ext
  intro x
  apply cutMap_fiber_injective F E ⟨0,le_rfl,hL.le⟩
  exact (hψ x).symm.trans (cutMap_endpoints F E hL x)

end PoincareConjecture.Topology.FiberSaturation.CircleBundle
