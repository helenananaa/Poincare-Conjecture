import PoincareConjecture.ProofContract.Refinement20260927.CutChoiceAudit
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set ParallelImplementation.ClosedSphereCutData
abbrev positiveCutComponent {M : ClosedThreeManifold.{u}}
    (f : Sphere2 × Icc (-1 : ℝ) 1 → M) (p : Sphere2) :=
  connectedComponentIn (embeddedSphereCutSlice f)ᶜ (embeddedSphereCutPositiveSeed f p)
abbrev negativeCutComponent {M : ClosedThreeManifold.{u}}
    (f : Sphere2 × Icc (-1 : ℝ) 1 → M) (p : Sphere2) :=
  connectedComponentIn (embeddedSphereCutSlice f)ᶜ (embeddedSphereCutNegativeSeed f p)
/-- **Math.** Unlike bare Nonempty choice, this type retains the original collar
in its specification. Every chosen value certifies the actual subsets and markings. -/
structure LocatedClosedCut {M : ClosedThreeManifold.{u}}
    (f : Sphere2 × Icc (-1 : ℝ) 1 → M) (p : Sphere2) where
  cut : RegularClosedCut M
  left_eq : cut.U = closure (positiveCutComponent f p)
  right_eq : cut.V = closure (negativeCutComponent f p)
  left_boundary : ∀ s, (cut.left.boundaryMap s).val = f (s, ⟨0, by norm_num⟩)
  right_boundary : ∀ s, (cut.right.boundaryMap s).val = f (s, ⟨0, by norm_num⟩)
  left_collar : ∀ (s : Sphere2) (t : Ico (0 : ℝ) 1),
    (cut.left.collar (s,t)).val = f (s, ⟨(t : ℝ)/2, by constructor <;> linarith [t.2.1,t.2.2]⟩)
  right_collar : ∀ (s : Sphere2) (t : Ico (0 : ℝ) 1),
    (cut.right.collar (s,t)).val = f (s, ⟨-(t : ℝ)/2, by constructor <;> linarith [t.2.1,t.2.2]⟩)
/-- **Math.** Construct all location certificates together; the choice's TYPE
now depends on the supplied collar. Existing geometric separation is reused. -/
def locatedNeckCut {M : ClosedThreeManifold.{u}} (hsc : SimplyConnectedSpace M)
    (f : Sphere2 × Icc (-1 : ℝ) 1 → M) (hf : Topology.IsEmbedding f) (p : Sphere2) :
    LocatedClosedCut f p := by
  apply Classical.choice
  let S := embeddedSphereCutSlice f
  let U := connectedComponentIn Sᶜ (embeddedSphereCutPositiveSeed f p)
  let V := connectedComponentIn Sᶜ (embeddedSphereCutNegativeSeed f p)
  have data := closed_embedded_sphere_cut_sides hsc f hf p
  change IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ _ at data
  rcases data with ⟨hUo,hVo,hUc,hVc,_,_,hdisj,hcover,hUf,hVf,_,_,_⟩
  obtain ⟨bU,kU,hbU,hkU,hbUf,hkUparam,hkUz⟩ :=
    ParallelImplementation.ClosedSideHalfCollar.exists_actual_closed_side_half_collar hsc f hf p
  obtain ⟨bV,kV,hbV,hkV,hbVf,hkVparam,hkVz⟩ := checked_negative_collar M hsc f hf p
  have hrangeU : ∀ x : closure U, x ∈ Set.range bU ↔ x.val ∈ frontier U := by
    intro x
    rw [hUf]
    constructor
    · rintro ⟨s,rfl⟩
      exact ⟨s,(hbUf s).symm⟩
    · rintro ⟨s,hs⟩
      exact ⟨s,Subtype.ext ((hbUf s).trans hs)⟩
  have hrangeV : ∀ x : closure V, x ∈ Set.range bV ↔ x.val ∈ frontier V := by
    intro x
    rw [hVf]
    constructor
    · rintro ⟨s,rfl⟩
      exact ⟨s,(hbVf s).symm⟩
    · rintro ⟨s,hs⟩
      exact ⟨s,Subtype.ext ((hbVf s).trans hs)⟩
  let left : RegularSide M (closure U) := {
    closed := isClosed_closure
    connected := isConnected_iff_connectedSpace.mp hUc.closure
    boundaryMap := bU
    boundaryEmbedding := hbU
    collar := kU
    collarEmbedding := hkU
    collarZero := hkUz
    interiorCharts := Classical.choice (checked_side_atlas M U hUo bU hrangeU) }
  let right : RegularSide M (closure V) := {
    closed := isClosed_closure
    connected := isConnected_iff_connectedSpace.mp hVc.closure
    boundaryMap := bV
    boundaryEmbedding := hbV
    collar := kV
    collarEmbedding := hkV
    collarZero := hkVz
    interiorCharts := Classical.choice (checked_side_atlas M V hVo bV hrangeV) }
  obtain ⟨covers,inter⟩ := closure_cut_incidence hdisj hcover hUf hVf
  let c : RegularClosedCut M := {
    U := closure U
    V := closure V
    left := left
    right := right
    covers := covers
    boundaryAgrees := fun s => (hbUf s).trans (hbVf s).symm
    intersection := by
      intro x
      rw [inter]
      change (∃ s, f (s, ⟨0, by norm_num⟩) = x) ↔ ∃ s, (bU s).val = x
      simp_rw [hbUf] }
  exact ⟨{ cut := c
           left_eq := rfl
           right_eq := rfl
           left_boundary := hbUf
           right_boundary := hbVf
           left_collar := hkUparam
           right_collar := hkVparam }⟩
theorem locatedCut_connectedSum {M : ClosedThreeManifold.{u}}
    {f : Sphere2 × Icc (-1 : ℝ) 1 → M} {p : Sphere2} (c : LocatedClosedCut f p) :
    Nonempty (ConnectedSumPresentation
      (cappedManifold checked_cap_chart checked_interior_open c.cut.left.regularPiece)
      (cappedManifold checked_cap_chart checked_interior_open c.cut.right.regularPiece) M) :=
  checked_closedCut_connectedSum c.cut
#print axioms locatedNeckCut
#print axioms locatedCut_connectedSum
end PoincareConjecture.ProofContract.Refinement20260927
