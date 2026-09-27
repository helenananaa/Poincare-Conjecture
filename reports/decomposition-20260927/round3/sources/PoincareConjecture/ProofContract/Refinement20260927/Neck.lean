import PoincareConjecture.ProofContract.Refinement20260927.ClosedCut
import PoincareConjecture.ParallelImplementation.ClosedSphereCutData
import PoincareConjecture.ParallelImplementation.ClosedSideHalfCollar
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open Set V1 ParallelImplementation.ClosedSphereCutData
/-- Interior atlas on the original open side, with the boundary removed exactly. -/
def SideInteriorAtlasStatement : Prop :=
  ∀ (M : ClosedThreeManifold.{u}) (U : Set M), IsOpen U →
    ∀ b : Sphere2 → closure U,
    (∀ x : closure U, x ∈ Set.range b ↔ x.val ∈ frontier U) →
    Nonempty (ChartedSpace Euclidean3 {x : closure U // x ∉ Set.range b})
/-- The negative side of the SAME collar, with its original central marking. -/
def NegativeHalfCollarStatement : Prop :=
  ∀ (M : ClosedThreeManifold.{u}), SimplyConnectedSpace M →
    ∀ (f : Sphere2 × Icc (-1 : ℝ) 1 → M), Topology.IsEmbedding f → ∀ p : Sphere2,
    let V := connectedComponentIn (embeddedSphereCutSlice f)ᶜ
      (embeddedSphereCutNegativeSeed f p)
    ∃ b : Sphere2 → closure V, ∃ k : Sphere2 × Ico (0 : ℝ) 1 → closure V,
      Topology.IsEmbedding b ∧ Topology.IsOpenEmbedding k ∧
      (∀ s : Sphere2, (b s).val = f (s, ⟨0, by norm_num⟩)) ∧
      (∀ (s : Sphere2) (t : Ico (0 : ℝ) 1),
        (k (s,t)).val = f (s, ⟨-(t : ℝ) / 2, by constructor <;> linarith [t.2.1,t.2.2]⟩)) ∧
      (∀ s : Sphere2, k (s, ⟨0, by norm_num⟩) = b s)
/-- Two actual component closures cover the original space and meet only at the slice. -/
theorem closure_cut_incidence {X : Type u} [TopologicalSpace X]
    {U V S : Set X} (hdisj : Disjoint U V) (hcover : U ∪ V = Sᶜ)
    (hU : frontier U = S) (hV : frontier V = S) :
    closure U ∪ closure V = univ ∧ closure U ∩ closure V = S := by
  classical
  have hcU : closure U = U ∪ S := (closure_eq_self_union_frontier U).trans (by rw [hU])
  have hcV : closure V = V ∪ S := (closure_eq_self_union_frontier V).trans (by rw [hV])
  constructor
  · rw [hcU, hcV]
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ S
    · exact Or.inl (Or.inr hx)
    · have hxUV : x ∈ U ∪ V := by rw [hcover]; exact hx
      rcases hxUV with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
  · rw [hcU, hcV]
    ext x
    constructor
    · rintro ⟨hxU | hxS, hxV | hxS'⟩
      · exact False.elim ((Set.disjoint_left.mp hdisj) hxU hxV)
      · exact hxS'
      · exact hxS
      · exact hxS
    · intro hx
      exact ⟨Or.inr hx, Or.inr hx⟩
/-- Construct both regular sides of the actual neck; no closed-cut certificate is assumed. -/
def closedCut_of_neck (atlas : SideInteriorAtlasStatement.{u})
    (negative : NegativeHalfCollarStatement.{u})
    {M : ClosedThreeManifold.{u}} (hsc : SimplyConnectedSpace M)
    (f : Sphere2 × Icc (-1 : ℝ) 1 → M) (hf : Topology.IsEmbedding f) (p : Sphere2) :
    RegularClosedCut M := by
  apply Classical.choice
  let S := embeddedSphereCutSlice f
  let U := connectedComponentIn Sᶜ (embeddedSphereCutPositiveSeed f p)
  let V := connectedComponentIn Sᶜ (embeddedSphereCutNegativeSeed f p)
  have data := closed_embedded_sphere_cut_sides hsc f hf p
  change IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ _ at data
  rcases data with ⟨hUo,hVo,hUc,hVc,_,_,hdisj,hcover,hUf,hVf,_,_,_⟩
  obtain ⟨bU,kU,hbU,hkU,hbUf,_,hkUz⟩ :=
    ParallelImplementation.ClosedSideHalfCollar.exists_actual_closed_side_half_collar hsc f hf p
  obtain ⟨bV,kV,hbV,hkV,hbVf,_,hkVz⟩ := negative M hsc f hf p
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
    interiorCharts := Classical.choice (atlas M U hUo bU hrangeU) }
  let right : RegularSide M (closure V) := {
    closed := isClosed_closure
    connected := isConnected_iff_connectedSpace.mp hVc.closure
    boundaryMap := bV
    boundaryEmbedding := hbV
    collar := kV
    collarEmbedding := hkV
    collarZero := hkVz
    interiorCharts := Classical.choice (atlas M V hVo bV hrangeV) }
  obtain ⟨covers,inter⟩ := closure_cut_incidence hdisj hcover hUf hVf
  refine ⟨{
    U := closure U
    V := closure V
    left := left
    right := right
    covers := covers
    boundaryAgrees := ?_
    intersection := ?_ }⟩
  · intro s
    exact (hbUf s).trans (hbVf s).symm
  · intro x
    rw [inter]
    change (∃ s, f (s, ⟨0, by norm_num⟩) = x) ↔ ∃ s, (bU s).val = x
    simp_rw [hbUf]
#print axioms closure_cut_incidence
#print axioms closedCut_of_neck
end PoincareConjecture.ProofContract.Refinement20260927
