import PoincareConjecture.ParallelImplementation.ClosedSphereCutData
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ClosedCutReconstruction
open Set PoincareConjecture.ProofContract.V1
open PoincareConjecture.ParallelImplementation.ClosedSphereCutData
open scoped Topology
abbrev PositiveSide {M : ClosedThreeManifold}
    (f : Sphere2 × Icc (-1 : ℝ) 1 → M) (p : Sphere2) :=
  closure (connectedComponentIn (embeddedSphereCutSlice f)ᶜ
    (embeddedSphereCutPositiveSeed f p))
abbrev NegativeSide {M : ClosedThreeManifold}
    (f : Sphere2 × Icc (-1 : ℝ) 1 → M) (p : Sphere2) :=
  closure (connectedComponentIn (embeddedSphereCutSlice f)ᶜ
    (embeddedSphereCutNegativeSeed f p))
def cutSeam {M : ClosedThreeManifold}
    (f : Sphere2 × Icc (-1 : ℝ) 1 → M) (p : Sphere2)
    (x y : PositiveSide f p ⊕ NegativeSide f p) : Prop :=
  match x,y with
  | .inl a,.inr b => ∃ s : Sphere2,
      a.val = f (s, ⟨0, by norm_num⟩) ∧ b.val = f (s, ⟨0, by norm_num⟩)
  | _,_ => False
/-- Gluing the TWO ACTUAL closed sides only on their shared sphere recovers
M, with the quotient map identified pointwise with the original inclusions.
This is not yet the capped-coordinate-ball connected sum presentation. -/
theorem actual_closed_cut_reconstruction
    {M : ClosedThreeManifold} (hsc : SimplyConnectedSpace M)
    (f : Sphere2 × Icc (-1 : ℝ) 1 → M) (hf : Topology.IsEmbedding f)
    (p : Sphere2) :
    ∃ e : Quot (cutSeam f p) ≃ₜ M,
      ∀ x : PositiveSide f p ⊕ NegativeSide f p,
        e (Quot.mk (cutSeam f p) x) = Sum.elim Subtype.val Subtype.val x :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let S := embeddedSphereCutSlice f
  let U := connectedComponentIn Sᶜ (embeddedSphereCutPositiveSeed f p)
  let V := connectedComponentIn Sᶜ (embeddedSphereCutNegativeSeed f p)
  let A : Set M := closure U
  let B : Set M := closure V
  have hcut := closed_embedded_sphere_cut_sides hsc f hf p
  dsimp only [S, U, V] at hcut
  rcases hcut with ⟨hUopen, hVopen, hUconn, hVconn, hUne, hVne, hdisj,
    hcover, hfrontU, hfrontV, hpos, hneg, hlocal⟩
  have hA : A = U ∪ S := by
    dsimp [A]
    rw [closure_eq_interior_union_frontier, hUopen.interior_eq, hfrontU]
  have hB : B = V ∪ S := by
    dsimp [B]
    rw [closure_eq_interior_union_frontier, hVopen.interior_eq, hfrontV]
  have hAB : A ∪ B = Set.univ := by
    ext m
    constructor
    · intro hm
      simp
    · intro _
      by_cases hs : m ∈ S
      · rw [hA, hB]
        exact Or.inl (Or.inr hs)
      · have hc : m ∈ Sᶜ := by change m ∉ S; exact hs
        have hc' : m ∈ U ∪ V := by rw [← hcover] at hc; exact hc
        rcases hc' with hu | hv
        · rw [hA, hB]
          exact Or.inl (Or.inl hu)
        · rw [hA, hB]
          exact Or.inr (Or.inl hv)
  have hABint : A ∩ B = S := by
    ext m
    constructor
    · intro hm
      have hm' : m ∈ (U ∪ S) ∩ (V ∪ S) := by simpa [hA, hB] using hm
      rcases hm' with ⟨hu | hs, hv | hs'⟩
      · exact False.elim ((Set.disjoint_left.mp hdisj) hu hv)
      · exact hs'
      · exact hs
      · exact hs
    · intro hs
      rw [hA, hB]
      exact ⟨Or.inr hs, Or.inr hs⟩
  have hAclosed : IsClosed A := isClosed_closure
  have hBclosed : IsClosed B := isClosed_closure
  letI : CompactSpace (PositiveSide f p) :=
    isCompact_iff_compactSpace.mp (hAclosed.isCompact)
  letI : CompactSpace (NegativeSide f p) :=
    isCompact_iff_compactSpace.mp (hBclosed.isCompact)
  letI : CompactSpace (PositiveSide f p ⊕ NegativeSide f p) := inferInstance
  letI : CompactSpace (Quot (cutSeam f p)) := Quot.compactSpace
  let phi : PositiveSide f p ⊕ NegativeSide f p → M :=
    Sum.elim Subtype.val Subtype.val
  have hcompat : ∀ x y, cutSeam f p x y → phi x = phi y := by
    intro x y hxy
    cases x with
    | inl a =>
      cases y with
      | inl b => cases hxy
      | inr b =>
        rcases hxy with ⟨s, ha, hb⟩
        exact ha.trans hb.symm
    | inr a => cases y <;> cases hxy
  let eFun : Quot (cutSeam f p) → M := Quot.lift phi hcompat
  have heFun : ∀ x, eFun (Quot.mk (cutSeam f p) x) = phi x := by
    intro x
    rfl
  have hcontinuous : Continuous eFun := by
    apply continuous_quot_lift hcompat
    continuity
  have hsurj : Function.Surjective eFun := by
    intro m
    have hm : m ∈ A ∪ B := by rw [hAB]; simp
    rcases hm with ha | hb
    · exact ⟨Quot.mk (cutSeam f p) (Sum.inl ⟨m, ha⟩), by simp [eFun, phi]⟩
    · exact ⟨Quot.mk (cutSeam f p) (Sum.inr ⟨m, hb⟩), by simp [eFun, phi]⟩
  have hinj : Function.Injective eFun := by
    intro q r hqr
    induction q using Quot.inductionOn with
    | _ x =>
      induction r using Quot.inductionOn with
      | _ y =>
       change eFun (Quot.mk (cutSeam f p) x) = eFun (Quot.mk (cutSeam f p) y) at hqr
       have hxy : phi x = phi y := hqr
       cases x with
    | inl a =>
      cases y with
      | inl b =>
        change a.val = b.val at hxy
        have hab : a.val = b.val := hxy
        have : a = b := Subtype.ext hab
        subst b
        rfl
      | inr b =>
        change a.val = b.val at hxy
        have hm : a.val ∈ A ∩ B := ⟨a.property, hxy ▸ b.property⟩
        have hmemS : a.val ∈ S := hABint ▸ hm
        change a.val ∈ Set.range (fun s : Sphere2 => f (s, ⟨0, by norm_num⟩)) at hmemS
        rcases hmemS with ⟨s, hs⟩
        apply Quot.sound
        exact ⟨s, hs.symm, hxy.symm.trans hs.symm⟩
    | inr a =>
      cases y with
      | inl b =>
        change a.val = b.val at hxy
        have hm : b.val ∈ A ∩ B := ⟨b.property, hxy.symm ▸ a.property⟩
        have hmemS : b.val ∈ S := hABint ▸ hm
        change b.val ∈ Set.range (fun s : Sphere2 => f (s, ⟨0, by norm_num⟩)) at hmemS
        rcases hmemS with ⟨s, hs⟩
        apply (Quot.sound ⟨s, hs.symm, hxy.trans hs.symm⟩).symm
      | inr b =>
        change a.val = b.val at hxy
        have hab : a.val = b.val := hxy
        have : a = b := Subtype.ext hab
        subst b
        rfl
  let equiv : Quot (cutSeam f p) ≃ M := Equiv.ofBijective eFun ⟨hinj, hsurj⟩
  let homeo : Quot (cutSeam f p) ≃ₜ M :=
    Continuous.homeoOfEquivCompactToT2 (f := equiv) hcontinuous
  refine ⟨homeo, ?_⟩
  intro x
  change eFun (Quot.mk (cutSeam f p) x) = phi x
  exact heFun x
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ClosedCutReconstruction
