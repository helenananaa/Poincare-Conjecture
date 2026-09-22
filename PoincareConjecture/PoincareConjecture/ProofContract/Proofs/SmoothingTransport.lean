import PoincareConjecture.ProofContract.V1.Obligations
import PoincareConjecture.ProofContract.Proofs.CoordinateBallExists
import PoincareConjecture.ProofContract.Proofs.OpenAnnulus
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- A smooth atlas may be pulled back through an actual homeomorphism. -/
theorem smoothing_transport_homeomorph {M N : ClosedThreeManifold.{u}}
    (e : M ≃ₜ N) (hN : Nonempty (Smoothing N)) : Nonempty (Smoothing M) :=
/- SWARM_PROOF_BEGIN -/
by
  rcases hN with ⟨sN⟩
  letI : ChartedSpace Euclidean3 N := sN.atlas
  letI : IsManifold (𝓡 3) ∞ N := sN.smooth
  have transported_transition :
      ∀ (z z' : N) (a b : OpenPartialHomeomorph N Euclidean3),
        a ∈ atlas Euclidean3 N → b ∈ atlas Euclidean3 N →
        let hf : IsLocalHomeomorph (e.symm : N → M) := e.symm.isLocalHomeomorph
        let l := hf.localInverseAt z
        let l' := hf.localInverseAt z'
        (l.trans a).symm.trans (l'.trans b) ∈
          contDiffGroupoid ∞ (𝓡 3) := by
    intro z z' a b ha hb
    let hf : IsLocalHomeomorph (e.symm : N → M) := e.symm.isLocalHomeomorph
    let l := hf.localInverseAt z
    let l' := hf.localInverseAt z'
    let E := e.toOpenPartialHomeomorph
    let S := l.source
    let S' := l'.source
    let D := E.trans a
    let D' := E.trans b
    let U := D.source ∩ S
    let U' := D'.source ∩ S'
    have hl : l ≈ E.restr S := by
      exact (show l ≈ E.restr l.source from by
        have hfun : (l.symm : N → M) = (e.symm : N → M) :=
          hf.localInverseAt_symm _
        constructor
        · rw [OpenPartialHomeomorph.restr_source,
            Homeomorph.toOpenPartialHomeomorph_source, univ_inter,
            l.open_source.interior_eq]
        · intro y hy
          change l y = e y
          apply e.symm.injective
          calc
            e.symm (l y) = l.symm (l y) := by rw [hfun]
            _ = y := l.left_inv hy
            _ = e.symm (e y) := by simp)
    have hl' : l' ≈ E.restr S' := by
      exact (show l' ≈ E.restr l'.source from by
        have hfun : (l'.symm : N → M) = (e.symm : N → M) :=
          hf.localInverseAt_symm _
        constructor
        · rw [OpenPartialHomeomorph.restr_source,
            Homeomorph.toOpenPartialHomeomorph_source, univ_inter,
            l'.open_source.interior_eq]
        · intro y hy
          change l' y = e y
          apply e.symm.injective
          calc
            e.symm (l' y) = l'.symm (l' y) := by rw [hfun]
            _ = y := l'.left_inv hy
            _ = e.symm (e y) := by simp)
    have hD : D.symm.trans D' ∈ contDiffGroupoid ∞ (𝓡 3) := by
      have hab := (contDiffGroupoid ∞ (𝓡 3)).compatible ha hb
      have hee : E.symm.trans E = OpenPartialHomeomorph.refl N := by
        ext y <;> simp [E]
      change (E.trans a).symm.trans (E.trans b) ∈ _
      rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
      rw [← OpenPartialHomeomorph.trans_assoc]
      rw [OpenPartialHomeomorph.trans_assoc a.symm E.symm E]
      rw [hee, OpenPartialHomeomorph.trans_refl]
      exact hab
    have hA0 : l.trans a ≈ D.restr S := by
      calc
        l.trans a ≈ (E.restr S).trans a :=
          OpenPartialHomeomorph.EqOnSource.trans' hl
            (OpenPartialHomeomorph.eqOnSource_refl a)
        _ = D.restr S := by rw [show D = E.trans a from rfl,
          OpenPartialHomeomorph.restr_trans]
    have hB0 : l'.trans b ≈ D'.restr S' := by
      calc
        l'.trans b ≈ (E.restr S').trans b :=
          OpenPartialHomeomorph.EqOnSource.trans' hl'
            (OpenPartialHomeomorph.eqOnSource_refl b)
        _ = D'.restr S' := by rw [show D' = E.trans b from rfl,
          OpenPartialHomeomorph.restr_trans]
    have hA : l.trans a ≈ D.restr U :=
      Setoid.trans hA0 (Setoid.symm (D.restr_inter_source (s := S)))
    have hB : l'.trans b ≈ D'.restr U' :=
      Setoid.trans hB0 (Setoid.symm (D'.restr_inter_source (s := S')))
    let A := (l.trans a).symm.trans (l'.trans b)
    have hAB : A ≈ (D.restr U).symm.trans (D'.restr U') :=
      OpenPartialHomeomorph.EqOnSource.trans'
        (OpenPartialHomeomorph.EqOnSource.symm' hA) hB
    let T := D.target ∩ D.symm ⁻¹' U'
    have hS : IsOpen S := l.open_source
    have hS' : IsOpen S' := l'.open_source
    have hU : IsOpen U := (show IsOpen D.source from D.open_source).inter hS
    have hU' : IsOpen U' := (show IsOpen D'.source from D'.open_source).inter hS'
    have hDS : IsOpen (D '' U) := D.isOpen_image_of_subset_source hU inter_subset_left
    have hT : IsOpen T := by
      rw [show T = D.target ∩ D.symm ⁻¹' U' from rfl,
        ← OpenPartialHomeomorph.image_source_inter_eq']
      exact D.isOpen_image_source_inter hU'
    have hR : (D.restr U).symm.trans (D'.restr U') ≈
        ((D.symm.trans D').restr T).restr (D '' U) := by
      exact Setoid.trans
        (D.restr_symm_trans hU hDS inter_subset_left)
        ((OpenPartialHomeomorph.EqOnSource.restr
          (D'.symm_trans_restr D hU') (D '' U)))
    have hmem : ((D.symm.trans D').restr T).restr (D '' U) ∈
        contDiffGroupoid ∞ (𝓡 3) := by
      exact closedUnderRestriction' (closedUnderRestriction' hD hT) hDS
    exact (contDiffGroupoid ∞ (𝓡 3)).mem_of_eqOnSource hmem (Setoid.trans hAB hR)
  let csM : ChartedSpace Euclidean3 M := e.symm.chartedSpace
  letI : ChartedSpace Euclidean3 M := csM
  have hM : @IsManifold ℝ _ Euclidean3 _ _ Euclidean3 _ (𝓡 3) ∞ M _ csM := by
    refine { compatible := ?_ }
    rintro c c' hc hc'
    rcases hc with ⟨q, rfl⟩
    rcases hc' with ⟨q', rfl⟩
    exact transported_transition _ _ _ _
      (chart_mem_atlas Euclidean3 _) (chart_mem_atlas Euclidean3 _)
  exact ⟨⟨csM, hM⟩⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
