import PoincareConjecture.ProofContract.V1.Obligations
import PoincareConjecture.ProofContract.Proofs.ControlledUniformLimit
import PoincareConjecture.ProofContract.Proofs.ControlledCollapseFibers
import PoincareConjecture.ProofContract.Proofs.SingleFiberQuotient
set_option autoImplicit false
noncomputable section
universe u v
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Filter Topology
open scoped Topology
/-- An actual single-fiber collapse is a homeomorphism off its collapsed compact fiber. -/
theorem collapse_complement_homeomorph {X : Type u} {Y : Type v}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
    (K : Set X) (q : X → Y) (hq : Continuous q) (hs : Surjective q) (k : X) (hk : k ∈ K)
    (hker : ∀ x y, q x=q y ↔ x=y ∨ (x∈K ∧ y∈K)) :
    ∃ e : {x : X // x∉K} ≃ₜ {y : Y // y≠q k}, ∀ x, (e x:Y)=q x :=
/- SWARM_PROOF_BEGIN -/
by
  have hK : IsClosed K := by
    have hfiber : q ⁻¹' {q k} = K := by
      ext x
      constructor
      · intro hx
        have hqx : q x = q k := hx
        rcases (hker x k).mp hqx with rfl | ⟨hxK, _⟩
        · exact hk
        · exact hxK
      · intro hxK
        exact (hker x k).mpr (Or.inr ⟨hxK, hk⟩)
    rw [← hfiber]
    exact isClosed_singleton.preimage hq
  have hfiber : q ⁻¹' {q k} = K := by
    ext x
    constructor
    · intro hx
      have hqx : q x = q k := hx
      rcases (hker x k).mp hqx with rfl | ⟨hxK, _⟩
      · exact hk
      · exact hxK
    · intro hxK
      exact (hker x k).mpr (Or.inr ⟨hxK, hk⟩)
  let f : {x : X // x ∉ K} → {y : Y // y ≠ q k} := fun x =>
    ⟨q x, by
      intro hqx
      apply x.property
      have : x.1 ∈ q ⁻¹' {q k} := hqx
      rw [hfiber] at this
      exact this⟩
  have hf_cont : Continuous f := by
    change Continuous (fun x : {x : X // x ∉ K} =>
      (⟨q x, _⟩ : {y : Y // y ≠ q k}))
    apply Continuous.subtype_mk
    exact hq.comp continuous_subtype_val
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    rcases (hker x.1 y.1).mp (congrArg Subtype.val hxy) with hxy' | ⟨hxK, _⟩
    · exact hxy'
    · exact (x.property hxK).elim
  have hf_surj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := hs y.1
    have hxK : x ∉ K := by
      intro hxK
      apply y.property
      exact hx.symm.trans ((hker x k).mpr (Or.inr ⟨hxK, hk⟩))
    refine ⟨⟨x, hxK⟩, ?_⟩
    exact Subtype.ext hx
  let e : {x : X // x ∉ K} ≃ {y : Y // y ≠ q k} :=
    Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have he_cont : Continuous e := by
    simpa [e] using hf_cont
  have he_closed : IsClosedMap e := by
    intro C hC
    obtain ⟨D, hD, hDC⟩ :=
      (Topology.IsInducing.subtypeVal.isClosed_iff).mp hC
    have hqD : IsClosed (q '' D) := hq.isClosedMap D hD
    have himage : e '' C = (Subtype.val : {y : Y // y ≠ q k} → Y) ⁻¹' (q '' D) := by
      ext y
      constructor
      · rintro ⟨x, hxC, rfl⟩
        refine ⟨x.1, ?_, ?_⟩
        · have : x.1 ∈ D := by
            have := congrArg (fun s => x ∈ s) hDC
            exact this.mpr hxC
          exact this
        · rfl
      · intro hy
        rcases hy with ⟨x, hxD, hqx⟩
        have hxK : x ∉ K := by
          intro hxK
          apply y.property
          exact hqx.symm.trans ((hker x k).mpr (Or.inr ⟨hxK, hk⟩))
        have hxC : (⟨x, hxK⟩ : {x : X // x ∉ K}) ∈ C := by
          have := congrArg (fun s => (⟨x, hxK⟩ : {x : X // x ∉ K}) ∈ s) hDC
          exact this.mp hxD
        refine ⟨⟨x, hxK⟩, hxC, ?_⟩
        apply Subtype.ext
        exact hqx
    rw [himage]
    exact hqD.preimage continuous_subtype_val
  refine ⟨e.toHomeomorphOfContinuousClosed he_cont he_closed, ?_⟩
  intro x
  change (e x : Y) = q x
  rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
