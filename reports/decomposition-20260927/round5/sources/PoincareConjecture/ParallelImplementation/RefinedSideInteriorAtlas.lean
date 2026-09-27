import PoincareConjecture.ProofContract.Refinement20260927.Neck
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedSideInteriorAtlas
open PoincareConjecture.ProofContract.Refinement20260927
theorem side_interior_atlas : SideInteriorAtlasStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  intro M U hU b hb
  by_cases hUempty : U = ∅
  · subst U
    let D := {x : closure (∅ : Set M) // x ∉ Set.range b}
    haveI : IsEmpty D := ⟨fun x => by
      have hx : (x.val : M) ∈ (∅ : Set M) := by simpa using x.val.property
      exact hx.elim⟩
    exact ⟨ChartedSpace.empty PoincareConjecture.ProofContract.V1.Euclidean3 D⟩
  · have hUne : U.Nonempty := Set.nonempty_iff_ne_empty.mpr hUempty
    obtain ⟨u, hu⟩ := hUne
    let s : TopologicalSpace.Opens M := ⟨U, hU⟩
    have hs : Nonempty s := ⟨⟨u, hu⟩⟩
    letI : ChartedSpace PoincareConjecture.ProofContract.V1.Euclidean3 s := {
      atlas := ⋃ x : s, {(chartAt PoincareConjecture.ProofContract.V1.Euclidean3 (x : M)).subtypeRestr hs}
      chartAt x := (chartAt PoincareConjecture.ProofContract.V1.Euclidean3 (x : M)).subtypeRestr hs
      mem_chart_source := by
        intro x
        simp only [OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage]
        exact mem_chart_source PoincareConjecture.ProofContract.V1.Euclidean3 (x : M)
      chart_mem_atlas := by
        intro x
        exact Set.mem_iUnion.mpr ⟨x, Set.mem_singleton _⟩
    }
    have hclosure : closure U \ frontier U = U := by
      rw [closure_sdiff_frontier, hU.interior_eq]
    have hyU (y : s) : (y : M) ∈ U := by
      exact y.property
    have hyNotFrontier (y : s) : (y : M) ∉ frontier U := by
      intro hyf
      have hyi : (y : M) ∈ interior U := by
        rw [hU.interior_eq]
        exact hyU y
      exact (Set.disjoint_left.mp (disjoint_interior_frontier (s := U))) hyi hyf
    let D := {x : closure U // x ∉ Set.range b}
    have hxU (x : D) : (x.val : M) ∈ U := by
      have hxNotFrontier : (x.val : M) ∉ frontier U := by
        intro hxfront
        exact x.property ((hb x.val).2 hxfront)
      have hxdiff : (x.val : M) ∈ closure U \ frontier U :=
        ⟨x.val.property, hxNotFrontier⟩
      rw [hclosure] at hxdiff
      exact hxdiff
    let e : D ≃ₜ s := {
      toEquiv := {
        toFun := fun x => ⟨(x.val : M), hxU x⟩
        invFun := fun y =>
          ⟨⟨(y : M), subset_closure (hyU y)⟩,
            fun hbr => hyNotFrontier y ((hb ⟨(y : M), subset_closure (hyU y)⟩).1 hbr)⟩
        left_inv := by
          intro x
          apply Subtype.ext
          apply Subtype.ext
          rfl
        right_inv := by
          intro y
          apply Subtype.ext
          rfl
      }
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp continuous_subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        · apply Continuous.subtype_mk
          exact continuous_subtype_val
    }
    exact ⟨e.symm.chartedSpace⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedSideInteriorAtlas
