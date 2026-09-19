import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.Core
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothNeck
open Set Function Manifold
open scoped Manifold ContDiff Topology

variable {V W G X N : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [TopologicalSpace G]
  [TopologicalSpace X] [TopologicalSpace N] [ChartedSpace V X] [ChartedSpace G N]
  {J : ModelWithCorners ℝ W G}

/-- A diffeomorphism between two actual open subspaces produces an ambient
partial diffeomorphism with the exact source, target and map. -/
theorem exists_partialDiffeomorph_of_open_subspaces
    (U : TopologicalSpace.Opens (X × ℝ)) (Q : TopologicalSpace.Opens N)
    [Nonempty U]
    (φ : Diffeomorph ((𝓘(ℝ,V)).prod (𝓘(ℝ,ℝ))) J U Q ∞) :
    ∃ Ψ : PartialDiffeomorph ((𝓘(ℝ,V)).prod (𝓘(ℝ,ℝ))) J (X × ℝ) N ∞,
      Ψ.source = (U : Set (X × ℝ)) ∧ Ψ.target = (Q : Set N) ∧
      (∀ z : U, Ψ z = (φ z : N)) ∧
      (∀ y : Q, Ψ.symm y = (φ.symm y : X × ℝ)) :=
/- SWARM_PROOF_BEGIN -/
by
  have hQ : Nonempty Q := Nonempty.map φ ‹Nonempty U›
  let I0 := (𝓘(ℝ, V)).prod (𝓘(ℝ, ℝ))
  let eU := U.openPartialHomeomorphSubtypeCoe ‹Nonempty U›
  let eQ := Q.openPartialHomeomorphSubtypeCoe hQ
  let ΨU : PartialDiffeomorph I0 I0 U (X × ℝ) ∞ :=
    { toPartialEquiv := eU.toPartialEquiv
      open_source := eU.open_source
      open_target := eU.open_target
      contMDiffOn_toFun := by
        change ContMDiffOn I0 I0 ∞ (Subtype.val : U → X × ℝ) eU.source
        exact (contMDiff_subtype_val (I := I0) (U := U)).contMDiffOn
      contMDiffOn_invFun := by
        intro x hx
        rw [← ContMDiffWithinAt.subtypeVal_comp_iff (U := U)]
        refine ContMDiffWithinAt.congr (f := id) contMDiffWithinAt_id ?_ ?_
        · intro y hy
          exact eU.right_inv hy
        · exact eU.right_inv hx }
  let ΨQ : PartialDiffeomorph J J Q N ∞ :=
    { toPartialEquiv := eQ.toPartialEquiv
      open_source := eQ.open_source
      open_target := eQ.open_target
      contMDiffOn_toFun := by
        change ContMDiffOn J J ∞ (Subtype.val : Q → N) eQ.source
        exact (contMDiff_subtype_val (I := J) (U := Q)).contMDiffOn
      contMDiffOn_invFun := by
        intro y hy
        rw [← ContMDiffWithinAt.subtypeVal_comp_iff (U := Q)]
        refine ContMDiffWithinAt.congr (f := id) contMDiffWithinAt_id ?_ ?_
        · intro z hz
          exact eQ.right_inv hz
        · exact eQ.right_inv hy }
  let Ψ := (ΨU.symm.trans φ.toPartialDiffeomorph).trans ΨQ
  have hΨUsource : ΨU.source = (univ : Set U) :=
    U.openPartialHomeomorphSubtypeCoe_source ‹Nonempty U›
  have hΨUtarget : ΨU.target = (U : Set (X × ℝ)) :=
    U.openPartialHomeomorphSubtypeCoe_target ‹Nonempty U›
  have hΨQsource : ΨQ.source = (univ : Set Q) :=
    Q.openPartialHomeomorphSubtypeCoe_source hQ
  have hΨQtarget : ΨQ.target = (Q : Set N) :=
    Q.openPartialHomeomorphSubtypeCoe_target hQ
  refine ⟨Ψ, ?source, ?target, ?apply, ?symm⟩
  · change Ψ.source = (U : Set (X × ℝ))
    simp only [Ψ, PartialDiffeomorph.trans_toPartialEquiv,
      OpenPartialHomeomorph.trans_toPartialEquiv, PartialEquiv.trans_source,
      PartialDiffeomorph.symm_toPartialEquiv, PartialEquiv.symm_source,
      PartialDiffeomorph.toOpenPartialHomeomorph_toPartialHomeomorph_toPartialEquiv,
      Diffeomorph.toPartialDiffeomorph, Equiv.toPartialEquiv_source]
    rw [hΨUtarget, hΨQsource]
    simp
  · change Ψ.target = (Q : Set N)
    simp only [Ψ, PartialDiffeomorph.trans_toPartialEquiv,
      OpenPartialHomeomorph.trans_toPartialEquiv, PartialEquiv.trans_target,
      PartialDiffeomorph.symm_toPartialEquiv, PartialEquiv.symm_target,
      PartialDiffeomorph.toOpenPartialHomeomorph_toPartialHomeomorph_toPartialEquiv,
      Diffeomorph.toPartialDiffeomorph, Equiv.toPartialEquiv_target]
    rw [hΨQtarget, hΨUsource]
    simp
  · intro z
    have hleft : eU.symm (z : X × ℝ) = z := eU.left_inv (mem_univ _)
    calc Ψ (z : X × ℝ)
        = ΨQ (φ.toPartialDiffeomorph (ΨU.symm (z : X × ℝ))) := rfl
      _ = ΨQ (φ.toPartialDiffeomorph (eU.symm (z : X × ℝ))) := rfl
      _ = ΨQ (φ.toPartialDiffeomorph z) := by rw [hleft]
      _ = ΨQ (φ z) := rfl
      _ = (φ z : N) := rfl
  · intro y
    have hleft : eQ.symm (y : N) = y := eQ.left_inv (mem_univ _)
    calc Ψ.symm (y : N)
        = ΨU (φ.toPartialDiffeomorph.symm (ΨQ.symm (y : N))) := rfl
      _ = ΨU (φ.symm (eQ.symm (y : N))) := rfl
      _ = ΨU (φ.symm y) := by rw [hleft]
      _ = (φ.symm y : X × ℝ) := rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.SmoothNeck
