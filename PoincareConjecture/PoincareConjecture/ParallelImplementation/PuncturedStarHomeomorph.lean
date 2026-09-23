import PoincareConjecture.ParallelImplementation.BarycentricLinkReconstruction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.PuncturedStarHomeomorph
open PoincareConjecture.ParallelImplementation.FinitePLRealization
open scoped BigOperators
theorem exists_punctured_star_homeomorph
    {V : Type*} [Fintype V] [DecidableEq V] (K : FiniteAbstractComplex V)
    (v : V) (hv : ({v} : Finset V) ∈ K.faces) :
    ∃ e : {x : V → ℝ // x ∈ (realization K).space ∧ 0 < x v ∧ x v < 1} ≃ₜ
      (Set.Ioo (0 : ℝ) 1 × {y : V → ℝ // (∀ w, 0 ≤ y w) ∧ (∑ w, y w) = 1 ∧
        (Finset.univ.filter (fun w => 0 < y w)) ∈ (abstractLink K {v} hv).faces}),
      ∀ x, (e x).1.1 = x.1 v ∧
        (e x).2.1 = (fun w => if w = v then 0 else x.1 w / (1 - x.1 v)) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let X := {x : V → ℝ // x ∈ (realization K).space ∧ 0 < x v ∧ x v < 1}
  let Y := {y : V → ℝ // (∀ w, 0 ≤ y w) ∧ (∑ w, y w) = 1 ∧
    (Finset.univ.filter (fun w => 0 < y w)) ∈ (abstractLink K {v} hv).faces}
  let P := Set.Ioo (0 : ℝ) 1 × Y
  let normCoord : X → V → ℝ := fun x w =>
    if w = v then 0 else x.1 w / (1 - x.1 v)
  let f : X → P := fun x =>
    (⟨x.1 v, x.2.2.1, x.2.2.2⟩,
      ⟨normCoord x, by
        have h := PoincareConjecture.ParallelImplementation.BarycentricLinkCoordinates.normalized_vertex_deletion_in_link K v hv x.1 x.2.1
          x.2.2.1 x.2.2.2
        simpa [normCoord] using h⟩)
  let g : P → X := fun p =>
    ⟨(fun w => if w = v then (p.1 : ℝ) else (1 - p.1) * p.2.1 w), by
      have h := PoincareConjecture.ParallelImplementation.BarycentricLinkReconstruction.reconstruct_from_link_coordinates K v hv p.2.1
        p.2.2.1 p.2.2.2.1 p.2.2.2.2 p.1 p.1.2.1 p.1.2.2
      refine ⟨?_, ?_, ?_⟩
      · simpa using h.1
      · simpa using p.1.2.1
      · simpa using p.1.2.2⟩
  have hdenX : ∀ x : X, 1 - x.1 v ≠ 0 := by
    intro x
    exact ne_of_gt (sub_pos.mpr x.2.2.2)
  have hnormCont : Continuous normCoord := by
    apply continuous_pi
    intro w
    by_cases hw : w = v
    · simp [normCoord, hw]
      exact continuous_const
    · simp only [normCoord, if_neg hw]
      have hxw : Continuous (fun x : X => x.1 w) :=
        (continuous_apply w).comp continuous_subtype_val
      have hxv : Continuous (fun x : X => x.1 v) :=
        (continuous_apply v).comp continuous_subtype_val
      have hden : Continuous (fun x : X => 1 - x.1 v) := continuous_const.sub hxv
      exact hxw.div hden hdenX
  have hGvalCont : Continuous
      (fun p : P => fun w : V =>
        if w = v then (p.1 : ℝ) else (1 - p.1) * p.2.1 w) := by
    apply continuous_pi
    intro w
    by_cases hw : w = v
    · simp [hw]
      exact (continuous_subtype_val.comp continuous_fst)
    · simp only [if_neg hw]
      have ht : Continuous (fun p : P => (p.1 : ℝ)) :=
        continuous_subtype_val.comp continuous_fst
      have hy : Continuous (fun p : P => p.2.1 w) :=
        (continuous_apply w).comp (continuous_subtype_val.comp continuous_snd)
      exact (continuous_const.sub ht).mul hy
  have hfCont : Continuous f := by
    dsimp [f]
    have ht : Continuous (fun x : X => x.1 v) :=
      (continuous_apply v).comp continuous_subtype_val
    exact continuous_prodMk.mpr ⟨ht.subtype_mk _, hnormCont.subtype_mk _⟩
  have hgCont : Continuous g := by
    dsimp [g]
    exact hGvalCont.subtype_mk _
  have hgf : ∀ x : X, g (f x) = x := by
    intro x
    apply Subtype.ext
    funext w
    by_cases hw : w = v
    · subst w
      simp [f, g]
    · have hden : 1 - x.1 v ≠ 0 := hdenX x
      simp only [f, g, normCoord, hw, if_false]
      field_simp [hden]
  have hfg : ∀ p : P, f (g p) = p := by
    intro p
    apply Prod.ext
    · apply Subtype.ext
      simp [f, g]
    · apply Subtype.ext
      have hrec := PoincareConjecture.ParallelImplementation.BarycentricLinkReconstruction.reconstruct_from_link_coordinates
        K v hv p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 p.1 p.1.2.1 p.1.2.2
      have hcoords : (fun w => if w = v then 0 else
          (if w = v then (p.1 : ℝ) else (1 - p.1) * p.2.1 w) /
            (1 - (if v = v then (p.1 : ℝ) else (1 - p.1) * p.2.1 v))) = p.2.1 := by
        simpa using hrec.2.2
      change normCoord (g p) = p.2.1
      simpa [normCoord, g] using hcoords
  let e : X ≃ₜ P := Homeomorph.mk ⟨f, g, hgf, hfg⟩ hfCont hgCont
  refine ⟨e, ?_⟩
  intro x
  exact ⟨rfl, rfl⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.PuncturedStarHomeomorph
