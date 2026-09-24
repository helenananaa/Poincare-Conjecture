import PoincareConjecture.ParallelImplementation.VertexStarBallChart
import PoincareConjecture.ParallelImplementation.BarycentricOpenCover
import Mathlib.Geometry.Manifold.ChartedSpace
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.RealizationOpenStarChart
open PoincareConjecture.ParallelImplementation.FinitePLRealization
open scoped BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** The proved star ball homeomorphism gives an ambient open partial homeomorphism. -/
theorem exists_open_star_chart
    {V : Type*} [Fintype V] [DecidableEq V] (K : FiniteAbstractComplex V)
    (v : V) (hv : ({v} : Finset V) ∈ K.faces)
    (eLink : {y : V → ℝ // (∀ w, 0 ≤ y w) ∧ (∑ w, y w) = 1 ∧
      (Finset.univ.filter (fun w => 0 < y w)) ∈ (abstractLink K {v} hv).faces} ≃ₜ
      {z : E3 // ‖z‖ = 1}) :
    ∃ e : OpenPartialHomeomorph {x : V → ℝ // x ∈ (realization K).space} E3,
      e.source = {x | 0 < x.1 v} ∧ e.target = {z | ‖z‖ < 1} :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let A := {x : V → ℝ // x ∈ (realization K).space}
  let U : Set A := {x | 0 < x.1 v}
  let X := {x : V → ℝ // x ∈ (realization K).space ∧ 0 < x v}
  let Z := {z : E3 // ‖z‖ < 1}
  letI : Nonempty Z := ⟨⟨0, by simp⟩⟩
  obtain ⟨hBall⟩ :=
    PoincareConjecture.ParallelImplementation.VertexStarBallChart.vertex_star_homeomorph_ball_of_spherical_link
      K v hv eLink
  have hOpenCover :=
    PoincareConjecture.ParallelImplementation.BarycentricOpenCover.positive_coordinate_open_cover K
  have hUopen : IsOpen U := by
    simpa [U, A] using hOpenCover.1 v
  have hZopen : IsOpen ({z : E3 | ‖z‖ < 1}) :=
    isOpen_lt continuous_norm continuous_const
  have hvReal : barycentricVertex v ∈ (realization K).space := by
    apply PoincareConjecture.ParallelImplementation.BarycentricMembership.mem_realization_iff_barycentric
      K (barycentricVertex v) |>.2
    refine ⟨?_, ?_, ?_⟩
    · intro w
      by_cases hw : w = v <;> simp [barycentricVertex, hw]
    · simp [barycentricVertex, Pi.single_apply]
    · have hs : Finset.univ.filter (fun w => 0 < barycentricVertex v w) = {v} := by
        ext w
        by_cases hw : w = v <;> simp [barycentricVertex, Pi.single_apply, hw]
      rw [hs]
      exact hv
  letI : Nonempty A := ⟨⟨barycentricVertex v, hvReal⟩⟩
  let hNest : U ≃ₜ X := {
    toEquiv := Equiv.subtypeSubtypeEquivSubtypeInter
      (fun x : V → ℝ => x ∈ (realization K).space) (fun x => 0 < x v)
    continuous_toFun := by
      change Continuous (fun u : U => (⟨u.1.1, And.intro u.1.2 u.2⟩ : X))
      exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
        (fun u : U => And.intro u.1.2 u.2)
    continuous_invFun := by
      change Continuous (fun x : X => (⟨⟨x.1, x.2.1⟩, x.2.2⟩ : U))
      exact (continuous_subtype_val.subtype_mk (fun x : X => x.2.1)).subtype_mk
        (fun x : X => x.2.2)
  }
  let h : U ≃ₜ Z := hNest.trans hBall
  let e0 : OpenPartialHomeomorph U Z := h.toOpenPartialHomeomorph
  let e1 : OpenPartialHomeomorph A Z :=
    e0.lift_openEmbedding hUopen.isOpenEmbedding_subtypeVal
  let e2 : OpenPartialHomeomorph Z A := e1.symm
  let e3 : OpenPartialHomeomorph E3 A :=
    e2.lift_openEmbedding hZopen.isOpenEmbedding_subtypeVal
  let e : OpenPartialHomeomorph A E3 := e3.symm
  have hstar : ((↑) : U → A) '' (Set.univ : Set U) = U := by
    ext a
    constructor
    · rintro ⟨u, -, rfl⟩
      exact u.2
    · intro ha
      exact ⟨⟨a, ha⟩, Set.mem_univ _, rfl⟩
  refine ⟨e, ?_, ?_⟩
  · have he : e.source = ((↑) : U → A) '' (Set.univ : Set U) := by
      simp [e, e3, e2, e1, e0]
    rw [he, hstar]
  · have he : e.target = Set.range ((↑) : Z → E3) := by
      simp [e, e3, e2, e1, e0, Z, Subtype.range_val]
    rw [he]
    simp [Z]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RealizationOpenStarChart
