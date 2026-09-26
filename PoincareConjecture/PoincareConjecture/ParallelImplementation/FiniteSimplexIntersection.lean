import PoincareConjecture.ParallelImplementation.SimplexFiniteHalfspaces
import PoincareConjecture.ParallelImplementation.FinitePolytopeHalfspaceClip
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.FiniteSimplexIntersection
/-- Construct finite vertices for the actual intersection with a simplex,
including empty intersections and lower-dimensional simplices. -/
theorem exists_finite_vertices_convexHull_inter_simplex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (s t : Finset E) (ht : t.Nonempty)
    (hind : AffineIndependent ℝ (fun v : t => (v : E))) :
    ∃ r : Finset E,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) = convexHull ℝ (r : Set E) ∧
      (r : Set E) ⊆ convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨n, l, a, hsimplex⟩ :=
    PoincareConjecture.ParallelImplementation.SimplexFiniteHalfspaces.simplex_eq_finite_halfspaces
      t ht hind
  let V : List (Fin n) → Finset E := fun is =>
    is.foldr (fun i v =>
      PoincareConjecture.ParallelImplementation.FinitePolytopeHalfspaceClip.clippedVertices
        v (l i) (a i)) s
  have hiter (is : List (Fin n)) :
      convexHull ℝ (V is : Set E) =
        convexHull ℝ (s : Set E) ∩ {x : E | ∀ i ∈ is, l i x ≤ a i} := by
    induction is with
    | nil =>
        simp [V]
    | cons i is ih =>
        rw [show V (i :: is) =
            PoincareConjecture.ParallelImplementation.FinitePolytopeHalfspaceClip.clippedVertices
              (V is) (l i) (a i) by rfl]
        rw [← PoincareConjecture.ParallelImplementation.FinitePolytopeHalfspaceClip.convexHull_inter_halfspace_eq_clipped,
          ih]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, List.mem_cons]
        constructor
        · rintro ⟨⟨hsx, hall⟩, hi⟩
          refine ⟨hsx, ?_⟩
          intro j hj
          rcases hj with rfl | hj
          · exact hi
          · exact hall j hj
        · rintro ⟨hsx, hall⟩
          refine ⟨⟨hsx, ?_⟩, hall i (Or.inl rfl)⟩
          intro j hj
          exact hall j (Or.inr hj)
  let r := V Finset.univ.toList
  refine ⟨r, ?_, ?_⟩
  · rw [hiter]
    apply Set.ext
    intro x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    rw [hsimplex x]
    simp
  · intro x hx
    have hx' : x ∈ convexHull ℝ (r : Set E) :=
      subset_convexHull ℝ (r : Set E) hx
    rw [hiter] at hx'
    rcases hx' with ⟨hsx, hall⟩
    have hineq : ∀ i : Fin n, l i x ≤ a i := by
      intro i
      exact hall i (Finset.mem_toList.mpr (Finset.mem_univ i))
    exact ⟨hsx, (hsimplex x).2 hineq⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.FiniteSimplexIntersection
