import PoincareConjecture.ProofContract.V1.Obligations

/-!
# Checked conditional assembly

The recursion below is genuine induction over finite traces and connected-sum
expressions. The open theorem arguments are explicit. These theorems establish
compatibility of the frozen boundaries, NOT the Poincare conjecture.
-/

universe u
namespace PoincareConjecture.ProofContract.V1

/-- Reconstruct standard factors backwards through one exact topological step. -/
theorem TopologicalStep.reconstruct {before after : List ClosedThreeManifold.{u}}
    (step : TopologicalStep before after)
    (done : ∀ M ∈ after, StandardDecomposition M) :
    ∀ M ∈ before, StandardDecomposition M := by
  cases step with
  | discardCovered pre post M h =>
    intro X hx
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | hx
    · exact done X (by simp only [List.mem_append]; exact Or.inl hx)
    · exact .sphereCovered h
    · exact done X (by simp only [List.mem_append]; exact Or.inr hx)
  | discardHandle pre post M h =>
    intro X hx
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | hx
    · exact done X (by simp only [List.mem_append]; exact Or.inl hx)
    · exact .handle h
    · exact done X (by simp only [List.mem_append]; exact Or.inr hx)
  | split pre post A B M h =>
    intro X hx
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | hx
    · exact done X (by simp only [List.mem_append, List.mem_cons]; exact Or.inl hx)
    · exact .connectedSum h (done A (by simp)) (done B (by simp))
    · exact done X (by simp only [List.mem_append, List.mem_cons]; exact Or.inr (Or.inr (Or.inr hx)))

/-- Finite extinction data gives finite, nonempty factor expressions for each
initial component; no geometric theorem is asserted here. -/
theorem FiniteExtinctionTrace.decomposes {components : List ClosedThreeManifold.{u}}
    (trace : FiniteExtinctionTrace components) :
    ∀ M ∈ components, StandardDecomposition M := by
  induction trace with
  | empty => simp
  | step step trace ih => exact step.reconstruct ih

/-- Four local topology obligations suffice to recognize a simply connected
standard-factor expression. No classification result is assumed implicitly. -/
theorem recognize_standard_decomposition
    (cover : SphereCoverRecognitionStatement.{u})
    (handle : HandleExclusionStatement.{u})
    (factors : ConnectedSumFactorsStatement.{u})
    (sphereSum : ConnectedSumSphereStatement.{u})
    {M : ClosedThreeManifold.{u}} (d : StandardDecomposition M) :
    SimplyConnectedSpace M → Nonempty (M ≃ₜ Sphere3) := by
  induction d with
  | sphereCovered h => intro hsc; exact cover _ hsc h
  | handle h => intro hsc; exact (handle _ hsc h).elim
  | connectedSum h da db iha ihb =>
    intro hsc
    obtain ⟨ha, hb⟩ := factors _ _ _ h hsc
    exact sphereSum _ _ _ h (iha ha) (ihb hb)

/-- The geometric output is consumed without changing its statement. -/
theorem smooth_topological_of_trace
    (geometric : GeometricTraceStatement.{u})
    (cover : SphereCoverRecognitionStatement.{u})
    (handle : HandleExclusionStatement.{u})
    (factors : ConnectedSumFactorsStatement.{u})
    (sphereSum : ConnectedSumSphereStatement.{u}) :
    SmoothTopologicalPoincareStatement.{u} := by
  intro M hsm hsc
  exact recognize_standard_decomposition cover handle factors sphereSum
    ((geometric M hsm hsc).decomposes M (by simp)) hsc

/-- The original topology survives the explicitly supplied smoothing. -/
theorem topological_of_smoothing_and_smooth_topological
    (smoothing : SmoothingStatement.{u})
    (smoothResult : SmoothTopologicalPoincareStatement.{u}) :
    TopologicalPoincareStatement.{u} := by
  intro M hsc
  obtain ⟨s⟩ := smoothing M
  obtain ⟨e⟩ := smoothResult s.manifold s.smooth hsc
  exact ⟨s.homeomorph.trans e⟩

/-- The smooth blueprint conclusion implies the weaker smooth topological one. -/
theorem smooth_topological_of_smooth
    (h : SmoothPoincareStatement.{u}) : SmoothTopologicalPoincareStatement.{u} := by
  intro M hsm hsc
  obtain ⟨e⟩ := h M hsm hsc
  exact ⟨e.toHomeomorph⟩

/-- Conditional top-level assembly: ALL six unproved inputs remain visible.
Do not rename this to an unconditional Poincare theorem. -/
theorem topological_of_contracts
    (smoothing : SmoothingStatement.{u})
    (geometric : GeometricTraceStatement.{u})
    (cover : SphereCoverRecognitionStatement.{u})
    (handle : HandleExclusionStatement.{u})
    (factors : ConnectedSumFactorsStatement.{u})
    (sphereSum : ConnectedSumSphereStatement.{u}) :
    TopologicalPoincareStatement.{u} :=
  topological_of_smoothing_and_smooth_topological smoothing
    (smooth_topological_of_trace geometric cover handle factors sphereSum)

end PoincareConjecture.ProofContract.V1
