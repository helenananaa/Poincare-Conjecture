import PoincareConjecture.ProofContract.Refinement20260927.GeometricNeck
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedEpsilonNeckEmbedding
open PoincareConjecture.ProofContract.Refinement20260927
theorem epsilon_neck_embedding : EpsilonNeckEmbeddingStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  intro M n
  have hpc : Continuous n.closedParameter := by
    unfold AmbientMetricNeck.closedParameter
    apply Continuous.subtype_mk
    have hscalar : Continuous (fun q :
        PoincareConjecture.ProofContract.V1.Sphere2 × Set.Icc (-1 : ℝ) 1 =>
        (q.2 : ℝ) / (2*n.epsilon)) := by fun_prop
    have hsingle : Continuous (fun r : ℝ => EuclideanSpace.single (0 : Fin 1) r) := by
      have hi : Isometry (fun r : ℝ => EuclideanSpace.single (0 : Fin 1) r) := by
        intro a b
        exact PiLp.edist_single_same 2 (fun _ : Fin 1 => ℝ) (0 : Fin 1) a b
      exact hi.continuous
    apply continuous_prodMk.mpr
    exact ⟨continuous_fst, hsingle.comp hscalar⟩
  have hcont : Continuous n.closedCollar := by
    change Continuous (n.inclusion ∘ fun q => n.neck.phi (n.closedParameter q))
    exact n.inclusion_open.continuous.comp (n.neck.phi.continuous.comp hpc)
  have hinj : Function.Injective n.closedCollar := by
    intro x y h
    change n.inclusion (n.neck.phi (n.closedParameter x)) =
      n.inclusion (n.neck.phi (n.closedParameter y)) at h
    have hphi : n.neck.phi (n.closedParameter x) = n.neck.phi (n.closedParameter y) :=
      n.inclusion_open.injective h
    have hparam : n.closedParameter x = n.closedParameter y := n.neck.phi.injective hphi
    have hval := congrArg Subtype.val hparam
    change (x.1, EuclideanSpace.single 0 ((x.2 : ℝ) / (2*n.epsilon))) =
      (y.1, EuclideanSpace.single 0 ((y.2 : ℝ) / (2*n.epsilon))) at hval
    have hs : x.1 = y.1 :=
      congrArg (fun p : MorganTianLib.EpsilonNeckCylinder => p.1) hval
    have hsingle := congrArg (fun p : MorganTianLib.EpsilonNeckCylinder => p.2) hval
    have hax : (x.2 : ℝ) / (2*n.epsilon) = (y.2 : ℝ) / (2*n.epsilon) := by
      have hzero := congrArg (fun v : MorganTianLib.EpsilonNeckAxis => v 0) hsingle
      simpa [EuclideanSpace.single, PiLp.single_apply] using hzero
    have hden : 2*n.epsilon ≠ 0 := ne_of_gt (mul_pos (by norm_num) n.epsilon_pos)
    have ht : (x.2 : ℝ) = (y.2 : ℝ) :=
      mul_right_cancel₀ hden ((div_eq_div_iff hden hden).mp hax)
    apply Prod.ext hs
    apply Subtype.ext
    exact ht
  have hclosed : IsClosedMap n.closedCollar := by
    intro s hs
    exact (hs.isCompact.image hcont).isClosed
  exact Topology.IsClosedEmbedding.isEmbedding
    (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap hcont hinj hclosed)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedEpsilonNeckEmbedding
