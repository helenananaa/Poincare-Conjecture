import PoincareConjecture.ProofContract.V1.Obligations
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- Exact frozen top-level handle exclusion; no extra premise. -/
theorem handle_exclusion : HandleExclusionStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  intro M hM hHandle
  rcases hHandle with ⟨e⟩
  letI : SimplyConnectedSpace M := hM
  letI : SimplyConnectedSpace SphereHandle :=
    e.symm.toHomotopyEquiv.simplyConnectedSpace
  have hcircle : Nontrivial (FundamentalGroup Circle (1 : Circle)) := by
    let G := AddSubgroup.zmultiples (2 * Real.pi)
    letI : Nontrivial G := by
      refine ⟨⟨0, G.zero_mem⟩, ⟨2 * Real.pi, ?_⟩, ?_⟩
      · exact ⟨1, by simp [G]⟩
      · intro h
        have : (0 : ℝ) = 2 * Real.pi := congrArg Subtype.val h
        nlinarith [Real.pi_pos]
    let eqv := (Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv
      (x := (1 : Circle)) ⟨0, by simp⟩)
    let g0 : G := ⟨0, G.zero_mem⟩
    let g1 : G := ⟨2 * Real.pi, by exact ⟨1, by simp⟩⟩
    refine ⟨eqv.symm (MulOpposite.op (Multiplicative.ofAdd g0)),
      eqv.symm (MulOpposite.op (Multiplicative.ofAdd g1)), ?_⟩
    intro h
    have h' : MulOpposite.op (Multiplicative.ofAdd g0) =
        MulOpposite.op (Multiplicative.ofAdd g1) := by
      simpa using congrArg eqv h
    have hv := congrArg (fun z => Multiplicative.toAdd (MulOpposite.unop z)) h'
    exact (show g0 ≠ g1 from by
      intro hg
      have : (0 : ℝ) = 2 * Real.pi := congrArg Subtype.val hg
      nlinarith [Real.pi_pos]) hv
  let p : Sphere2 := ⟨EuclideanSpace.single 0 1, by
    rw [Metric.mem_sphere, dist_zero_right, EuclideanSpace.norm_single]
    simp⟩
  let s : C(Circle, SphereHandle) := ⟨fun z => (p, z), by fun_prop⟩
  let r : C(SphereHandle, Circle) := ⟨Prod.snd, continuous_snd⟩
  have hsr : r.comp s = ContinuousMap.id Circle := by
    ext z
    rfl
  have hmap_id (c : Path.Homotopic.Quotient (1 : Circle) 1) :
      c.map (r.comp s) = c := by
    obtain ⟨γ⟩ := c
    congr 1
  letI : Subsingleton (FundamentalGroup SphereHandle (p, 1)) := inferInstance
  haveI : Subsingleton (FundamentalGroup Circle 1) := by
    constructor
    intro a b
    have hcomp (c : FundamentalGroup Circle 1) :
        FundamentalGroup.map r (s 1) (FundamentalGroup.map s 1 c) =
          (FundamentalGroup.toPath c).map (r.comp s) := by
      change ((FundamentalGroup.toPath c).map s).map r = _
      rw [← Path.Homotopic.Quotient.map_comp]
    have hab : FundamentalGroup.map s 1 a = FundamentalGroup.map s 1 b :=
      Subsingleton.elim _ _
    have hab' := congrArg (fun c => FundamentalGroup.map r (s 1) c) hab
    have ha1 : (FundamentalGroup.toPath a).map (r.comp s) =
        FundamentalGroup.map r (s 1) (FundamentalGroup.map s 1 a) :=
      (hcomp a).symm
    have ha0 : a = (FundamentalGroup.toPath a).map (r.comp s) :=
      (hmap_id _).symm
    exact ha0.trans <| ha1.trans <| hab'.trans <| (hcomp b).trans (hmap_id _)
  exact (not_subsingleton_iff_nontrivial.mpr hcircle) inferInstance
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
