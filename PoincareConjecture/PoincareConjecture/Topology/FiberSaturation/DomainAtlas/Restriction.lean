import PoincareConjecture.Topology.FiberSaturation.DomainAtlas.Core
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.DomainAtlas
open Set Function Manifold
open scoped Manifold ContDiff Topology
variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace N]
  {I : ModelWithCorners ℝ E H} {K : Set N}

/-- Construct the intrinsic chart from a genuine ambient local model.
The set K retains its original subspace topology. -/
theorem exists_modelDomainChart (I : ModelWithCorners ℝ E H) (K : Set N)
    (e : OpenPartialHomeomorph N E) (he : e.IsImage K (range I))
    (p : K) (hp : p.1 ∈ e.source) :
    ∃ c : ModelDomainChart I K, c.ambient = e :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let src : Set K := (Subtype.val : K → N) ⁻¹' e.source
  let tgt : Set H := I ⁻¹' e.target
  have _hp : p ∈ src := hp
  have hmem : ∀ ⦃y : H⦄, y ∈ tgt → e.symm (I y) ∈ K := by
    intro y hy
    exact (he.symm_apply_mem_iff hy).mpr (mem_range_self y)
  have hrange : ∀ ⦃q : K⦄, q ∈ src → e q.1 ∈ range I := by
    intro q hq
    exact (he hq).mpr q.property
  let F : K → H := fun q =>
    if h : q.1 ∈ e.source then I.symm (e q.1) else I.symm (e p.1)
  let G : H → K := fun y =>
    if h : y ∈ tgt then ⟨e.symm (I y), hmem h⟩ else p
  have F_src : ∀ q ∈ src, F q = I.symm (e q.1) := fun q hq => dif_pos hq
  have G_tgt : ∀ (y : H) (hy : y ∈ tgt), G y = ⟨e.symm (I y), hmem hy⟩ :=
    fun y hy => dif_pos hy
  have F_maps : MapsTo F src tgt := by
    intro q hq
    rw [F_src q hq]
    change I (I.symm (e q.1)) ∈ e.target
    rw [I.right_inv (hrange hq)]
    exact e.map_source hq
  have G_maps : MapsTo G tgt src := by
    intro y hy
    rw [G_tgt y hy]
    exact e.map_target hy
  have hsrcOpen : IsOpen src := e.open_source.preimage continuous_subtype_val
  have htgtOpen : IsOpen tgt := e.open_target.preimage I.continuous
  have hFcont : ContinuousOn F src := by
    have hcomp : ContinuousOn (I.symm ∘ e ∘ (Subtype.val : K → N)) src :=
      I.continuous_symm.comp_continuousOn
        (e.continuousOn.comp continuous_subtype_val.continuousOn fun _ hx => hx)
    exact hcomp.congr fun q hq => F_src q hq
  have hGcont : ContinuousOn G tgt := by
    rw [continuousOn_iff_continuous_restrict]
    refine continuous_induced_rng.2 ?_
    change Continuous fun y : tgt => (G y.1 : N)
    have hEq : (fun y : tgt => (G y.1 : N)) = fun y : tgt => e.symm (I y.1) := by
      ext y
      exact congrArg Subtype.val (G_tgt y.1 y.2)
    rw [hEq]
    exact (e.continuousOn_symm.comp I.continuous.continuousOn fun _ hy => hy).restrict
  let pe : PartialEquiv K H :=
    { toFun := F
      invFun := G
      source := src
      target := tgt
      map_source' := F_maps
      map_target' := G_maps
      left_inv' := by
        intro q hq
        apply Subtype.ext
        calc
          (G (F q)).1
            = (⟨e.symm (I (F q)), hmem (F_maps hq)⟩ : K).1 := by rw [G_tgt _ (F_maps hq)]
          _ = e.symm (I (F q)) := rfl
          _ = e.symm (I (I.symm (e q.1))) := by rw [F_src q hq]
          _ = e.symm (e q.1) := by rw [I.right_inv (hrange hq)]
          _ = q.1 := e.left_inv hq
      right_inv' := by
        intro y hy
        calc
          F (G y)
            = I.symm (e (G y).1) := F_src _ (G_maps hy)
          _ = I.symm (e (⟨e.symm (I y), hmem hy⟩ : K).1) := by rw [G_tgt y hy]
          _ = I.symm (e (e.symm (I y))) := rfl
          _ = I.symm (I y) := by rw [e.right_inv hy]
          _ = y := I.left_inv y }
  let intrinsic : OpenPartialHomeomorph K H :=
    { toPartialEquiv := pe
      open_source := hsrcOpen
      open_target := htgtOpen
      continuousOn_toFun := hFcont
      continuousOn_invFun := hGcont }
  refine ⟨
    { ambient := e
      intrinsic := intrinsic
      source_eq := rfl
      target_eq := rfl
      forward_eq := by
        intro q hq
        change I (F q) = e q.1
        rw [F_src q hq, I.right_inv (hrange hq)]
      inverse_eq := by
        intro y hy
        change ((G y : K) : N) = e.symm (I y)
        rw [G_tgt y hy]
      model_image := he },
    rfl⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.DomainAtlas
