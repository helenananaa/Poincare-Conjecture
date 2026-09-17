import PoincareConjecture.Topology.FiberSaturation.BoundaryRegularity
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option autoImplicit false
noncomputable section

namespace PoincareConjecture.Topology.FiberSaturation
open Set Function
open scoped Manifold ContDiff

/-- Shrinking an ambient chart turns an embedding's local normal form into
an exact local set model. Global embedding, not just immersion, excludes
other parts of the source from re-entering the chosen neighborhood. -/
theorem embedding_local_set_model {A B V : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace V] {f : A → B}
    (hf : _root_.Topology.IsEmbedding f) (e₀ : OpenPartialHomeomorph B V)
    (g : PartialEquiv A V) (hg : IsOpen g.source)
    (hmap : MapsTo f g.source e₀.source)
    (hcoord : EqOn (e₀ ∘ f) g g.source)
    {O R : Set V} (hO : IsOpen O) (htarget : g.target = O ∩ R)
    {x : A} (hx : x ∈ g.source) :
    ∃ e : OpenPartialHomeomorph B V,
      f x ∈ e.source ∧ e.IsImage (range f) R ∧ e (f x) = g x := by
  obtain ⟨W, hW, hpre⟩ := hf.isInducing.isOpen_iff.mp hg
  let S : Set B := W ∩ (e₀.source ∩ e₀ ⁻¹' O)
  have hS : IsOpen S := hW.inter (e₀.isOpen_inter_preimage hO)
  let e := e₀.restr S
  have hfx : f x ∈ e.source := by
    rw [e₀.restr_source' S hS]
    refine ⟨hmap hx, ?_, hmap hx, ?_⟩
    · change x ∈ f ⁻¹' W
      rwa [hpre]
    · change e₀ (f x) ∈ O
      rw [show e₀ (f x) = g x from hcoord hx]
      exact (htarget ▸ g.map_source hx).1
  refine ⟨e, hfx, ?_, hcoord hx⟩
  intro y hy
  have hy' : y ∈ e₀.source ∩ S := by rwa [e₀.restr_source' S hS] at hy
  change e₀ y ∈ R ↔ y ∈ range f
  constructor
  · intro hyr
    have hyt : e₀ y ∈ g.target := htarget ▸ ⟨hy'.2.2.2, hyr⟩
    refine ⟨g.symm (e₀ y), ?_⟩
    apply e₀.injOn (hmap (g.map_target hyt)) hy'.1
    exact (hcoord (g.map_target hyt)).trans (g.right_inv hyt)
  · rintro ⟨z, rfl⟩
    have hz : z ∈ g.source := by
      rw [← hpre]
      exact hy'.2.1
    rw [show e₀ (f z) = g z from hcoord hz]
    exact (htarget ▸ g.map_source hz).2

end PoincareConjecture.Topology.FiberSaturation
