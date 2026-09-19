import PoincareConjecture.ParallelMath.Transfer.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transfer
open Set Function Filter MeasureTheory
open scoped Topology BigOperators

/-- Two vectors either have rank below two, or have explicit triangular coordinates in a reference-orthonormal pair. -/
theorem pair_degenerate_or_orthonormal {V : Type*} [AddCommGroup V] [Module ℝ V]
    (G : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hs : ∀ x y, G x y = G y x)
    (hp : ∀ x : V, x ≠ 0 → 0 < G x x) (v w : V) :
    (v = 0 ∨ ∃ t : ℝ, w = t • v) ∨
    ∃ e f : V, ∃ a b c : ℝ, 0 < a ∧ 0 < c ∧
      G e e = 1 ∧ G f f = 1 ∧ G e f = 0 ∧
      v = a • e ∧ w = b • e + c • f :=
/- SWARM_PROOF_BEGIN -/
by
  rcases eq_or_ne v 0 with hv | hv
  · exact Or.inl (Or.inl hv)
  · set A : ℝ := G v v
    have hA : 0 < A := hp v hv
    set q : ℝ := G v w / A
    set u : V := w - q • v
    rcases eq_or_ne u 0 with hu | hu
    · refine Or.inl (Or.inr ⟨q, ?_⟩)
      exact eq_of_sub_eq_zero hu
    · set D : ℝ := G u u
      have hD : 0 < D := hp u hu
      set a : ℝ := Real.sqrt A
      set c : ℝ := Real.sqrt D
      have ha : 0 < a := Real.sqrt_pos.mpr hA
      have hc : 0 < c := Real.sqrt_pos.mpr hD
      set e : V := a⁻¹ • v
      set f : V := c⁻¹ • u
      set b : ℝ := q * a
      have hvu : G v u = 0 := by
        dsimp [u]
        rw [map_sub, map_smul, smul_eq_mul]
        change G v w - q * A = 0
        dsimp [q]
        rw [div_mul_cancel₀ _ hA.ne']
        exact sub_self _
      have hnorm : ∀ (x : V) (r : ℝ), 0 < r → G x x = r * r →
          G (r⁻¹ • x) (r⁻¹ • x) = 1 := by
        intro x r hr hx
        rw [LinearMap.map_smul₂, map_smul, smul_eq_mul, smul_eq_mul, hx]
        field_simp [hr.ne']
      refine Or.inr ⟨e, f, a, b, c, ha, hc, ?gee, ?gff, ?gef, ?vre, ?wre⟩
      · dsimp [e]
        refine hnorm v a ha ?_
        exact (Real.mul_self_sqrt hA.le).symm
      · dsimp [f]
        refine hnorm u c hc ?_
        exact (Real.mul_self_sqrt hD.le).symm
      · rw [hs e f]
        dsimp [e, f]
        rw [LinearMap.map_smul₂, map_smul, smul_eq_mul, smul_eq_mul, hs u v, hvu]
        ring
      · dsimp [e]
        rw [smul_inv_smul₀ ha.ne']
      · have hbe : b • e = q • v := by
          dsimp [b, e]
          rw [smul_smul, mul_assoc, mul_inv_cancel₀ ha.ne', mul_one]
        have hcf : c • f = u := by
          dsimp [f]
          rw [smul_inv_smul₀ hc.ne']
        rw [hbe, hcf]
        dsimp [u]
        rw [add_comm, sub_add_cancel]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transfer
