import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function
open scoped Topology RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Pointwise positivity of a continuous compact family gives a genuine uniform lower bound. -/
theorem compact_positive_operator_coercivity {X : Type*} [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K) (hKn : K.Nonempty)
    (A : X → (E3 →L[ℝ] E3)) (hA : ContinuousOn A K)
    (hpos : ∀ x∈K, ∀ v : E3, v ≠ 0 → 0 < inner ℝ (A x v) v) :
    ∃ c : ℝ, 0<c ∧ ∀ x∈K, ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A x v) v :=
/- SWARM_PROOF_BEGIN -/
by
  let S : Set E3 := Metric.sphere (0 : E3) 1
  have hScompact : IsCompact S := by
    dsimp [S]
    exact isCompact_sphere 0 1
  have hSnonempty : S.Nonempty := by
    let b := EuclideanSpace.basisFun (Fin 3) ℝ
    refine ⟨b 0, ?_⟩
    rw [mem_sphere_zero_iff_norm]
    exact b.norm_eq_one 0
  have hprodcompact : IsCompact (K ×ˢ S) := hK.prod hScompact
  have hprodnonempty : (K ×ˢ S).Nonempty := hKn.prod hSnonempty
  let f : X × E3 → ℝ := fun p => inner ℝ (A p.1 p.2) p.2
  have hf : ContinuousOn f (K ×ˢ S) := by
    have hA' : ContinuousOn (fun p : X × E3 => A p.1) (K ×ˢ S) := by
      exact hA.comp continuous_fst.continuousOn (by
        rintro ⟨x, v⟩ ⟨hx, hv⟩
        exact hx)
    have hAv : ContinuousOn (fun p : X × E3 => A p.1 p.2) (K ×ˢ S) :=
      hA'.clm_apply continuous_snd.continuousOn
    exact hAv.inner continuous_snd.continuousOn
  obtain ⟨p, hp, hpmin⟩ := hprodcompact.exists_isMinOn hprodnonempty hf
  have hpK : p.1 ∈ K := hp.1
  have hpS : p.2 ∈ S := hp.2
  have hp2ne : p.2 ≠ 0 := by
    intro hp20
    have : ‖p.2‖ = 1 := (mem_sphere_zero_iff_norm.mp hpS)
    simp [hp20] at this
  let c : ℝ := f p
  have hc : 0 < c := by
    dsimp [c, f]
    exact hpos p.1 hpK p.2 hp2ne
  refine ⟨c, hc, ?_⟩
  intro x hx v
  by_cases hv : v = 0
  · simp [hv]
  · let r : ℝ := ‖v‖
    have hr : 0 < r := by
      dsimp [r]
      exact (norm_pos_iff.mpr hv)
    let u : E3 := r⁻¹ • v
    have huS : u ∈ S := by
      rw [mem_sphere_zero_iff_norm]
      change ‖r⁻¹ • v‖ = 1
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr]
      exact inv_mul_cancel₀ hr.ne'
    have hunit : c ≤ inner ℝ (A x u) u := by
      change f p ≤ f (x, u)
      exact hpmin ⟨hx, huS⟩
    have hscaled : c ≤ (r⁻¹)^2 * inner ℝ (A x v) v := by
      calc
        c ≤ inner ℝ (A x u) u := hunit
        _ = (r⁻¹)^2 * inner ℝ (A x v) v := by
          rw [show u = r⁻¹ • v by rfl, ContinuousLinearMap.map_smul,
            real_inner_smul_left, real_inner_smul_right]
          ring
    calc
      c * ‖v‖ ^ 2 = c * r ^ 2 := by rfl
      _ ≤ ((r⁻¹)^2 * inner ℝ (A x v) v) * r ^ 2 :=
        mul_le_mul_of_nonneg_right hscaled (sq_nonneg r)
      _ = inner ℝ (A x v) v := by
        field_simp
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
