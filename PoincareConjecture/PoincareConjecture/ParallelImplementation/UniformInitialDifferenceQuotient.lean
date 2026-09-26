import PoincareConjecture.ParallelImplementation.BoundedC3InitialHolderJets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.UniformInitialDifferenceQuotient
open scoped ContDiff Topology BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
def differenceQuotient (u : E3 → E6) (h : ℝ) (v x : E3) : E6 :=
  h⁻¹ • (u (x + h • v) - u x)
/-- A single bound for actual C2-Holder initial jets of every spatial difference
quotient of smooth compact data. No bound on a PDE solution is asserted. -/
theorem exists_uniform_initial_difference_jets
    (u : E3 → E6) (hu : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u)
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ), h ≠ 0 → ∀ (v : E3), ‖v‖ ≤ 1 →
      ∃ u0 : E3 →ᵇ E6, ∃ A0 : E3 →ᵇ (E3 →L[ℝ] E6),
      ∃ H0 : E3 →ᵇ (E3 →L[ℝ] E3 →L[ℝ] E6),
        (∀ x : E3, u0 x = differenceQuotient u h v x ∧
          A0 x = fderiv ℝ (differenceQuotient u h v) x ∧
          H0 x = fderiv ℝ (fderiv ℝ (differenceQuotient u h v)) x) ∧
        (∀ x : E3, HasFDerivAt u0 (A0 x) x) ∧
        (∀ x : E3, HasFDerivAt A0 (H0 x) x) ∧
        ‖u0‖ ≤ C ∧ ‖A0‖ ≤ C ∧ ‖H0‖ ≤ C ∧
        (∀ x y : E3, ‖H0 x - H0 y‖ ≤ C * ‖x - y‖ ^ alpha) :=
/- SWARM_PROOF_BEGIN -/
by
  letI : NormedAddCommGroup (E3 →L[ℝ] E3) := inferInstance
  letI : NormedSpace ℝ (E3 →L[ℝ] E3) := inferInstance
  letI : NormedAddCommGroup (E3 →L[ℝ] E6) := inferInstance
  letI : NormedSpace ℝ (E3 →L[ℝ] E6) := inferInstance
  letI : NormedAddCommGroup ((E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
  letI : NormedSpace ℝ ((E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
  letI : NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
  letI : NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
  letI : NormedAddCommGroup ((E3 →L[ℝ] E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
  letI : NormedSpace ℝ ((E3 →L[ℝ] E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
  letI : NormedAddCommGroup
      ((E3 →L[ℝ] E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
  letI : NormedSpace ℝ
      ((E3 →L[ℝ] E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
  letI : NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
  letI : NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
  let D1 : E3 → E3 →L[ℝ] E6 := fderiv ℝ u
  let D2 : E3 → E3 →L[ℝ] E3 →L[ℝ] E6 := fderiv ℝ D1
  let D3 : E3 → E3 →L[ℝ] E3 →L[ℝ] E3 →L[ℝ] E6 := fderiv ℝ D2
  let D4 : E3 → E3 →L[ℝ] E3 →L[ℝ] E3 →L[ℝ] E3 →L[ℝ] E6 := fderiv ℝ D3
  have hD1cd : ContDiff ℝ 3 D1 := by
    have h := hu.fderiv_right (m := 3) (show (4 : ℕ∞ω) ≤ ∞ from
      WithTop.coe_le_coe.mpr (show (4 : ℕ∞) ≤ ⊤ from le_top))
    simpa [D1] using h
  have hD2cd : ContDiff ℝ 2 D2 := by
    have h := hD1cd.fderiv_right (m := 2) (by norm_num)
    simpa [D1, D2] using h
  have hD3cd : ContDiff ℝ 1 D3 := by
    have h := hD2cd.fderiv_right (m := 1) (by norm_num)
    simpa [D1, D2, D3] using h
  have hD4cd : ContDiff ℝ 0 D4 := by
    have h := hD3cd.fderiv_right (m := 0) (by norm_num)
    simpa [D1, D2, D3, D4] using h
  have hD1c : HasCompactSupport D1 := by
    simpa [D1] using hcompact.fderiv ℝ
  have hD2c : HasCompactSupport D2 := by
    simpa [D1, D2] using hD1c.fderiv ℝ
  have hD3c : HasCompactSupport D3 := by
    simpa [D1, D2, D3] using hD2c.fderiv ℝ
  have hD4c : HasCompactSupport D4 := by
    simpa [D1, D2, D3, D4] using hD3c.fderiv ℝ
  obtain ⟨b1, hb1⟩ := hD1cd.continuous.bounded_above_of_compact_support hD1c
  obtain ⟨b2, hb2⟩ := hD2cd.continuous.bounded_above_of_compact_support hD2c
  obtain ⟨b3, hb3⟩ := hD3cd.continuous.bounded_above_of_compact_support hD3c
  obtain ⟨b4, hb4⟩ := hD4cd.continuous.bounded_above_of_compact_support hD4c
  have hb1nonneg : 0 ≤ b1 := le_trans (norm_nonneg (D1 0)) (hb1 0)
  have hb2nonneg : 0 ≤ b2 := le_trans (norm_nonneg (D2 0)) (hb2 0)
  have hb3nonneg : 0 ≤ b3 := le_trans (norm_nonneg (D3 0)) (hb3 0)
  have hb4nonneg : 0 ≤ b4 := le_trans (norm_nonneg (D4 0)) (hb4 0)
  let M : ℝ := b1 + b2 + b3 + b4 + 1
  have hMpos : 0 < M := by
    dsimp [M]
    linarith
  have hMnonneg : 0 ≤ M := le_of_lt hMpos
  have hD1bound : ∀ x : E3, ‖D1 x‖ ≤ M := by
    intro x
    calc
      ‖D1 x‖ ≤ b1 := hb1 x
      _ ≤ M := by dsimp [M]; linarith
  have hD2bound : ∀ x : E3, ‖D2 x‖ ≤ M := by
    intro x
    calc
      ‖D2 x‖ ≤ b2 := hb2 x
      _ ≤ M := by dsimp [M]; linarith
  have hD3bound : ∀ x : E3, ‖D3 x‖ ≤ M := by
    intro x
    calc
      ‖D3 x‖ ≤ b3 := hb3 x
      _ ≤ M := by dsimp [M]; linarith
  have hD4bound : ∀ x : E3, ‖D4 x‖ ≤ M := by
    intro x
    calc
      ‖D4 x‖ ≤ b4 := hb4 x
      _ ≤ M := by dsimp [M]; linarith
  refine ⟨3 * M, by positivity, ?_⟩
  intro h hne v hv
  let Q := fun {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (f : E3 → F) (x : E3) => h⁻¹ • (f (x + h • v) - f x)
  have hqcd : ContDiff ℝ 3 (differenceQuotient u h v) := by
    have harg : ContDiff ℝ ∞ (fun x : E3 => x + h • v) := by
      exact contDiff_id.add contDiff_const
    have hshift : ContDiff ℝ ∞ (fun x : E3 => u (x + h • v)) := hu.comp harg
    have hdiff : ContDiff ℝ ∞ (fun x : E3 => u (x + h • v) - u x) := hshift.sub hu
    have hsmul : ContDiff ℝ ∞ (fun x : E3 => h⁻¹ • (u (x + h • v) - u x)) := by
      simpa using hdiff.const_smul (h⁻¹)
    change ContDiff ℝ 3 (fun x : E3 => h⁻¹ • (u (x + h • v) - u x))
    exact hsmul.of_le (show (3 : ℕ∞ω) ≤ ∞ from
      WithTop.coe_le_coe.mpr (show (3 : ℕ∞) ≤ ⊤ from le_top))
  have quotient_fderiv {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (f : E3 → F) (hf : Differentiable ℝ f) :
      fderiv ℝ (Q f) = Q (fderiv ℝ f : E3 → E3 →L[ℝ] F) := by
    funext x
    change fderiv ℝ (fun y : E3 => h⁻¹ • (f (y + h • v) - f y)) x =
      h⁻¹ • (fderiv ℝ f (x + h • v) - fderiv ℝ f x)
    have hshift : Differentiable ℝ (fun y : E3 => f (y + h • v)) :=
      hf.comp (differentiable_id.add_const (h • v))
    have hdiff : DifferentiableAt ℝ (fun y : E3 => f (y + h • v) - f y) x :=
      (hshift x).sub (hf x)
    rw [fderiv_fun_const_smul hdiff (h⁻¹)]
    change h⁻¹ • fderiv ℝ ((fun y : E3 => f (y + h • v)) - f) x =
      h⁻¹ • (fderiv ℝ f (x + h • v) - fderiv ℝ f x)
    rw [fderiv_sub (hshift x) (hf x)]
    rw [fderiv_comp_add_right]
  have quotient_bound {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (f : E3 → F) (hf : Differentiable ℝ f) (B : ℝ) (hB : 0 ≤ B)
      (hdf : ∀ x : E3, ‖fderiv ℝ f x‖ ≤ B) :
      ∀ x : E3, ‖Q f x‖ ≤ B := by
    intro x
    have hmv : ‖f (x + h • v) - f x‖ ≤ B * ‖(x + h • v) - x‖ :=
      (convex_univ.norm_image_sub_le_of_norm_fderiv_le
        (fun z _ => hf z)
        (fun z _ => hdf z) (x := x) (y := x + h • v) (Set.mem_univ _) (Set.mem_univ _))
    have hshiftNorm : ‖(x + h • v) - x‖ = ‖h‖ * ‖v‖ := by
      rw [show (x + h • v) - x = h • v by abel, norm_smul]
    have hhnorm : 0 < ‖h‖ := norm_pos_iff.mpr hne
    calc
      ‖Q f x‖ = ‖h⁻¹‖ * ‖f (x + h • v) - f x‖ := by
        simp [Q, norm_smul]
      _ ≤ ‖h⁻¹‖ * (B * ‖(x + h • v) - x‖) :=
        mul_le_mul_of_nonneg_left hmv (norm_nonneg _)
      _ = ‖h‖⁻¹ * (B * (‖h‖ * ‖v‖)) := by rw [norm_inv, hshiftNorm]
      _ = B * ‖v‖ := by field_simp [ne_of_gt hhnorm]
      _ ≤ B := by
        calc
          B * ‖v‖ ≤ B * 1 := mul_le_mul_of_nonneg_left hv hB
          _ = B := by ring
  have huDiff : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hD1Diff : Differentiable ℝ D1 := hD1cd.differentiable (by norm_num)
  have hD2Diff : Differentiable ℝ D2 := hD2cd.differentiable (by norm_num)
  have hD3Diff : Differentiable ℝ D3 := hD3cd.differentiable (by norm_num)
  have hq1 : fderiv ℝ (differenceQuotient u h v) = Q D1 := by
    change fderiv ℝ (Q u) = Q D1
    simpa [D1] using quotient_fderiv u huDiff
  have hq2 : fderiv ℝ (fderiv ℝ (differenceQuotient u h v)) =
      Q D2 := by
    rw [hq1]
    simpa [Q, D2] using quotient_fderiv D1 hD1Diff
  have hq3 : fderiv ℝ (fderiv ℝ (fderiv ℝ (differenceQuotient u h v))) =
      Q D3 := by
    rw [hq2]
    simpa [Q, D3] using quotient_fderiv D2 hD2Diff
  have hq0bound : ∀ x : E3, ‖differenceQuotient u h v x‖ ≤ M := by
    change ∀ x : E3, ‖Q u x‖ ≤ M
    exact quotient_bound u huDiff M hMnonneg hD1bound
  have hq1bound : ∀ x : E3, ‖fderiv ℝ (differenceQuotient u h v) x‖ ≤ M := by
    intro x
    rw [hq1]
    exact quotient_bound D1 hD1Diff M hMnonneg hD2bound x
  have hq2bound : ∀ x : E3,
      ‖fderiv ℝ (fderiv ℝ (differenceQuotient u h v)) x‖ ≤ M := by
    intro x
    rw [hq2]
    exact quotient_bound D2 hD2Diff M hMnonneg hD3bound x
  have hq3bound : ∀ x : E3,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (differenceQuotient u h v))) x‖ ≤ M := by
    intro x
    rw [hq3]
    exact quotient_bound D3 hD3Diff M hMnonneg hD4bound x
  obtain ⟨u0, A0, H0, hvalues, hu0deriv, hA0deriv,
      hu0norm, hA0norm, hH0norm, _, _, hH0holder⟩ :=
    PoincareConjecture.ParallelImplementation.BoundedC3InitialHolderJets.exists_bounded_c3_initial_holder_jets
      (differenceQuotient u h v) hqcd M alpha hMnonneg ha ha1
      hq0bound hq1bound hq2bound hq3bound
  refine ⟨u0, A0, H0, hvalues, hu0deriv, hA0deriv, ?_, ?_, ?_, ?_⟩
  · exact le_trans hu0norm (by linarith [hMnonneg])
  · exact le_trans hA0norm (by linarith [hMnonneg])
  · change ‖H0‖ ≤ 3 * M
    exact le_trans hH0norm (by linarith [hMnonneg])
  · exact hH0holder
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.UniformInitialDifferenceQuotient
