import MorganTianLib.Ch02.NeckVolume.CylinderModelFacts
import Mathlib

open Set MeasureTheory Riemannian Bundle Function
open scoped ContDiff Manifold Topology ENNReal Bundle RealInnerProductSpace
noncomputable section
namespace MorganTianLib

/-- **Math.** A fixed nonempty bounded open transverse patch has rectangular
Haar volume bounded below by a positive constant times axial length. -/
theorem haar_cylinder_box_volume_lower
    (mu : Measure (EuclideanSpace ℝ (Fin 3))) [mu.IsAddHaarMeasure]
    {U : Set (EuclideanSpace ℝ (Fin 2))}
    (hU : IsOpen U) (hne : U.Nonempty) (hbounded : Bornology.IsBounded U) :
    ∃ b : ℝ, 0 < b ∧ ∀ L : ℝ, 0 < L →
      ENNReal.ofReal (b * L) ≤
        mu (epsilonNeckModelEquiv ''
          (U ×ˢ {t : EpsilonNeckAxis | -L / 2 < t 0 ∧ t 0 < -L / 4})) := by
/- SWARM_PROOF_BEGIN -/
  let I₁ : Set EpsilonNeckAxis :=
    {t | -(1 : ℝ) / 2 < t 0 ∧ t 0 < -(1 : ℝ) / 4}
  let Q₁ : Set (EuclideanSpace ℝ (Fin 2) × EpsilonNeckAxis) := U ×ˢ I₁
  let B : Set (EuclideanSpace ℝ (Fin 3)) := epsilonNeckModelEquiv '' Q₁
  have haxis : Continuous (fun t : EpsilonNeckAxis => t 0) :=
    PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0
  have hI₁open : IsOpen I₁ := by
    dsimp [I₁]
    exact (isOpen_lt continuous_const haxis).inter
      (isOpen_lt haxis continuous_const)
  have hI₁ne : I₁.Nonempty := by
    let t : EpsilonNeckAxis := EuclideanSpace.single 0 (-(3 : ℝ) / 8)
    refine ⟨t, ?_⟩
    dsimp [I₁, t]
    change -(1 : ℝ) / 2 < -(3 : ℝ) / 8 ∧ -(3 : ℝ) / 8 < -(1 : ℝ) / 4
    norm_num
  have hI₁bounded : Bornology.IsBounded I₁ := by
    apply (Metric.isBounded_iff_subset_closedBall (0 : EpsilonNeckAxis)).2
    refine ⟨1, ?_⟩
    intro t ht
    have hnorm : ‖t‖ = ‖t 0‖ := by
      rw [EuclideanSpace.norm_eq]
      simp [Real.sqrt_sq_eq_abs]
    have ht0 : ‖t 0‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [ht.1, ht.2]
    rw [Metric.mem_closedBall, dist_zero_right, hnorm]
    exact ht0
  have hQ₁open : IsOpen Q₁ := hU.prod hI₁open
  have hQ₁ne : Q₁.Nonempty := hne.prod hI₁ne
  have hQ₁bounded : Bornology.IsBounded Q₁ := hbounded.prod hI₁bounded
  have hBopen : IsOpen B := epsilonNeckModelEquiv.isOpenMap _ hQ₁open
  have hBne : B.Nonempty := hQ₁ne.image epsilonNeckModelEquiv
  have hBpos : 0 < mu B := hBopen.measure_pos mu hBne
  have hBtop : mu B < (⊤ : ENNReal) :=
    (epsilonNeckModelEquiv.lipschitz.isBounded_image hQ₁bounded).measure_lt_top
  let b : ℝ := (mu B).toReal
  have hb : 0 < b := ENNReal.toReal_pos hBpos.ne' hBtop.ne
  refine ⟨b, hb, ?_⟩
  intro L hL
  let IL : Set EpsilonNeckAxis :=
    {t | -L / 2 < t 0 ∧ t 0 < -L / 4}
  let QL : Set (EuclideanSpace ℝ (Fin 2) × EpsilonNeckAxis) := U ×ˢ IL
  let sL : EpsilonNeckAxis ≃L[ℝ] EpsilonNeckAxis :=
    ContinuousLinearEquiv.equivOfInverse
      (L • ContinuousLinearMap.id ℝ EpsilonNeckAxis)
      (L⁻¹ • ContinuousLinearMap.id ℝ EpsilonNeckAxis)
      (by intro t; simp [smul_smul, hL.ne'])
      (by intro t; simp [smul_smul, hL.ne'])
  let pL : (EuclideanSpace ℝ (Fin 2) × EpsilonNeckAxis) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin 2) × EpsilonNeckAxis) :=
    (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2))).prodCongr sL
  let TL : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    epsilonNeckModelEquiv.symm.trans (pL.trans epsilonNeckModelEquiv)
  have hIL : IL = sL '' I₁ := by
    ext t
    constructor
    · intro ht
      refine ⟨sL.symm t, ?_, ?_⟩
      · dsimp [I₁, sL]
        change -(1 : ℝ) / 2 < L⁻¹ * t 0 ∧ L⁻¹ * t 0 < -(1 : ℝ) / 4
        have hLi : L⁻¹ * L = 1 := inv_mul_cancel₀ hL.ne'
        have hlow := mul_lt_mul_of_pos_left ht.1 (inv_pos.mpr hL)
        have hupp := mul_lt_mul_of_pos_left ht.2 (inv_pos.mpr hL)
        constructor
        · calc
            -(1 : ℝ) / 2 = L⁻¹ * (-L / 2) := by field_simp
            _ < L⁻¹ * t 0 := hlow
        · calc
            L⁻¹ * t 0 < L⁻¹ * (-L / 4) := hupp
            _ = -(1 : ℝ) / 4 := by field_simp
      · exact sL.apply_symm_apply t
    · rintro ⟨t, ht, rfl⟩
      dsimp [IL, sL]
      change -L / 2 < L * t 0 ∧ L * t 0 < -L / 4
      constructor <;> nlinarith [ht.1, ht.2]
  have hQL : QL = pL '' Q₁ := by
    rw [show QL = U ×ˢ (sL '' I₁) by simp [QL, hIL]]
    ext z
    constructor
    · rintro ⟨hu, ⟨t, ht, hzt⟩⟩
      refine ⟨(z.1, t), ⟨hu, ht⟩, ?_⟩
      ext <;> simp [pL, hzt]
    · rintro ⟨w, ⟨hu, ht⟩, rfl⟩
      exact ⟨hu, ⟨w.2, ht, rfl⟩⟩
  have htarget : epsilonNeckModelEquiv '' QL = TL '' B := by
    rw [hQL]
    ext z
    constructor
    · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨epsilonNeckModelEquiv w, ⟨w, hw, rfl⟩, by simp [TL, pL]⟩
    · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨pL w, ⟨w, hw, rfl⟩, by simp [TL, pL]⟩
  have hdet : |LinearMap.det (TL : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin 3))| = L := by
    have hconj : LinearMap.det (TL : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin 3)) = LinearMap.det (pL :
          (EuclideanSpace ℝ (Fin 2) × EpsilonNeckAxis) →ₗ[ℝ]
            (EuclideanSpace ℝ (Fin 2) × EpsilonNeckAxis)) := by
      have h := congrArg (fun u : ℝˣ => (u : ℝ))
        (LinearEquiv.det_conj pL.toLinearEquiv epsilonNeckModelEquiv.toLinearEquiv)
      have hTL : TL.toLinearEquiv =
          (epsilonNeckModelEquiv.toLinearEquiv.symm.trans pL.toLinearEquiv).trans
            epsilonNeckModelEquiv.toLinearEquiv := by
        ext x
        simp [TL]
      change LinearMap.det TL.toLinearEquiv.toLinearMap =
        LinearMap.det pL.toLinearEquiv.toLinearMap
      rw [hTL]
      simpa only [LinearEquiv.coe_det] using h
    have hsdet : LinearMap.det (sL : EpsilonNeckAxis →ₗ[ℝ] EpsilonNeckAxis) = L := by
      change LinearMap.det (L • (LinearMap.id : EpsilonNeckAxis →ₗ[ℝ] EpsilonNeckAxis)) = L
      rw [LinearMap.det_smul, LinearMap.det_id]
      norm_num
    have hpdet : LinearMap.det (pL :
        (EuclideanSpace ℝ (Fin 2) × EpsilonNeckAxis) →ₗ[ℝ]
          (EuclideanSpace ℝ (Fin 2) × EpsilonNeckAxis)) = L := by
      change LinearMap.det ((LinearMap.id : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin 2)).prodMap (sL : EpsilonNeckAxis →ₗ[ℝ] EpsilonNeckAxis)) = L
      rw [LinearMap.det_prodMap, LinearMap.det_id, hsdet, one_mul]
    rw [hconj, hpdet, abs_of_pos hL]
  change ENNReal.ofReal (b * L) ≤ mu (epsilonNeckModelEquiv '' QL)
  rw [htarget, MeasureTheory.Measure.addHaar_image_continuousLinearEquiv, hdet]
  have hBof : ENNReal.ofReal b = mu B := by
    dsimp [b]
    exact ENNReal.ofReal_toReal hBtop.ne
  have heq : ENNReal.ofReal (b * L) = ENNReal.ofReal L * mu B := by
    rw [← hBof, ← ENNReal.ofReal_mul (le_of_lt hL)]
    congr 1
    ring
  exact le_of_eq heq
/- SWARM_PROOF_END -/

end MorganTianLib
