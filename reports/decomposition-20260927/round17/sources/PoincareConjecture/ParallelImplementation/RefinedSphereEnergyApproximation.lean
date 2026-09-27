import PoincareConjecture.ProofContract.Refinement20260927.RelativeApproximation
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedSphereEnergyApproximation
open PoincareConjecture.ProofContract.Refinement20260927
theorem sphere_energy_approximation : SphereEnergyApproximationStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  intro N g n A C Q e hC hQ he
  let K : ℝ := (C + 1) ^ 2 + Q * (2 * C + 1)
  let m : ℝ := sphereEnergyMeasure.real Set.univ
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hm : 0 ≤ m := by
    exact MeasureTheory.measureReal_nonneg
  have hden : 0 < (K + 1) * (m + 1) := by
    positivity
  let delta : ℝ := min 1 (e / ((K + 1) * (m + 1)))
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    exact lt_min (by norm_num) (div_pos he hden)
  have hdelta_one : delta ≤ 1 := by
    dsimp [delta]
    exact min_le_left _ _
  have hdelta_bound : delta ≤ e / ((K + 1) * (m + 1)) := by
    dsimp [delta]
    exact min_le_right _ _
  have hmass_bound : m * (delta * K) ≤ e := by
    have hprod : K * m ≤ (K + 1) * (m + 1) := by
      nlinarith [mul_nonneg hK hm]
    calc
      m * (delta * K) = delta * (K * m) := by ring
      _ ≤ delta * ((K + 1) * (m + 1)) :=
        mul_le_mul_of_nonneg_left hprod (le_of_lt hdelta_pos)
      _ ≤ (e / ((K + 1) * (m + 1))) * ((K + 1) * (m + 1)) :=
        mul_le_mul_of_nonneg_right hdelta_bound (le_of_lt hden)
      _ = e := by field_simp [ne_of_gt hden]
  have hdim : Module.finrank ℝ SphereModel = 2 := by
    simp [SphereModel]
  have bilinear_estimate :
      ∀ (v w : ApproxAmbient n)
        (B₀ A₀ : ApproxAmbient n →L[ℝ] ApproxAmbient n →L[ℝ] ℝ),
        ‖v‖ ≤ C → ‖w - v‖ ≤ delta → ‖A₀‖ ≤ Q → ‖B₀ - A₀‖ ≤ delta →
        |B₀ w w - A₀ v v| ≤ delta * K := by
    intro v w B₀ A₀ hv hdv hA hBA
    have hw : ‖w‖ ≤ C + 1 := by
      calc
        ‖w‖ = ‖(w - v) + v‖ := by congr 1; abel
        _ ≤ ‖w - v‖ + ‖v‖ := norm_add_le _ _
        _ ≤ delta + C := add_le_add hdv hv
        _ ≤ 1 + C := by nlinarith [hdelta_one]
        _ = C + 1 := by ring
    have hBw : ‖(B₀ - A₀) w‖ ≤ delta * (C + 1) := by
      calc
        ‖(B₀ - A₀) w‖ ≤ ‖B₀ - A₀‖ * ‖w‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ delta * (C + 1) :=
          mul_le_mul hBA hw (norm_nonneg _) (le_of_lt hdelta_pos)
    have hAvdiff : ‖A₀ (w - v)‖ ≤ Q * delta := by
      calc
        ‖A₀ (w - v)‖ ≤ ‖A₀‖ * ‖w - v‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ Q * delta := mul_le_mul hA hdv (norm_nonneg _) hQ
    have hAv : ‖A₀ v‖ ≤ Q * C := by
      calc
        ‖A₀ v‖ ≤ ‖A₀‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ Q * C := mul_le_mul hA hv (norm_nonneg _) hQ
    have hexpand :
        B₀ w w - A₀ v v =
          ((B₀ - A₀) w) w + (A₀ (w - v)) w + (A₀ v) (w - v) := by
      simp only [sub_apply, map_sub]
      abel
    have ht₁ : ‖((B₀ - A₀) w) w‖ ≤ delta * (C + 1) ^ 2 := by
      calc
        ‖((B₀ - A₀) w) w‖ ≤ ‖(B₀ - A₀) w‖ * ‖w‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ (delta * (C + 1)) * (C + 1) :=
          mul_le_mul hBw hw (norm_nonneg _) (by positivity)
        _ = delta * (C + 1) ^ 2 := by ring
    have ht₂ : ‖(A₀ (w - v)) w‖ ≤ (Q * delta) * (C + 1) := by
      calc
        ‖(A₀ (w - v)) w‖ ≤ ‖A₀ (w - v)‖ * ‖w‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ (Q * delta) * (C + 1) :=
          mul_le_mul hAvdiff hw (norm_nonneg _) (by positivity)
    have ht₃ : ‖(A₀ v) (w - v)‖ ≤ (Q * C) * delta := by
      calc
        ‖(A₀ v) (w - v)‖ ≤ ‖A₀ v‖ * ‖w - v‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ (Q * C) * delta :=
          mul_le_mul hAv hdv (norm_nonneg _) (by positivity)
    calc
      |B₀ w w - A₀ v v| =
          ‖((B₀ - A₀) w) w + (A₀ (w - v)) w + (A₀ v) (w - v)‖ := by
            rw [Real.norm_eq_abs, hexpand]
      _ ≤ ‖((B₀ - A₀) w) w‖ + ‖(A₀ (w - v)) w‖ + ‖(A₀ v) (w - v)‖ := by
        calc
          ‖((B₀ - A₀) w) w + (A₀ (w - v)) w + (A₀ v) (w - v)‖
              ≤ ‖((B₀ - A₀) w) w + (A₀ (w - v)) w‖ + ‖(A₀ v) (w - v)‖ :=
                norm_add_le _ _
          _ ≤ (‖((B₀ - A₀) w) w‖ + ‖(A₀ (w - v)) w‖) +
                ‖(A₀ v) (w - v)‖ :=
              add_le_add (norm_add_le _ _) le_rfl
      _ ≤ delta * (C + 1) ^ 2 + (Q * delta) * (C + 1) + (Q * C) * delta := by
        gcongr
      _ = delta * K := by
        dsimp [K]
        ring
  refine ⟨delta, hdelta_pos, hdelta_one, ?_⟩
  intro f h hf hsmooth hfint hbounds
  have hh := hsmooth.mdifferentiable (by norm_num)
  have hhint : MeasureTheory.Integrable (sphereEnergyDensity N g h) sphereEnergyMeasure :=
    sphere_density_integrable checked_sphere_energy_continuity N g h hsmooth
  have hdensity :
      ∀ p : PoincareConjecture.ProofContract.V1.Sphere2,
        ‖sphereEnergyDensity N g h p - sphereEnergyDensity N g f p‖ ≤ delta * K := by
    intro p
    have hp := hbounds p
    rcases hp with ⟨hform, hformdiff, hvectors⟩
    have hterm (i : Fin (Module.finrank ℝ SphereModel)) :
        |(A.form (h p) (ambientSphereVector A h p i)) (ambientSphereVector A h p i) -
          (A.form (f p) (ambientSphereVector A f p i)) (ambientSphereVector A f p i)| ≤
          delta * K := by
      rcases hvectors i with ⟨hv, hdv⟩
      exact bilinear_estimate
        (ambientSphereVector A f p i) (ambientSphereVector A h p i)
        (A.form (h p)) (A.form (f p)) hv hdv hform hformdiff
    have hsum :
        ‖(∑ i : Fin (Module.finrank ℝ SphereModel),
              (A.form (h p) (ambientSphereVector A h p i)) (ambientSphereVector A h p i)) -
          ∑ i : Fin (Module.finrank ℝ SphereModel),
              (A.form (f p) (ambientSphereVector A f p i)) (ambientSphereVector A f p i)‖ ≤
          2 * (delta * K) := by
      calc
        _ = ‖∑ i : Fin (Module.finrank ℝ SphereModel),
              ((A.form (h p) (ambientSphereVector A h p i)) (ambientSphereVector A h p i) -
                (A.form (f p) (ambientSphereVector A f p i)) (ambientSphereVector A f p i))‖ := by
              rw [Finset.sum_sub_distrib]
        _ ≤ ∑ i : Fin (Module.finrank ℝ SphereModel),
              ‖(A.form (h p) (ambientSphereVector A h p i)) (ambientSphereVector A h p i) -
                (A.form (f p) (ambientSphereVector A f p i)) (ambientSphereVector A f p i)‖ :=
              norm_sum_le _ _
        _ ≤ ∑ _i : Fin (Module.finrank ℝ SphereModel), delta * K :=
              Finset.sum_le_sum (fun i _ => by simpa [Real.norm_eq_abs] using hterm i)
        _ = 2 * (delta * K) := by simp [hdim]
    calc
      ‖sphereEnergyDensity N g h p - sphereEnergyDensity N g f p‖ =
          ‖(1 / 2 : ℝ) * (∑ i : Fin (Module.finrank ℝ SphereModel),
              (A.form (h p) (ambientSphereVector A h p i)) (ambientSphereVector A h p i)) -
            (1 / 2 : ℝ) * (∑ i : Fin (Module.finrank ℝ SphereModel),
              (A.form (f p) (ambientSphereVector A f p i)) (ambientSphereVector A f p i))‖ := by
        rw [sphereDensity_ambient A h hh p, sphereDensity_ambient A f hf p]
      _ =
          (1 / 2 : ℝ) * ‖(∑ i : Fin (Module.finrank ℝ SphereModel),
              (A.form (h p) (ambientSphereVector A h p i)) (ambientSphereVector A h p i) -
            ∑ i : Fin (Module.finrank ℝ SphereModel),
              (A.form (f p) (ambientSphereVector A f p i)) (ambientSphereVector A f p i))‖ := by
        rw [← mul_sub, norm_mul]
        norm_num
      _ ≤ (1 / 2 : ℝ) * (2 * (delta * K)) := by
        exact mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = delta * K := by ring
  have hdiffint :
      MeasureTheory.Integrable
        (fun p : PoincareConjecture.ProofContract.V1.Sphere2 =>
          sphereEnergyDensity N g h p - sphereEnergyDensity N g f p)
        sphereEnergyMeasure := hhint.sub hfint
  have hnormint := hdiffint.norm
  have hconstint :
      MeasureTheory.Integrable
        (fun _ : PoincareConjecture.ProofContract.V1.Sphere2 => delta * K) sphereEnergyMeasure :=
    MeasureTheory.integrable_const _
  have hintegral := MeasureTheory.integral_mono_ae hnormint hconstint
    (Filter.Eventually.of_forall hdensity)
  change |(∫ p, sphereEnergyDensity N g h p ∂sphereEnergyMeasure) -
    ∫ p, sphereEnergyDensity N g f p ∂sphereEnergyMeasure| ≤ e
  rw [← MeasureTheory.integral_sub hhint hfint, ← Real.norm_eq_abs]
  calc
    ‖∫ p, sphereEnergyDensity N g h p - sphereEnergyDensity N g f p ∂sphereEnergyMeasure‖ ≤
        ∫ p, ‖sphereEnergyDensity N g h p - sphereEnergyDensity N g f p‖ ∂sphereEnergyMeasure :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ _p : PoincareConjecture.ProofContract.V1.Sphere2, delta * K ∂sphereEnergyMeasure :=
      hintegral
    _ = m * (delta * K) := by
      rw [MeasureTheory.integral_const]
      simp [m, smul_eq_mul]
    _ ≤ e := hmass_bound
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedSphereEnergyApproximation
