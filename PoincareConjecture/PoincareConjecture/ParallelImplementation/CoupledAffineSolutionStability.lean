import PoincareConjecture.ParallelImplementation.JointAffineBackgroundLipschitz
import PoincareConjecture.ParallelImplementation.SameWitnessHeatTranslation
import PoincareConjecture.ParallelImplementation.CoupledAffineParabolicFixedPoint
import PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CoupledAffineSolutionStability
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open scoped Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "A" => E3 →L[ℝ] E3
local notation "V" => E3 →L[ℝ] E6
local notation "H" => E3 →L[ℝ] E3 →L[ℝ] E6
local instance standardGroup0 : NormedAddCommGroup A := inferInstance
local instance standardSpace0 : NormedSpace ℝ A := inferInstance
local instance standardGroup1 : NormedAddCommGroup V := inferInstance
local instance standardSpace1 : NormedSpace ℝ V := inferInstance
local instance standardGroup2 : NormedAddCommGroup H := inferInstance
local instance standardSpace2 : NormedSpace ℝ H := inferInstance
local instance standardGroup3 : NormedAddCommGroup (V →L[ℝ] E6) := inferInstance
local instance standardSpace3 : NormedSpace ℝ (V →L[ℝ] E6) := inferInstance
local instance standardGroup4 : NormedAddCommGroup (A →L[ℝ] V →L[ℝ] V →L[ℝ] E6) := inferInstance
local instance standardSpace4 : NormedSpace ℝ (A →L[ℝ] V →L[ℝ] V →L[ℝ] E6) := inferInstance
local instance standardGroup5 : NormedAddCommGroup (A →L[ℝ] A →L[ℝ] V →L[ℝ] V →L[ℝ] E6) := inferInstance
local instance standardSpace5 : NormedSpace ℝ (A →L[ℝ] A →L[ℝ] V →L[ℝ] V →L[ℝ] E6) := inferInstance

/-- Joint-background Lipschitz estimate for the actual rational inverse-metric
Hessian and quadratic-gradient forcing terms. The correction variable remains
in the existing zero-trace space; the three affine initial backgrounds may
vary. The coefficient of the correction difference is the existing
fixed-background contraction coefficient, while the remaining terms charge
only the changes in the backgrounds. -/
theorem coupled_affine_solution_stability
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T alpha R : ℝ) (hR : 0 < R)
    (X : Submodule ℝ (ForcingJet E6 T))
    (hX : (X : Set (ForcingJet E6 T)) = forcingGraph E6 T alpha)
    (B : A →L[ℝ] A →L[ℝ] V →L[ℝ] V →L[ℝ] E6)
    (a₀ a₁ : ForcingJet A T)
    (ha₀ : a₀ ∈ forcingGraph A T alpha)
    (ha₁ : a₁ ∈ forcingGraph A T alpha)
    (v₀ v₁ : ForcingJet V T)
    (hv₀ : v₀ ∈ forcingGraph V T alpha)
    (hv₁ : v₁ ∈ forcingGraph V T alpha)
    (H₀ H₁ : ForcingJet H T)
    (hH₀ : H₀ ∈ forcingGraph H T alpha)
    (hH₁ : H₁ ∈ forcingGraph H T alpha)
    (P : Y →L[ℝ] ForcingJet A T)
    (Q : Y →L[ℝ] ForcingJet V T)
    (G : Y →L[ℝ] ForcingJet H T)
    (hP : ∀ y, P y ∈ forcingGraph A T alpha)
    (hQ : ∀ y, Q y ∈ forcingGraph V T alpha)
    (hG : ∀ y, G y ∈ forcingGraph H T alpha)
    (hsmall₀ : ‖a₀‖ + ‖P‖ * R ≤ 1 / 2)
    (hsmall₁ : ‖a₁‖ + ‖P‖ * R ≤ 1 / 2)
    (L : Y →L[ℝ] X) (D : X →L[ℝ] Y)
    (hDL : D.comp L = ContinuousLinearMap.id ℝ Y)
    (z₀ z₁ : Y) (hz₀ : ‖z₀‖ ≤ R) (hz₁ : ‖z₁‖ ≤ R)
    (f₀ f₁ : X) (b₀ b₁ : ForcingJet A T)
    (hb₀ : ∀ p : Slab T, (1 - (a₀ + P z₀).1 p) * b₀.1 p = 1 ∧
      b₀.1 p * (1 - (a₀ + P z₀).1 p) = 1)
    (hb₁ : ∀ p : Slab T, (1 - (a₁ + P z₁).1 p) * b₁.1 p = 1 ∧
      b₁.1 p * (1 - (a₁ + P z₁).1 p) = 1)
    (heq₀ : ∀ p : Slab T, (L z₀).1.1 p = f₀.1.1 p +
      PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.principalPart
        (b₀.1 p - 1) ((H₀ + G z₀).1 p) +
      B (b₀.1 p) (b₀.1 p) ((v₀ + Q z₀).1 p) ((v₀ + Q z₀).1 p))
    (heq₁ : ∀ p : Slab T, (L z₁).1.1 p = f₁.1.1 p +
      PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.principalPart
        (b₁.1 p - 1) ((H₁ + G z₁).1 p) +
      B (b₁.1 p) (b₁.1 p) ((v₁ + Q z₁).1 p) ((v₁ + Q z₁).1 p)) :
    let abar : ℝ := max ‖a₀‖ ‖a₁‖
    let vbar : ℝ := max ‖v₀‖ ‖v₁‖
    let hbar : ℝ := max ‖H₀‖ ‖H₁‖
    let S : ℝ := vbar + ‖Q‖ * R
    let Ky : ℝ :=
      18 * (12 * ‖P‖ * (hbar + ‖G‖ * R) +
        (4 * abar + 12 * ‖P‖ * R) * ‖G‖) +
      384 * ‖B‖ * ‖P‖ * S ^ 2 + 64 * ‖B‖ * ‖Q‖ * S
    let Ka : ℝ := 216 * (hbar + ‖G‖ * R) + 384 * ‖B‖ * S ^ 2
    let Kv : ℝ := 64 * ‖B‖ * S
    let Kh : ℝ := 18 * (4 * abar + 12 * ‖P‖ * R)
    ‖D‖ * Ky < 1 →
      ‖z₁ - z₀‖ ≤ (‖D‖ / (1 - ‖D‖ * Ky)) *
        (‖f₁ - f₀‖ + Ka * ‖a₁ - a₀‖ + Kv * ‖v₁ - v₀‖ + Kh * ‖H₁ - H₀‖) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let abar : ℝ := max ‖a₀‖ ‖a₁‖
  let vbar : ℝ := max ‖v₀‖ ‖v₁‖
  let hbar : ℝ := max ‖H₀‖ ‖H₁‖
  let S : ℝ := vbar + ‖Q‖ * R
  let Ky : ℝ :=
    18 * (12 * ‖P‖ * (hbar + ‖G‖ * R) +
      (4 * abar + 12 * ‖P‖ * R) * ‖G‖) +
      384 * ‖B‖ * ‖P‖ * S ^ 2 + 64 * ‖B‖ * ‖Q‖ * S
  let Ka : ℝ := 216 * (hbar + ‖G‖ * R) + 384 * ‖B‖ * S ^ 2
  let Kv : ℝ := 64 * ‖B‖ * S
  let Kh : ℝ := 18 * (4 * abar + 12 * ‖P‖ * R)
  change ‖D‖ * Ky < 1 →
    ‖z₁ - z₀‖ ≤ (‖D‖ / (1 - ‖D‖ * Ky)) *
      (‖f₁ - f₀‖ + Ka * ‖a₁ - a₀‖ + Kv * ‖v₁ - v₀‖ + Kh * ‖H₁ - H₀‖)
  intro hcontract
  obtain ⟨I₀, I₁, N₀, N₁, hI₀, hI₁, hN₀, hN₁, hNlip⟩ :=
    PoincareConjecture.ParallelImplementation.JointAffineBackgroundLipschitz.exists_joint_background_coupled_lipschitz
      T alpha R hR X hX B a₀ a₁ ha₀ ha₁ v₀ v₁ hv₀ hv₁ H₀ H₁ hH₀ hH₁
      P Q G hP hQ hG hsmall₀ hsmall₁

  have hinv₀ (p : Slab T) : (I₀ z₀).1 p = b₀.1 p := by
    have hI := (hI₀ z₀ hz₀).2.2 p
    have hb := hb₀ p
    calc
      (I₀ z₀).1 p = 1 * (I₀ z₀).1 p := by simp
      _ = (b₀.1 p * (1 - (a₀ + P z₀).1 p)) * (I₀ z₀).1 p := by rw [hb.2]
      _ = b₀.1 p * ((1 - (a₀ + P z₀).1 p) * (I₀ z₀).1 p) := by rw [mul_assoc]
      _ = b₀.1 p * 1 := by rw [hI.1]
      _ = b₀.1 p := by simp

  have hinv₁ (p : Slab T) : (I₁ z₁).1 p = b₁.1 p := by
    have hI := (hI₁ z₁ hz₁).2.2 p
    have hb := hb₁ p
    calc
      (I₁ z₁).1 p = 1 * (I₁ z₁).1 p := by simp
      _ = (b₁.1 p * (1 - (a₁ + P z₁).1 p)) * (I₁ z₁).1 p := by rw [hb.2]
      _ = b₁.1 p * ((1 - (a₁ + P z₁).1 p) * (I₁ z₁).1 p) := by rw [mul_assoc]
      _ = b₁.1 p * 1 := by rw [hI.1]
      _ = b₁.1 p := by simp

  have hgraph₀ : (L z₀).1 ∈ forcingGraph E6 T alpha := by
    rw [← hX]
    exact (L z₀).2
  have hgraph₁ : (L z₁).1 ∈ forcingGraph E6 T alpha := by
    rw [← hX]
    exact (L z₁).2
  have hsumgraph₀ : (f₀ + N₀ z₀).1 ∈ forcingGraph E6 T alpha := by
    rw [← hX]
    exact (f₀ + N₀ z₀).2
  have hsumgraph₁ : (f₁ + N₁ z₁).1 ∈ forcingGraph E6 T alpha := by
    rw [← hX]
    exact (f₁ + N₁ z₁).2

  have hvalue₀ (p : Slab T) :
      ((L z₀).1).1 p = ((f₀ + N₀ z₀).1).1 p := by
    calc
      ((L z₀).1).1 p = f₀.1.1 p +
          PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.principalPart
            (b₀.1 p - 1) ((H₀ + G z₀).1 p) +
          B (b₀.1 p) (b₀.1 p) ((v₀ + Q z₀).1 p) ((v₀ + Q z₀).1 p) := heq₀ p
      _ = ((f₀ + N₀ z₀).1).1 p := by
        change f₀.1.1 p +
          PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.principalPart
            (b₀.1 p - 1) ((H₀ + G z₀).1 p) +
          B (b₀.1 p) (b₀.1 p) ((v₀ + Q z₀).1 p) ((v₀ + Q z₀).1 p) =
          f₀.1.1 p + (N₀ z₀).1.1 p
        rw [hN₀ z₀ hz₀ p, hinv₀ p]
        abel

  have hvalue₁ (p : Slab T) :
      ((L z₁).1).1 p = ((f₁ + N₁ z₁).1).1 p := by
    calc
      ((L z₁).1).1 p = f₁.1.1 p +
          PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.principalPart
            (b₁.1 p - 1) ((H₁ + G z₁).1 p) +
          B (b₁.1 p) (b₁.1 p) ((v₁ + Q z₁).1 p) ((v₁ + Q z₁).1 p) := heq₁ p
      _ = ((f₁ + N₁ z₁).1).1 p := by
        change f₁.1.1 p +
          PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.principalPart
            (b₁.1 p - 1) ((H₁ + G z₁).1 p) +
          B (b₁.1 p) (b₁.1 p) ((v₁ + Q z₁).1 p) ((v₁ + Q z₁).1 p) =
          f₁.1.1 p + (N₁ z₁).1.1 p
        rw [hN₁ z₁ hz₁ p, hinv₁ p]
        abel

  have hPDE₀ : L z₀ = f₀ + N₀ z₀ := by
    apply Subtype.ext
    exact PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality.forcing_jet_eq_of_value_eq
      T alpha (L z₀).1 (f₀ + N₀ z₀).1 hgraph₀ hsumgraph₀ hvalue₀
  have hPDE₁ : L z₁ = f₁ + N₁ z₁ := by
    apply Subtype.ext
    exact PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality.forcing_jet_eq_of_value_eq
      T alpha (L z₁).1 (f₁ + N₁ z₁).1 hgraph₁ hsumgraph₁ hvalue₁

  have hDLapply (z : Y) : D (L z) = z := by
    have hh := congrArg (fun F : Y →L[ℝ] Y => F z) hDL
    simpa using hh
  have hsol₀ : z₀ = D (f₀ + N₀ z₀) := by
    calc
      z₀ = D (L z₀) := (hDLapply z₀).symm
      _ = D (f₀ + N₀ z₀) := congrArg D hPDE₀
  have hsol₁ : z₁ = D (f₁ + N₁ z₁) := by
    calc
      z₁ = D (L z₁) := (hDLapply z₁).symm
      _ = D (f₁ + N₁ z₁) := congrArg D hPDE₁

  let E : ℝ := ‖f₁ - f₀‖ + Ka * ‖a₁ - a₀‖ +
    Kv * ‖v₁ - v₀‖ + Kh * ‖H₁ - H₀‖
  have hE : 0 ≤ E := by
    dsimp [E, Ka, Kv, Kh, abar, vbar, hbar, S]
    positivity
  have hKy : 0 ≤ Ky := by
    dsimp [Ky, abar, vbar, hbar, S]
    positivity
  have hD : 0 ≤ ‖D‖ := norm_nonneg _
  have hsource :
      ‖(f₁ + N₁ z₁) - (f₀ + N₀ z₀)‖ ≤ Ky * ‖z₁ - z₀‖ + E := by
    have hsplit : (f₁ + N₁ z₁) - (f₀ + N₀ z₀) =
        (f₁ - f₀) + (N₁ z₁ - N₀ z₀) := by abel
    calc
      _ = ‖(f₁ - f₀) + (N₁ z₁ - N₀ z₀)‖ := by rw [hsplit]
      _ ≤ ‖f₁ - f₀‖ + ‖N₁ z₁ - N₀ z₀‖ := norm_add_le _ _
      _ ≤ ‖f₁ - f₀‖ +
          (Ky * ‖z₁ - z₀‖ + Ka * ‖a₁ - a₀‖ +
            Kv * ‖v₁ - v₀‖ + Kh * ‖H₁ - H₀‖) :=
        add_le_add (le_refl _) (hNlip z₀ z₁ hz₀ hz₁)
      _ = Ky * ‖z₁ - z₀‖ + E := by dsimp [E]; ring

  have hmain : ‖z₁ - z₀‖ ≤ ‖D‖ * (Ky * ‖z₁ - z₀‖ + E) := by
    have hdiff : z₁ - z₀ = D ((f₁ + N₁ z₁) - (f₀ + N₀ z₀)) := by
      calc
        z₁ - z₀ = D (L z₁) - D (L z₀) := by rw [hDLapply z₁, hDLapply z₀]
        _ = D (L z₁ - L z₀) := by rw [map_sub]
        _ = D ((f₁ + N₁ z₁) - (f₀ + N₀ z₀)) := by rw [hPDE₁, hPDE₀]
    calc
      ‖z₁ - z₀‖ = ‖D ((f₁ + N₁ z₁) - (f₀ + N₀ z₀))‖ := by rw [hdiff]
      _ ≤ ‖D‖ * ‖(f₁ + N₁ z₁) - (f₀ + N₀ z₀)‖ := D.le_opNorm _
      _ ≤ ‖D‖ * (Ky * ‖z₁ - z₀‖ + E) :=
        mul_le_mul_of_nonneg_left hsource hD

  have hcontract' : ‖D‖ * Ky ≤ 1 := le_of_lt hcontract
  have hprod : (‖D‖ * Ky) * ‖z₁ - z₀‖ ≤ ‖z₁ - z₀‖ :=
    calc
      (‖D‖ * Ky) * ‖z₁ - z₀‖ ≤ 1 * ‖z₁ - z₀‖ :=
        mul_le_mul_of_nonneg_right hcontract'
          (show 0 ≤ ‖z₁ - z₀‖ from norm_nonneg _)
      _ = ‖z₁ - z₀‖ := one_mul _
  have habsorbed : (1 - ‖D‖ * Ky) * ‖z₁ - z₀‖ ≤ ‖D‖ * E := by
    nlinarith [hmain]
  have hden : 0 < 1 - ‖D‖ * Ky := by linarith
  change ‖z₁ - z₀‖ ≤ (‖D‖ / (1 - ‖D‖ * Ky)) * E
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hden).2
  nlinarith [habsorbed]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CoupledAffineSolutionStability
