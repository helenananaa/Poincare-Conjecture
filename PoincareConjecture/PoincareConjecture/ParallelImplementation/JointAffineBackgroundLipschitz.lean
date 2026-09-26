import PoincareConjecture.ParallelImplementation.CoupledAffineParabolicFixedPoint
import PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.JointAffineBackgroundLipschitz
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
theorem exists_joint_background_coupled_lipschitz
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
    (hsmall₁ : ‖a₁‖ + ‖P‖ * R ≤ 1 / 2) :
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
    ∃ I₀ I₁ : Y → ForcingJet A T, ∃ N₀ N₁ : Y → X,
      (∀ y, ‖y‖ ≤ R →
        I₀ y ∈ forcingGraph A T alpha ∧ ‖I₀ y‖ ≤ 2 ∧
          (∀ p : Slab T,
            (1 - (a₀ + P y).1 p) * (I₀ y).1 p = 1 ∧
            (I₀ y).1 p * (1 - (a₀ + P y).1 p) = 1)) ∧
      (∀ y, ‖y‖ ≤ R →
        I₁ y ∈ forcingGraph A T alpha ∧ ‖I₁ y‖ ≤ 2 ∧
          (∀ p : Slab T,
            (1 - (a₁ + P y).1 p) * (I₁ y).1 p = 1 ∧
            (I₁ y).1 p * (1 - (a₁ + P y).1 p) = 1)) ∧
      (∀ y, ‖y‖ ≤ R → ∀ p : Slab T,
        (N₀ y).1.1 p =
          PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.principalPart
              ((I₀ y).1 p - 1) ((H₀ + G y).1 p) +
            B ((I₀ y).1 p) ((I₀ y).1 p)
              ((v₀ + Q y).1 p) ((v₀ + Q y).1 p)) ∧
      (∀ y, ‖y‖ ≤ R → ∀ p : Slab T,
        (N₁ y).1.1 p =
          PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.principalPart
              ((I₁ y).1 p - 1) ((H₁ + G y).1 p) +
            B ((I₁ y).1 p) ((I₁ y).1 p)
              ((v₁ + Q y).1 p) ((v₁ + Q y).1 p)) ∧
      (∀ y₀ y₁, ‖y₀‖ ≤ R → ‖y₁‖ ≤ R →
        ‖N₁ y₁ - N₀ y₀‖ ≤
          Ky * ‖y₁ - y₀‖ +
          Ka * ‖a₁ - a₀‖ +
          Kv * ‖v₁ - v₀‖ +
          Kh * ‖H₁ - H₀‖) :=
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
  let oneJet : ForcingJet A T :=
    ((1 : Slab T →ᵇ A), (0 : Pair T →ᵇ A))
  have hOneGraph : oneJet ∈ forcingGraph A T alpha := by
    intro p
    simp [oneJet]
  have haddGraph {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
      (f g : ForcingJet Z T)
      (hf : f ∈ forcingGraph Z T alpha)
      (hg : g ∈ forcingGraph Z T alpha) : f + g ∈ forcingGraph Z T alpha := by
    intro p
    change f.2 p + g.2 p =
      (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        ((f.1 p.1.1 + g.1 p.1.1) - (f.1 p.1.2 + g.1 p.1.2))
    rw [hf p, hg p]
    simp only [smul_add, smul_sub]
    abel
  have hsubGraph {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
      (f g : ForcingJet Z T)
      (hf : f ∈ forcingGraph Z T alpha)
      (hg : g ∈ forcingGraph Z T alpha) : f - g ∈ forcingGraph Z T alpha := by
    intro p
    change f.2 p - g.2 p =
      (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        ((f.1 p.1.1 - g.1 p.1.1) - (f.1 p.1.2 - g.1 p.1.2))
    rw [hf p, hg p]
    simp only [smul_sub]
    abel

  obtain ⟨J, hJspec, hJlip⟩ :=
    @PoincareConjecture.ParallelImplementation.CoherentForcingGraphInverse.exists_coherent_forcing_graph_inverse
      A _ _ _ _ T alpha (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  have hArgGraph (a : ForcingJet A T) (ha : a ∈ forcingGraph A T alpha)
      (y : Y) : a + P y ∈ forcingGraph A T alpha := by
    intro p
    change a.2 p + (P y).2 p =
      (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        (a.1 p.1.1 + (P y).1 p.1.1 - (a.1 p.1.2 + (P y).1 p.1.2))
    rw [ha p, hP y p]
    simp only [smul_add, smul_sub]
    abel
  have hArgNorm (a : ForcingJet A T) (hsmall : ‖a‖ + ‖P‖ * R ≤ 1 / 2)
      (y : Y) (hy : ‖y‖ ≤ R) : ‖a + P y‖ ≤ 1 / 2 := by
    calc
      ‖a + P y‖ ≤ ‖a‖ + ‖P y‖ := norm_add_le _ _
      _ ≤ ‖a‖ + ‖P‖ * ‖y‖ := by
        calc
          ‖a‖ + ‖P y‖ = ‖P y‖ + ‖a‖ := by ring
          _ ≤ ‖P‖ * ‖y‖ + ‖a‖ := add_le_add_left (P.le_opNorm y) ‖a‖
          _ = ‖a‖ + ‖P‖ * ‖y‖ := by ring
      _ ≤ ‖a‖ + ‖P‖ * R := by
        calc
          ‖a‖ + ‖P‖ * ‖y‖ = ‖P‖ * ‖y‖ + ‖a‖ := by ring
          _ ≤ ‖P‖ * R + ‖a‖ :=
            add_le_add_left (mul_le_mul_of_nonneg_left hy (norm_nonneg P)) ‖a‖
          _ = ‖a‖ + ‖P‖ * R := by ring
      _ ≤ 1 / 2 := hsmall
  let InvArg₀ (y : Y) (hy : ‖y‖ ≤ R) :
      {x : ForcingJet A T // x ∈ forcingGraph A T alpha ∧
        ‖x.1‖ ≤ (1 / 2 : ℝ) ∧ ‖x.2‖ ≤ (1 / 2 : ℝ)} :=
    ⟨a₀ + P y, hArgGraph a₀ ha₀ y,
      (norm_fst_le (a₀ + P y)).trans (hArgNorm a₀ hsmall₀ y hy),
      (norm_snd_le (a₀ + P y)).trans (hArgNorm a₀ hsmall₀ y hy)⟩
  let InvArg₁ (y : Y) (hy : ‖y‖ ≤ R) :
      {x : ForcingJet A T // x ∈ forcingGraph A T alpha ∧
        ‖x.1‖ ≤ (1 / 2 : ℝ) ∧ ‖x.2‖ ≤ (1 / 2 : ℝ)} :=
    ⟨a₁ + P y, hArgGraph a₁ ha₁ y,
      (norm_fst_le (a₁ + P y)).trans (hArgNorm a₁ hsmall₁ y hy),
      (norm_snd_le (a₁ + P y)).trans (hArgNorm a₁ hsmall₁ y hy)⟩

  have hzeroBall : ‖(0 : Y)‖ ≤ R := by simpa using hR.le
  let I₀ : Y → ForcingJet A T := fun y =>
    if hy : ‖y‖ ≤ R then J (InvArg₀ y hy) else 0
  let I₁ : Y → ForcingJet A T := fun y =>
    if hy : ‖y‖ ≤ R then J (InvArg₁ y hy) else 0
  have hI₀branch (y : Y) (hy : ‖y‖ ≤ R) : I₀ y = J (InvArg₀ y hy) := by
    simp [I₀, hy]
  have hI₁branch (y : Y) (hy : ‖y‖ ≤ R) : I₁ y = J (InvArg₁ y hy) := by
    simp [I₁, hy]
  have hI₀spec (y : Y) (hy : ‖y‖ ≤ R) :
      I₀ y ∈ forcingGraph A T alpha ∧ ‖I₀ y‖ ≤ 2 ∧
        ∀ p : Slab T,
          (1 - (a₀ + P y).1 p) * (I₀ y).1 p = 1 ∧
          (I₀ y).1 p * (1 - (a₀ + P y).1 p) = 1 := by
    rw [hI₀branch y hy]
    have hs := hJspec (InvArg₀ y hy)
    refine ⟨hs.1, ?_, ?_⟩
    · have hmax :
          max (1 / (1 - (1 / 2 : ℝ)))
            ((1 / (1 - (1 / 2 : ℝ))) ^ 2 * (1 / 2 : ℝ)) ≤ 2 := by norm_num
      exact hs.2.2.trans hmax
    · intro p
      simpa [InvArg₀] using hs.2.1 p
  have hI₁spec (y : Y) (hy : ‖y‖ ≤ R) :
      I₁ y ∈ forcingGraph A T alpha ∧ ‖I₁ y‖ ≤ 2 ∧
        ∀ p : Slab T,
          (1 - (a₁ + P y).1 p) * (I₁ y).1 p = 1 ∧
          (I₁ y).1 p * (1 - (a₁ + P y).1 p) = 1 := by
    rw [hI₁branch y hy]
    have hs := hJspec (InvArg₁ y hy)
    refine ⟨hs.1, ?_, ?_⟩
    · have hmax :
          max (1 / (1 - (1 / 2 : ℝ)))
            ((1 / (1 - (1 / 2 : ℝ))) ^ 2 * (1 / 2 : ℝ)) ≤ 2 := by norm_num
      exact hs.2.2.trans hmax
    · intro p
      simpa [InvArg₁] using hs.2.1 p
  have hI₀lip (y z : Y) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
      ‖I₀ y - I₀ z‖ ≤ (12 * ‖P‖) * ‖y - z‖ := by
    rw [hI₀branch y hy, hI₀branch z hz]
    have harg : (InvArg₀ y hy).1 - (InvArg₀ z hz).1 = P y - P z := by
      change (a₀ + P y) - (a₀ + P z) = P y - P z
      abel
    have hl := hJlip (InvArg₀ y hy) (InvArg₀ z hz)
    have hl' : ‖J (InvArg₀ y hy) - J (InvArg₀ z hz)‖ ≤
        12 * ‖(InvArg₀ y hy).1 - (InvArg₀ z hz).1‖ := by
      convert hl using 1 <;> norm_num
    calc
      ‖J (InvArg₀ y hy) - J (InvArg₀ z hz)‖ ≤
          12 * ‖P y - P z‖ := by rw [← harg]; exact hl'
      _ ≤ 12 * (‖P‖ * ‖y - z‖) :=
        mul_le_mul_of_nonneg_left (by
          rw [← P.map_sub]
          exact P.le_opNorm (y - z)) (by norm_num)
      _ = (12 * ‖P‖) * ‖y - z‖ := by ring
  have hI₁lip (y z : Y) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
      ‖I₁ y - I₁ z‖ ≤ (12 * ‖P‖) * ‖y - z‖ := by
    rw [hI₁branch y hy, hI₁branch z hz]
    have harg : (InvArg₁ y hy).1 - (InvArg₁ z hz).1 = P y - P z := by
      change (a₁ + P y) - (a₁ + P z) = P y - P z
      abel
    have hl := hJlip (InvArg₁ y hy) (InvArg₁ z hz)
    have hl' : ‖J (InvArg₁ y hy) - J (InvArg₁ z hz)‖ ≤
        12 * ‖(InvArg₁ y hy).1 - (InvArg₁ z hz).1‖ := by
      convert hl using 1 <;> norm_num
    calc
      ‖J (InvArg₁ y hy) - J (InvArg₁ z hz)‖ ≤
          12 * ‖P y - P z‖ := by rw [← harg]; exact hl'
      _ ≤ 12 * (‖P‖ * ‖y - z‖) :=
        mul_le_mul_of_nonneg_left (by
          rw [← P.map_sub]
          exact P.le_opNorm (y - z)) (by norm_num)
      _ = (12 * ‖P‖) * ‖y - z‖ := by ring
  have hIcross (y : Y) (hy : ‖y‖ ≤ R) :
      ‖I₁ y - I₀ y‖ ≤ 12 * ‖a₁ - a₀‖ := by
    rw [hI₁branch y hy, hI₀branch y hy]
    have harg : (InvArg₁ y hy).1 - (InvArg₀ y hy).1 = a₁ - a₀ := by
      change (a₁ + P y) - (a₀ + P y) = a₁ - a₀
      abel
    have hl := hJlip (InvArg₁ y hy) (InvArg₀ y hy)
    have hl' : ‖J (InvArg₁ y hy) - J (InvArg₀ y hy)‖ ≤
        12 * ‖(InvArg₁ y hy).1 - (InvArg₀ y hy).1‖ := by
      convert hl using 1 <;> norm_num
    simpa [harg] using hl'

  obtain ⟨Icanon₀, hcanon₀, hcanon₀zero, _⟩ :=
    PoincareConjecture.ParallelImplementation.AffineInverseCorrectionBound.exists_affine_inverse_correction_bound
      T alpha R hR a₀ ha₀ P hP hsmall₀
  obtain ⟨Icanon₁, hcanon₁, hcanon₁zero, _⟩ :=
    PoincareConjecture.ParallelImplementation.AffineInverseCorrectionBound.exists_affine_inverse_correction_bound
      T alpha R hR a₁ ha₁ P hP hsmall₁
  have hI₀zeroEq : I₀ 0 = Icanon₀ 0 := by
    apply PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality.forcing_jet_eq_of_value_eq
      T alpha (I₀ 0) (Icanon₀ 0) (hI₀spec 0 hzeroBall).1 (hcanon₀ 0 hzeroBall).1
    intro p
    have hl : (1 - a₀.1 p) * (Icanon₀ 0).1 p = 1 := by
      simpa [P.map_zero] using ((hcanon₀ 0 hzeroBall).2.2.1 p).1
    have hr : (I₀ 0).1 p * (1 - a₀.1 p) = 1 := by
      simpa [P.map_zero] using ((hI₀spec 0 hzeroBall).2.2 p).2
    calc
      (I₀ 0).1 p = (I₀ 0).1 p * ((1 - a₀.1 p) * (Icanon₀ 0).1 p) := by
        rw [hl, mul_one]
      _ = ((I₀ 0).1 p * (1 - a₀.1 p)) * (Icanon₀ 0).1 p := by rw [mul_assoc]
      _ = (Icanon₀ 0).1 p := by rw [hr, one_mul]
  have hI₁zeroEq : I₁ 0 = Icanon₁ 0 := by
    apply PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality.forcing_jet_eq_of_value_eq
      T alpha (I₁ 0) (Icanon₁ 0) (hI₁spec 0 hzeroBall).1 (hcanon₁ 0 hzeroBall).1
    intro p
    have hl : (1 - a₁.1 p) * (Icanon₁ 0).1 p = 1 := by
      simpa [P.map_zero] using ((hcanon₁ 0 hzeroBall).2.2.1 p).1
    have hr : (I₁ 0).1 p * (1 - a₁.1 p) = 1 := by
      simpa [P.map_zero] using ((hI₁spec 0 hzeroBall).2.2 p).2
    calc
      (I₁ 0).1 p = (I₁ 0).1 p * ((1 - a₁.1 p) * (Icanon₁ 0).1 p) := by
        rw [hl, mul_one]
      _ = ((I₁ 0).1 p * (1 - a₁.1 p)) * (Icanon₁ 0).1 p := by rw [mul_assoc]
      _ = (Icanon₁ 0).1 p := by rw [hr, one_mul]
  have hI₀corrZero : ‖I₀ 0 - oneJet‖ ≤ 4 * ‖a₀‖ := by
    rw [hI₀zeroEq]
    simpa [oneJet] using hcanon₀zero
  have hI₁corrZero : ‖I₁ 0 - oneJet‖ ≤ 4 * ‖a₁‖ := by
    rw [hI₁zeroEq]
    simpa [oneJet] using hcanon₁zero

  obtain ⟨C, hCnorm, hCvalue⟩ :=
    @PoincareConjecture.ParallelImplementation.OperatorHessianContraction.exists_operator_hessian_contraction
      E6 _ _
  obtain ⟨L, hLnorm, hLvalue, hLgraph⟩ :=
    PoincareConjecture.ParallelImplementation.ForcingGraphQuadrilinearLift.exists_forcing_graph_quadrilinear_lift
      (B := B) T alpha

  let cbase₀ : ForcingJet A T := I₀ 0 - oneJet
  let cbase₁ : ForcingJet A T := I₁ 0 - oneJet
  let Jcorr₀ : Y → ForcingJet A T := fun y => I₀ y - I₀ 0
  let Jcorr₁ : Y → ForcingJet A T := fun y => I₁ y - I₁ 0
  have hcbase₀graph : cbase₀ ∈ forcingGraph A T alpha := by
    change I₀ 0 - oneJet ∈ forcingGraph A T alpha
    exact hsubGraph (I₀ 0) oneJet (hI₀spec 0 hzeroBall).1 hOneGraph
  have hcbase₁graph : cbase₁ ∈ forcingGraph A T alpha := by
    change I₁ 0 - oneJet ∈ forcingGraph A T alpha
    exact hsubGraph (I₁ 0) oneJet (hI₁spec 0 hzeroBall).1 hOneGraph
  have hJcorr₀zero : Jcorr₀ 0 = 0 := by simp [Jcorr₀]
  have hJcorr₁zero : Jcorr₁ 0 = 0 := by simp [Jcorr₁]
  have hJcorr₀graph (y : Y) (hy : ‖y‖ ≤ R) :
      Jcorr₀ y ∈ forcingGraph A T alpha := by
    change I₀ y - I₀ 0 ∈ forcingGraph A T alpha
    exact hsubGraph (I₀ y) (I₀ 0) (hI₀spec y hy).1 (hI₀spec 0 hzeroBall).1
  have hJcorr₁graph (y : Y) (hy : ‖y‖ ≤ R) :
      Jcorr₁ y ∈ forcingGraph A T alpha := by
    change I₁ y - I₁ 0 ∈ forcingGraph A T alpha
    exact hsubGraph (I₁ y) (I₁ 0) (hI₁spec y hy).1 (hI₁spec 0 hzeroBall).1
  have hJcorr₀lip (y z : Y) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
      ‖Jcorr₀ y - Jcorr₀ z‖ ≤ (12 * ‖P‖) * ‖y - z‖ := by
    have heq : Jcorr₀ y - Jcorr₀ z = I₀ y - I₀ z := by
      dsimp [Jcorr₀]
      abel
    rw [heq]
    exact hI₀lip y z hy hz
  have hJcorr₁lip (y z : Y) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
      ‖Jcorr₁ y - Jcorr₁ z‖ ≤ (12 * ‖P‖) * ‖y - z‖ := by
    have heq : Jcorr₁ y - Jcorr₁ z = I₁ y - I₁ z := by
      dsimp [Jcorr₁]
      abel
    rw [heq]
    exact hI₁lip y z hy hz
  have hcbase₀norm : ‖cbase₀‖ ≤ 4 * ‖a₀‖ := by simpa [cbase₀] using hI₀corrZero
  have hcbase₁norm : ‖cbase₁‖ ≤ 4 * ‖a₁‖ := by simpa [cbase₁] using hI₁corrZero
  have hcorr₀jet (y : Y) : cbase₀ + Jcorr₀ y = I₀ y - oneJet := by
    dsimp [cbase₀, Jcorr₀]
    abel
  have hcorr₁jet (y : Y) : cbase₁ + Jcorr₁ y = I₁ y - oneJet := by
    dsimp [cbase₁, Jcorr₁]
    abel

  obtain ⟨NH₀, hNH₀coord, _, hNH₀lip⟩ :=
    PoincareConjecture.ParallelImplementation.AffineForcingGraphBilinearProduct.exists_affine_forcing_bilinear_product
      T alpha R (12 * ‖P‖) hR (by positivity) X hX C cbase₀ H₀
      hcbase₀graph hH₀ Jcorr₀ hJcorr₀zero hJcorr₀graph hJcorr₀lip G hG
  obtain ⟨NH₁, hNH₁coord, _, hNH₁lip⟩ :=
    PoincareConjecture.ParallelImplementation.AffineForcingGraphBilinearProduct.exists_affine_forcing_bilinear_product
      T alpha R (12 * ‖P‖) hR (by positivity) X hX C cbase₁ H₁
      hcbase₁graph hH₁ Jcorr₁ hJcorr₁zero hJcorr₁graph hJcorr₁lip G hG

  have hVsum₀ (y : Y) : v₀ + Q y ∈ forcingGraph V T alpha :=
    haddGraph v₀ (Q y) hv₀ (hQ y)
  have hVsum₁ (y : Y) : v₁ + Q y ∈ forcingGraph V T alpha :=
    haddGraph v₁ (Q y) hv₁ (hQ y)
  let Grad₀ : Y → X := fun y =>
    if hy : ‖y‖ ≤ R then
      ⟨L (I₀ y) (I₀ y) (v₀ + Q y) (v₀ + Q y), by
        change L (I₀ y) (I₀ y) (v₀ + Q y) (v₀ + Q y) ∈
          (X : Set (ForcingJet E6 T))
        rw [hX]
        exact hLgraph (I₀ y) (hI₀spec y hy).1 (I₀ y) (hI₀spec y hy).1
          (v₀ + Q y) (hVsum₀ y) (v₀ + Q y) (hVsum₀ y)⟩
    else 0
  let Grad₁ : Y → X := fun y =>
    if hy : ‖y‖ ≤ R then
      ⟨L (I₁ y) (I₁ y) (v₁ + Q y) (v₁ + Q y), by
        change L (I₁ y) (I₁ y) (v₁ + Q y) (v₁ + Q y) ∈
          (X : Set (ForcingJet E6 T))
        rw [hX]
        exact hLgraph (I₁ y) (hI₁spec y hy).1 (I₁ y) (hI₁spec y hy).1
          (v₁ + Q y) (hVsum₁ y) (v₁ + Q y) (hVsum₁ y)⟩
    else 0
  have hGrad₀branch (y : Y) (hy : ‖y‖ ≤ R) :
      (Grad₀ y : ForcingJet E6 T) = L (I₀ y) (I₀ y) (v₀ + Q y) (v₀ + Q y) := by
    simp [Grad₀, hy]
  have hGrad₁branch (y : Y) (hy : ‖y‖ ≤ R) :
      (Grad₁ y : ForcingJet E6 T) = L (I₁ y) (I₁ y) (v₁ + Q y) (v₁ + Q y) := by
    simp [Grad₁, hy]
  let N₀ : Y → X := fun y => NH₀ y + Grad₀ y
  let N₁ : Y → X := fun y => NH₁ y + Grad₁ y

  have hCprincipal (A0 : A) (H0 : H) :
      C A0 H0 =
        PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.principalPart A0 H0 := by
    simpa [PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.principalPart,
      PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.spatialUnit] using
        hCvalue A0 H0
  have hNH₀coord' (y : Y) (hy : ‖y‖ ≤ R) (p : Slab T) :
      (NH₀ y).1.1 p = C ((I₀ y - oneJet).1 p) ((H₀ + G y).1 p) := by
    rw [hNH₀coord y hy p]
    have hh := congrArg (fun x : ForcingJet A T => x.1 p) (hcorr₀jet y)
    exact congrArg (fun a : A => C a ((H₀ + G y).1 p))
      (by simpa using hh)
  have hNH₁coord' (y : Y) (hy : ‖y‖ ≤ R) (p : Slab T) :
      (NH₁ y).1.1 p = C ((I₁ y - oneJet).1 p) ((H₁ + G y).1 p) := by
    rw [hNH₁coord y hy p]
    have hh := congrArg (fun x : ForcingJet A T => x.1 p) (hcorr₁jet y)
    exact congrArg (fun a : A => C a ((H₁ + G y).1 p))
      (by simpa using hh)
  have hGrad₀coord (y : Y) (hy : ‖y‖ ≤ R) (p : Slab T) :
      (Grad₀ y).1.1 p = B ((I₀ y).1 p) ((I₀ y).1 p)
        ((v₀ + Q y).1 p) ((v₀ + Q y).1 p) := by
    change ((Grad₀ y : ForcingJet E6 T).1 p) = _
    rw [hGrad₀branch y hy]
    exact hLvalue (I₀ y) (I₀ y) (v₀ + Q y) (v₀ + Q y) p
  have hGrad₁coord (y : Y) (hy : ‖y‖ ≤ R) (p : Slab T) :
      (Grad₁ y).1.1 p = B ((I₁ y).1 p) ((I₁ y).1 p)
        ((v₁ + Q y).1 p) ((v₁ + Q y).1 p) := by
    change ((Grad₁ y : ForcingJet E6 T).1 p) = _
    rw [hGrad₁branch y hy]
    exact hLvalue (I₁ y) (I₁ y) (v₁ + Q y) (v₁ + Q y) p

  have habar₀ : ‖a₀‖ ≤ abar := by dsimp [abar]; exact le_max_left _ _
  have habar₁ : ‖a₁‖ ≤ abar := by dsimp [abar]; exact le_max_right _ _
  have hvbar₀ : ‖v₀‖ ≤ vbar := by dsimp [vbar]; exact le_max_left _ _
  have hvbar₁ : ‖v₁‖ ≤ vbar := by dsimp [vbar]; exact le_max_right _ _
  have hhbar₀ : ‖H₀‖ ≤ hbar := by dsimp [hbar]; exact le_max_left _ _
  have hhbar₁ : ‖H₁‖ ≤ hbar := by dsimp [hbar]; exact le_max_right _ _
  have hSnonneg : 0 ≤ S := by dsimp [S]; positivity
  have hRnonneg : 0 ≤ R := hR.le
  have hKnonneg : 0 ≤ 12 * ‖P‖ := by positivity
  have hV₀norm (y : Y) (hy : ‖y‖ ≤ R) : ‖v₀ + Q y‖ ≤ S := by
    dsimp [S]
    calc
      ‖v₀ + Q y‖ ≤ ‖v₀‖ + ‖Q y‖ := norm_add_le _ _
      _ ≤ ‖v₀‖ + ‖Q‖ * R := by
        gcongr
        calc
          ‖Q y‖ ≤ ‖Q‖ * ‖y‖ := Q.le_opNorm y
          _ ≤ ‖Q‖ * R := mul_le_mul_of_nonneg_left hy (norm_nonneg _)
      _ ≤ vbar + ‖Q‖ * R := by gcongr
  have hV₁norm (y : Y) (hy : ‖y‖ ≤ R) : ‖v₁ + Q y‖ ≤ S := by
    dsimp [S]
    calc
      ‖v₁ + Q y‖ ≤ ‖v₁‖ + ‖Q y‖ := norm_add_le _ _
      _ ≤ ‖v₁‖ + ‖Q‖ * R := by
        gcongr
        calc
          ‖Q y‖ ≤ ‖Q‖ * ‖y‖ := Q.le_opNorm y
          _ ≤ ‖Q‖ * R := mul_le_mul_of_nonneg_left hy (norm_nonneg _)
      _ ≤ vbar + ‖Q‖ * R := by gcongr

  have hcbase₀abar : ‖cbase₀‖ ≤ 4 * abar := by
    calc
      ‖cbase₀‖ ≤ 4 * ‖a₀‖ := hcbase₀norm
      _ ≤ 4 * abar := by gcongr
  have hcbase₁abar : ‖cbase₁‖ ≤ 4 * abar := by
    calc
      ‖cbase₁‖ ≤ 4 * ‖a₁‖ := hcbase₁norm
      _ ≤ 4 * abar := by gcongr

  let Hcoef : ℝ :=
    18 * (12 * ‖P‖ * (hbar + ‖G‖ * R) +
      (4 * abar + 12 * ‖P‖ * R) * ‖G‖)
  let Gcoef : ℝ := 384 * ‖B‖ * ‖P‖ * S ^ 2 + 64 * ‖B‖ * ‖Q‖ * S

  have hinner₀ :
      12 * ‖P‖ * (‖H₀‖ + ‖G‖ * R) +
        (‖cbase₀‖ + 12 * ‖P‖ * R) * ‖G‖ ≤
      12 * ‖P‖ * (hbar + ‖G‖ * R) +
        (4 * abar + 12 * ‖P‖ * R) * ‖G‖ := by
    gcongr
  have hinner₁ :
      12 * ‖P‖ * (‖H₁‖ + ‖G‖ * R) +
        (‖cbase₁‖ + 12 * ‖P‖ * R) * ‖G‖ ≤
      12 * ‖P‖ * (hbar + ‖G‖ * R) +
        (4 * abar + 12 * ‖P‖ * R) * ‖G‖ := by
    gcongr
  have hinner₀nonneg :
      0 ≤ 12 * ‖P‖ * (‖H₀‖ + ‖G‖ * R) +
        (‖cbase₀‖ + 12 * ‖P‖ * R) * ‖G‖ := by positivity
  have hinner₁nonneg :
      0 ≤ 12 * ‖P‖ * (‖H₁‖ + ‖G‖ * R) +
        (‖cbase₁‖ + 12 * ‖P‖ * R) * ‖G‖ := by positivity
  have htwoC : 2 * ‖C‖ ≤ 18 := by nlinarith [hCnorm]
  have hHsame₀ (y z : Y) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
      ‖NH₀ y - NH₀ z‖ ≤ Hcoef * ‖y - z‖ := by
    calc
      ‖NH₀ y - NH₀ z‖ ≤
          (2 * ‖C‖ *
            (12 * ‖P‖ * (‖H₀‖ + ‖G‖ * R) +
              (‖cbase₀‖ + 12 * ‖P‖ * R) * ‖G‖)) * ‖y - z‖ := hNH₀lip y z hy hz
      _ ≤ (18 *
          (12 * ‖P‖ * (hbar + ‖G‖ * R) +
            (4 * abar + 12 * ‖P‖ * R) * ‖G‖)) * ‖y - z‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        calc
          2 * ‖C‖ *
              (12 * ‖P‖ * (‖H₀‖ + ‖G‖ * R) +
                (‖cbase₀‖ + 12 * ‖P‖ * R) * ‖G‖) ≤
            18 * (12 * ‖P‖ * (‖H₀‖ + ‖G‖ * R) +
              (‖cbase₀‖ + 12 * ‖P‖ * R) * ‖G‖) :=
                mul_le_mul_of_nonneg_right htwoC hinner₀nonneg
          _ ≤ 18 * (12 * ‖P‖ * (hbar + ‖G‖ * R) +
              (4 * abar + 12 * ‖P‖ * R) * ‖G‖) :=
                mul_le_mul_of_nonneg_left hinner₀ (by norm_num)
      _ = Hcoef * ‖y - z‖ := by simp [Hcoef]
  have hHsame₁ (y z : Y) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
      ‖NH₁ y - NH₁ z‖ ≤ Hcoef * ‖y - z‖ := by
    calc
      ‖NH₁ y - NH₁ z‖ ≤
          (2 * ‖C‖ *
            (12 * ‖P‖ * (‖H₁‖ + ‖G‖ * R) +
              (‖cbase₁‖ + 12 * ‖P‖ * R) * ‖G‖)) * ‖y - z‖ := hNH₁lip y z hy hz
      _ ≤ (18 *
          (12 * ‖P‖ * (hbar + ‖G‖ * R) +
            (4 * abar + 12 * ‖P‖ * R) * ‖G‖)) * ‖y - z‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        calc
          2 * ‖C‖ *
              (12 * ‖P‖ * (‖H₁‖ + ‖G‖ * R) +
                (‖cbase₁‖ + 12 * ‖P‖ * R) * ‖G‖) ≤
            18 * (12 * ‖P‖ * (‖H₁‖ + ‖G‖ * R) +
              (‖cbase₁‖ + 12 * ‖P‖ * R) * ‖G‖) :=
                mul_le_mul_of_nonneg_right htwoC hinner₁nonneg
          _ ≤ 18 * (12 * ‖P‖ * (hbar + ‖G‖ * R) +
              (4 * abar + 12 * ‖P‖ * R) * ‖G‖) :=
                mul_le_mul_of_nonneg_left hinner₁ (by norm_num)
      _ = Hcoef * ‖y - z‖ := by simp [Hcoef]

  have hGradSame₀ (y z : Y) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
      ‖Grad₀ y - Grad₀ z‖ ≤ Gcoef * ‖y - z‖ := by
    change ‖(Grad₀ y : ForcingJet E6 T) - (Grad₀ z : ForcingJet E6 T)‖ ≤ _
    rw [hGrad₀branch y hy, hGrad₀branch z hz]
    let Sj : ℝ := ‖v₀‖ + ‖Q‖ * R
    have hSj : Sj ≤ S := by dsimp [Sj, S]; gcongr
    have hraw :=
      PoincareConjecture.ParallelImplementation.AffineQuadrilinearEstimate.affine_quadrilinear_lipschitz
        (B := L) (I := I₀) (Q := Q) (v0 := v₀) (M := 2)
        (K := 12 * ‖P‖) (R := R) (by norm_num) hKnonneg hR
        (fun x hx => (hI₀spec x hx).2.1) (fun x w hx hw => hI₀lip x w hx hw) y z hy hz
    have hraw' :
        ‖L (I₀ y) (I₀ y) (v₀ + Q y) (v₀ + Q y) -
          L (I₀ z) (I₀ z) (v₀ + Q z) (v₀ + Q z)‖ ≤
        ‖L‖ * (48 * ‖P‖ * Sj ^ 2 + 8 * ‖Q‖ * Sj) * ‖y - z‖ := by
      convert hraw using 1 <;> ring
    have hcoef : ‖L‖ * (48 * ‖P‖ * Sj ^ 2 + 8 * ‖Q‖ * Sj) ≤ Gcoef := by
      calc
        ‖L‖ * (48 * ‖P‖ * Sj ^ 2 + 8 * ‖Q‖ * Sj) ≤
            (8 * ‖B‖) * (48 * ‖P‖ * Sj ^ 2 + 8 * ‖Q‖ * Sj) :=
              mul_le_mul_of_nonneg_right hLnorm (by positivity)
        _ ≤ (8 * ‖B‖) * (48 * ‖P‖ * S ^ 2 + 8 * ‖Q‖ * S) := by
          gcongr
        _ = Gcoef := by dsimp [Gcoef]; ring
    calc
      ‖L (I₀ y) (I₀ y) (v₀ + Q y) (v₀ + Q y) -
        L (I₀ z) (I₀ z) (v₀ + Q z) (v₀ + Q z)‖ ≤
          ‖L‖ * (48 * ‖P‖ * Sj ^ 2 + 8 * ‖Q‖ * Sj) * ‖y - z‖ := hraw'
      _ ≤ Gcoef * ‖y - z‖ := mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
  have hGradSame₁ (y z : Y) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
      ‖Grad₁ y - Grad₁ z‖ ≤ Gcoef * ‖y - z‖ := by
    change ‖(Grad₁ y : ForcingJet E6 T) - (Grad₁ z : ForcingJet E6 T)‖ ≤ _
    rw [hGrad₁branch y hy, hGrad₁branch z hz]
    let Sj : ℝ := ‖v₁‖ + ‖Q‖ * R
    have hSj : Sj ≤ S := by dsimp [Sj, S]; gcongr
    have hraw :=
      PoincareConjecture.ParallelImplementation.AffineQuadrilinearEstimate.affine_quadrilinear_lipschitz
        (B := L) (I := I₁) (Q := Q) (v0 := v₁) (M := 2)
        (K := 12 * ‖P‖) (R := R) (by norm_num) hKnonneg hR
        (fun x hx => (hI₁spec x hx).2.1) (fun x w hx hw => hI₁lip x w hx hw) y z hy hz
    have hraw' :
        ‖L (I₁ y) (I₁ y) (v₁ + Q y) (v₁ + Q y) -
          L (I₁ z) (I₁ z) (v₁ + Q z) (v₁ + Q z)‖ ≤
        ‖L‖ * (48 * ‖P‖ * Sj ^ 2 + 8 * ‖Q‖ * Sj) * ‖y - z‖ := by
      convert hraw using 1 <;> ring
    have hcoef : ‖L‖ * (48 * ‖P‖ * Sj ^ 2 + 8 * ‖Q‖ * Sj) ≤ Gcoef := by
      calc
        ‖L‖ * (48 * ‖P‖ * Sj ^ 2 + 8 * ‖Q‖ * Sj) ≤
            (8 * ‖B‖) * (48 * ‖P‖ * Sj ^ 2 + 8 * ‖Q‖ * Sj) :=
              mul_le_mul_of_nonneg_right hLnorm (by positivity)
        _ ≤ (8 * ‖B‖) * (48 * ‖P‖ * S ^ 2 + 8 * ‖Q‖ * S) := by
          gcongr
        _ = Gcoef := by dsimp [Gcoef]; ring
    calc
      ‖L (I₁ y) (I₁ y) (v₁ + Q y) (v₁ + Q y) -
        L (I₁ z) (I₁ z) (v₁ + Q z) (v₁ + Q z)‖ ≤
          ‖L‖ * (48 * ‖P‖ * Sj ^ 2 + 8 * ‖Q‖ * Sj) * ‖y - z‖ := hraw'
      _ ≤ Gcoef * ‖y - z‖ := mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
  have hSame₀ (y z : Y) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
      ‖N₀ y - N₀ z‖ ≤ (Hcoef + Gcoef) * ‖y - z‖ := by
    calc
      ‖N₀ y - N₀ z‖ = ‖(NH₀ y - NH₀ z) + (Grad₀ y - Grad₀ z)‖ := by
        congr 1
        dsimp [N₀]
        abel
      _ ≤ ‖NH₀ y - NH₀ z‖ + ‖Grad₀ y - Grad₀ z‖ := norm_add_le _ _
      _ ≤ Hcoef * ‖y - z‖ + Gcoef * ‖y - z‖ :=
        add_le_add (hHsame₀ y z hy hz) (hGradSame₀ y z hy hz)
      _ = (Hcoef + Gcoef) * ‖y - z‖ := by ring
  have hSame₁ (y z : Y) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
      ‖N₁ y - N₁ z‖ ≤ (Hcoef + Gcoef) * ‖y - z‖ := by
    calc
      ‖N₁ y - N₁ z‖ = ‖(NH₁ y - NH₁ z) + (Grad₁ y - Grad₁ z)‖ := by
        congr 1
        dsimp [N₁]
        abel
      _ ≤ ‖NH₁ y - NH₁ z‖ + ‖Grad₁ y - Grad₁ z‖ := norm_add_le _ _
      _ ≤ Hcoef * ‖y - z‖ + Gcoef * ‖y - z‖ :=
        add_le_add (hHsame₁ y z hy hz) (hGradSame₁ y z hy hz)
      _ = (Hcoef + Gcoef) * ‖y - z‖ := by ring

  have hHsumGraph₀ (y : Y) : H₀ + G y ∈ forcingGraph H T alpha :=
    haddGraph H₀ (G y) hH₀ (hG y)
  have hHsumGraph₁ (y : Y) : H₁ + G y ∈ forcingGraph H T alpha :=
    haddGraph H₁ (G y) hH₁ (hG y)
  have hNH₀mem (y : Y) : (NH₀ y : ForcingJet E6 T) ∈ forcingGraph E6 T alpha := by
    rw [← hX]
    exact (NH₀ y).property
  have hNH₁mem (y : Y) : (NH₁ y : ForcingJet E6 T) ∈ forcingGraph E6 T alpha := by
    rw [← hX]
    exact (NH₁ y).property

  have hCrossHess (y : Y) (hy : ‖y‖ ≤ R) :
      ‖NH₁ y - NH₀ y‖ ≤
        216 * (hbar + ‖G‖ * R) * ‖a₁ - a₀‖ +
          18 * (4 * abar + 12 * ‖P‖ * R) * ‖H₁ - H₀‖ := by
    let c₀ : ForcingJet A T := I₀ y - oneJet
    let c₁ : ForcingJet A T := I₁ y - oneJet
    let cd : ForcingJet A T := c₁ - c₀
    let u₀ : ForcingJet H T := H₀ + G y
    let u₁ : ForcingJet H T := H₁ + G y
    have hc₀graph : c₀ ∈ forcingGraph A T alpha :=
      hsubGraph (I₀ y) oneJet (hI₀spec y hy).1 hOneGraph
    have hc₁graph : c₁ ∈ forcingGraph A T alpha :=
      hsubGraph (I₁ y) oneJet (hI₁spec y hy).1 hOneGraph
    have hcdgraph : cd ∈ forcingGraph A T alpha := by
      change c₁ - c₀ ∈ forcingGraph A T alpha
      exact hsubGraph c₁ c₀ hc₁graph hc₀graph
    have hu₀graph : u₀ ∈ forcingGraph H T alpha := hHsumGraph₀ y
    have hu₁graph : u₁ ∈ forcingGraph H T alpha := hHsumGraph₁ y
    have hudgraph : u₁ - u₀ ∈ forcingGraph H T alpha :=
      hsubGraph u₁ u₀ hu₁graph hu₀graph
    obtain ⟨M₁, hM₁norm, hM₁value, _, hM₁graph⟩ :=
      PoincareConjecture.ParallelImplementation.ForcingGraphBilinearProduct.exists_forcing_bilinear_product
        (B := C) T alpha c₁ hc₁graph
    obtain ⟨Md, hMdNorm, hMdvalue, _, hMdgraph⟩ :=
      PoincareConjecture.ParallelImplementation.ForcingGraphBilinearProduct.exists_forcing_bilinear_product
        (B := C) T alpha cd hcdgraph
    let U : ForcingJet E6 T := M₁ (u₁ - u₀)
    let Wd : ForcingJet E6 T := Md u₀
    have hUgraph : U ∈ forcingGraph E6 T alpha := by
      exact hM₁graph (u₁ - u₀) hudgraph
    have hWdgraph : Wd ∈ forcingGraph E6 T alpha := by
      exact hMdgraph u₀ hu₀graph
    have hleftGraph :
        ((NH₁ y : X) : ForcingJet E6 T) - (NH₀ y : ForcingJet E6 T) ∈
          forcingGraph E6 T alpha := hsubGraph _ _ (hNH₁mem y) (hNH₀mem y)
    have hrightGraph : U + Wd ∈ forcingGraph E6 T alpha :=
      haddGraph U Wd hUgraph hWdgraph
    have heq :
        ((NH₁ y : X) : ForcingJet E6 T) - (NH₀ y : ForcingJet E6 T) = U + Wd := by
      apply PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality.forcing_jet_eq_of_value_eq
        T alpha _ _ hleftGraph hrightGraph
      intro p
      change (NH₁ y).1.1 p - (NH₀ y).1.1 p = (U + Wd).1 p
      rw [hNH₁coord' y hy p, hNH₀coord' y hy p]
      change C (c₁.1 p) (u₁.1 p) - C (c₀.1 p) (u₀.1 p) =
        (M₁ (u₁ - u₀)).1 p + (Md u₀).1 p
      rw [hM₁value (u₁ - u₀) p, hMdvalue u₀ p]
      change C (c₁.1 p) (u₁.1 p) - C (c₀.1 p) (u₀.1 p) =
        C (c₁.1 p) ((u₁ - u₀).1 p) + C (cd.1 p) (u₀.1 p)
      have hcdval : cd.1 p = c₁.1 p - c₀.1 p := by
        simp [cd, c₁, c₀, BoundedContinuousFunction.sub_apply]
      rw [hcdval]
      calc
        C (c₁.1 p) (u₁.1 p) - C (c₀.1 p) (u₀.1 p) =
            (C (c₁.1 p) (u₁.1 p) - C (c₁.1 p) (u₀.1 p)) +
              (C (c₁.1 p) (u₀.1 p) - C (c₀.1 p) (u₀.1 p)) := by abel
        _ = C (c₁.1 p) ((u₁ - u₀).1 p) +
              C (c₁.1 p - c₀.1 p) (u₀.1 p) := by
          rw [← map_sub, ← C.map_sub₂]
          rfl
    have hc₁bound : ‖c₁‖ ≤ 4 * abar + 12 * ‖P‖ * R := by
      have hsplit : I₁ y - oneJet = (I₁ y - I₁ 0) + (I₁ 0 - oneJet) := by abel
      change ‖I₁ y - oneJet‖ ≤ 4 * abar + 12 * ‖P‖ * R
      rw [hsplit]
      calc
        ‖(I₁ y - I₁ 0) + (I₁ 0 - oneJet)‖ ≤
            ‖I₁ y - I₁ 0‖ + ‖I₁ 0 - oneJet‖ := norm_add_le _ _
        _ ≤ 12 * ‖P‖ * R + 4 * abar := by
          apply add_le_add
          · calc
              ‖I₁ y - I₁ 0‖ ≤ (12 * ‖P‖) * ‖y - 0‖ := hI₁lip y 0 hy hzeroBall
              _ ≤ (12 * ‖P‖) * R := by
                simpa using mul_le_mul_of_nonneg_left hy (by positivity : 0 ≤ 12 * ‖P‖)
              _ = 12 * ‖P‖ * R := by ring
          · exact hcbase₁abar
        _ = 4 * abar + 12 * ‖P‖ * R := by ring
    have hcdvalNorm : ‖cd‖ ≤ 12 * ‖a₁ - a₀‖ := by
      have heq : cd = I₁ y - I₀ y := by
        dsimp [cd, c₁, c₀]
        abel
      rw [heq]
      exact hIcross y hy
    have hu₀bound : ‖u₀‖ ≤ hbar + ‖G‖ * R := by
      dsimp [u₀]
      calc
        ‖H₀ + G y‖ ≤ ‖H₀‖ + ‖G y‖ := norm_add_le _ _
        _ ≤ hbar + ‖G‖ * R := by
          have hGy : ‖G y‖ ≤ ‖G‖ * R := by
            calc
              ‖G y‖ ≤ ‖G‖ * ‖y‖ := G.le_opNorm y
              _ ≤ ‖G‖ * R := mul_le_mul_of_nonneg_left hy (norm_nonneg _)
          gcongr
    have hudnorm : ‖u₁ - u₀‖ = ‖H₁ - H₀‖ := by
      congr 1
      dsimp [u₁, u₀]
      abel
    have htermH :
        (2 * ‖C‖ * ‖c₁‖) * ‖H₁ - H₀‖ ≤
          18 * (4 * abar + 12 * ‖P‖ * R) * ‖H₁ - H₀‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      calc
        2 * ‖C‖ * ‖c₁‖ ≤ 18 * ‖c₁‖ :=
          mul_le_mul_of_nonneg_right htwoC (norm_nonneg _)
        _ ≤ 18 * (4 * abar + 12 * ‖P‖ * R) :=
          mul_le_mul_of_nonneg_left hc₁bound (by norm_num)
    have htermA :
        (2 * ‖C‖ * ‖cd‖) * ‖u₀‖ ≤
          216 * (hbar + ‖G‖ * R) * ‖a₁ - a₀‖ := by
      calc
        (2 * ‖C‖ * ‖cd‖) * ‖u₀‖ ≤
            (18 * (12 * ‖a₁ - a₀‖)) * (hbar + ‖G‖ * R) := by
          calc
            (2 * ‖C‖ * ‖cd‖) * ‖u₀‖ ≤
                (18 * ‖cd‖) * ‖u₀‖ := by
              apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
              exact mul_le_mul_of_nonneg_right htwoC (norm_nonneg _)
            _ ≤ (18 * (12 * ‖a₁ - a₀‖)) * ‖u₀‖ := by
              apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
              exact mul_le_mul_of_nonneg_left hcdvalNorm (by norm_num)
            _ ≤ (18 * (12 * ‖a₁ - a₀‖)) * (hbar + ‖G‖ * R) :=
              mul_le_mul_of_nonneg_left hu₀bound (by positivity)
        _ = 216 * (hbar + ‖G‖ * R) * ‖a₁ - a₀‖ := by ring
    have hnormEq : ‖NH₁ y - NH₀ y‖ = ‖U + Wd‖ := by
      change ‖((NH₁ y : X) : ForcingJet E6 T) -
        ((NH₀ y : X) : ForcingJet E6 T)‖ = _
      exact congrArg norm heq
    rw [hnormEq]
    calc
      ‖U + Wd‖ ≤ ‖U‖ + ‖Wd‖ := norm_add_le _ _
      _ ≤ (2 * ‖C‖ * ‖c₁‖) * ‖u₁ - u₀‖ +
            (2 * ‖C‖ * ‖cd‖) * ‖u₀‖ := by
        apply add_le_add
        · calc
            ‖U‖ ≤ ‖M₁‖ * ‖u₁ - u₀‖ := M₁.le_opNorm _
            _ ≤ (2 * ‖C‖ * ‖c₁‖) * ‖u₁ - u₀‖ := by
              exact mul_le_mul_of_nonneg_right hM₁norm (norm_nonneg _)
        · calc
            ‖Wd‖ ≤ ‖Md‖ * ‖u₀‖ := Md.le_opNorm _
            _ ≤ (2 * ‖C‖ * ‖cd‖) * ‖u₀‖ := by
              exact mul_le_mul_of_nonneg_right hMdNorm (norm_nonneg _)
      _ ≤ 18 * (4 * abar + 12 * ‖P‖ * R) * ‖H₁ - H₀‖ +
            216 * (hbar + ‖G‖ * R) * ‖a₁ - a₀‖ := by
        rw [hudnorm]
        exact add_le_add htermH htermA
      _ = 216 * (hbar + ‖G‖ * R) * ‖a₁ - a₀‖ +
            18 * (4 * abar + 12 * ‖P‖ * R) * ‖H₁ - H₀‖ := by ring

  have hLpoint (x y : ForcingJet A T) (u w : ForcingJet V T) :
      ‖L x y u w‖ ≤ ‖L‖ * ‖x‖ * ‖y‖ * ‖u‖ * ‖w‖ := by
    calc
      ‖L x y u w‖ ≤ ‖L x y u‖ * ‖w‖ := (L x y u).le_opNorm w
      _ ≤ (‖L x y‖ * ‖u‖) * ‖w‖ := by
        gcongr
        exact (L x y).le_opNorm u
      _ ≤ ((‖L x‖ * ‖y‖) * ‖u‖) * ‖w‖ := by
        gcongr
        exact (L x).le_opNorm y
      _ ≤ (((‖L‖ * ‖x‖) * ‖y‖) * ‖u‖) * ‖w‖ := by
        gcongr
        exact L.le_opNorm x

  have hCrossGrad (y : Y) (hy : ‖y‖ ≤ R) :
      ‖Grad₁ y - Grad₀ y‖ ≤
        384 * ‖B‖ * S ^ 2 * ‖a₁ - a₀‖ + 64 * ‖B‖ * S * ‖v₁ - v₀‖ := by
    change ‖(Grad₁ y : ForcingJet E6 T) - (Grad₀ y : ForcingJet E6 T)‖ ≤ _
    rw [hGrad₁branch y hy, hGrad₀branch y hy]
    let dI : ForcingJet A T := I₁ y - I₀ y
    let u₀ : ForcingJet V T := v₀ + Q y
    let u₁ : ForcingJet V T := v₁ + Q y
    have huDiff : ‖u₁ - u₀‖ ≤ ‖v₁ - v₀‖ := by
      have heq : u₁ - u₀ = v₁ - v₀ := by
        dsimp [u₁, u₀]
        abel
      rw [heq]
    have hIsub : ‖dI‖ ≤ 12 * ‖a₁ - a₀‖ := by
      dsimp [dI]
      exact hIcross y hy
    have hu₀ : ‖u₀‖ ≤ S := by simpa [u₀] using hV₀norm y hy
    have hu₁ : ‖u₁‖ ≤ S := by simpa [u₁] using hV₁norm y hy
    have hsplit :
        L (I₁ y) (I₁ y) u₁ u₁ - L (I₀ y) (I₀ y) u₀ u₀ =
          L dI (I₁ y) u₁ u₁ + L (I₀ y) dI u₁ u₁ +
            L (I₀ y) (I₀ y) (u₁ - u₀) u₁ +
              L (I₀ y) (I₀ y) u₀ (u₁ - u₀) := by
      simp only [dI, map_sub, sub_apply]
      abel
    have he1 : ‖L dI (I₁ y) u₁ u₁‖ ≤
        (8 * ‖B‖) * (12 * ‖a₁ - a₀‖) * 2 * S * S := by
      calc
        ‖L dI (I₁ y) u₁ u₁‖ ≤ ‖L‖ * ‖dI‖ * ‖I₁ y‖ * ‖u₁‖ * ‖u₁‖ :=
          hLpoint _ _ _ _
        _ ≤ (8 * ‖B‖) * (12 * ‖a₁ - a₀‖) * 2 * S * S := by
          gcongr
          all_goals first
            | exact hLnorm
            | exact hIsub
            | exact (hI₁spec y hy).2.1
            | exact hu₁
    have he2 : ‖L (I₀ y) dI u₁ u₁‖ ≤
        (8 * ‖B‖) * 2 * (12 * ‖a₁ - a₀‖) * S * S := by
      calc
        ‖L (I₀ y) dI u₁ u₁‖ ≤ ‖L‖ * ‖I₀ y‖ * ‖dI‖ * ‖u₁‖ * ‖u₁‖ :=
          hLpoint _ _ _ _
        _ ≤ (8 * ‖B‖) * 2 * (12 * ‖a₁ - a₀‖) * S * S := by
          gcongr
          all_goals first
            | exact hLnorm
            | exact (hI₀spec y hy).2.1
            | exact hIsub
            | exact hu₁
    have he3 : ‖L (I₀ y) (I₀ y) (u₁ - u₀) u₁‖ ≤
        (8 * ‖B‖) * 2 * 2 * ‖v₁ - v₀‖ * S := by
      calc
        ‖L (I₀ y) (I₀ y) (u₁ - u₀) u₁‖ ≤
            ‖L‖ * ‖I₀ y‖ * ‖I₀ y‖ * ‖u₁ - u₀‖ * ‖u₁‖ :=
          hLpoint _ _ _ _
        _ ≤ (8 * ‖B‖) * 2 * 2 * ‖v₁ - v₀‖ * S := by
          gcongr
          all_goals first
            | exact hLnorm
            | exact (hI₀spec y hy).2.1
            | exact huDiff
            | exact hu₁
    have he4 : ‖L (I₀ y) (I₀ y) u₀ (u₁ - u₀)‖ ≤
        (8 * ‖B‖) * 2 * 2 * S * ‖v₁ - v₀‖ := by
      calc
        ‖L (I₀ y) (I₀ y) u₀ (u₁ - u₀)‖ ≤
            ‖L‖ * ‖I₀ y‖ * ‖I₀ y‖ * ‖u₀‖ * ‖u₁ - u₀‖ :=
          hLpoint _ _ _ _
        _ ≤ (8 * ‖B‖) * 2 * 2 * S * ‖v₁ - v₀‖ := by
          gcongr
          all_goals first
            | exact hLnorm
            | exact (hI₀spec y hy).2.1
            | exact hu₀
            | exact huDiff
    calc
      ‖L (I₁ y) (I₁ y) u₁ u₁ - L (I₀ y) (I₀ y) u₀ u₀‖ ≤
          ‖L dI (I₁ y) u₁ u₁‖ + ‖L (I₀ y) dI u₁ u₁‖ +
            ‖L (I₀ y) (I₀ y) (u₁ - u₀) u₁‖ +
              ‖L (I₀ y) (I₀ y) u₀ (u₁ - u₀)‖ := by
        rw [hsplit]
        calc
          ‖L dI (I₁ y) u₁ u₁ + L (I₀ y) dI u₁ u₁ +
              L (I₀ y) (I₀ y) (u₁ - u₀) u₁ +
                L (I₀ y) (I₀ y) u₀ (u₁ - u₀)‖ ≤
            ‖L dI (I₁ y) u₁ u₁ + L (I₀ y) dI u₁ u₁ +
              L (I₀ y) (I₀ y) (u₁ - u₀) u₁‖ +
                ‖L (I₀ y) (I₀ y) u₀ (u₁ - u₀)‖ := norm_add_le _ _
          _ ≤ (‖L dI (I₁ y) u₁ u₁‖ + ‖L (I₀ y) dI u₁ u₁‖ +
                ‖L (I₀ y) (I₀ y) (u₁ - u₀) u₁‖) +
                ‖L (I₀ y) (I₀ y) u₀ (u₁ - u₀)‖ := by
            apply add_le_add
            · calc
                ‖(L dI (I₁ y) u₁ u₁ + L (I₀ y) dI u₁ u₁) +
                    L (I₀ y) (I₀ y) (u₁ - u₀) u₁‖ ≤
                    ‖L dI (I₁ y) u₁ u₁ + L (I₀ y) dI u₁ u₁‖ +
                      ‖L (I₀ y) (I₀ y) (u₁ - u₀) u₁‖ := norm_add_le _ _
                _ ≤ (‖L dI (I₁ y) u₁ u₁‖ + ‖L (I₀ y) dI u₁ u₁‖) +
                      ‖L (I₀ y) (I₀ y) (u₁ - u₀) u₁‖ := by
                    exact add_le_add (norm_add_le _ _) (le_refl _)
            · exact le_refl _
          _ = _ := by ring
      _ ≤ ((8 * ‖B‖) * (12 * ‖a₁ - a₀‖) * 2 * S * S) +
            ((8 * ‖B‖) * 2 * (12 * ‖a₁ - a₀‖) * S * S) +
            ((8 * ‖B‖) * 2 * 2 * ‖v₁ - v₀‖ * S) +
            ((8 * ‖B‖) * 2 * 2 * S * ‖v₁ - v₀‖) := by
        gcongr
      _ = 384 * ‖B‖ * S ^ 2 * ‖a₁ - a₀‖ +
            64 * ‖B‖ * S * ‖v₁ - v₀‖ := by ring

  refine ⟨I₀, I₁, N₀, N₁, ?_, ?_, ?_, ?_, ?_⟩
  · exact hI₀spec
  · exact hI₁spec
  · intro y hy p
    change (NH₀ y).1.1 p + (Grad₀ y).1.1 p = _
    rw [hNH₀coord' y hy p, hCprincipal, hGrad₀coord y hy p]
    simp [oneJet, BoundedContinuousFunction.sub_apply]
  · intro y hy p
    change (NH₁ y).1.1 p + (Grad₁ y).1.1 p = _
    rw [hNH₁coord' y hy p, hCprincipal, hGrad₁coord y hy p]
    simp [oneJet, BoundedContinuousFunction.sub_apply]
  · intro y₀ y₁ hy₀ hy₁
    have hsplit : N₁ y₁ - N₀ y₀ =
        (N₁ y₁ - N₁ y₀) + (N₁ y₀ - N₀ y₀) := by abel
    calc
      ‖N₁ y₁ - N₀ y₀‖ =
          ‖(N₁ y₁ - N₁ y₀) + (N₁ y₀ - N₀ y₀)‖ := by rw [← hsplit]
      _ ≤ ‖N₁ y₁ - N₁ y₀‖ + ‖N₁ y₀ - N₀ y₀‖ := norm_add_le _ _
      _ ≤ (Hcoef + Gcoef) * ‖y₁ - y₀‖ +
            (216 * (hbar + ‖G‖ * R) * ‖a₁ - a₀‖ +
              384 * ‖B‖ * S ^ 2 * ‖a₁ - a₀‖ +
                64 * ‖B‖ * S * ‖v₁ - v₀‖ +
                  18 * (4 * abar + 12 * ‖P‖ * R) * ‖H₁ - H₀‖) := by
        have hcrossN :
            ‖N₁ y₀ - N₀ y₀‖ ≤
              216 * (hbar + ‖G‖ * R) * ‖a₁ - a₀‖ +
                384 * ‖B‖ * S ^ 2 * ‖a₁ - a₀‖ +
                  64 * ‖B‖ * S * ‖v₁ - v₀‖ +
                    18 * (4 * abar + 12 * ‖P‖ * R) * ‖H₁ - H₀‖ := by
          calc
            ‖N₁ y₀ - N₀ y₀‖ =
                ‖(NH₁ y₀ - NH₀ y₀) + (Grad₁ y₀ - Grad₀ y₀)‖ := by
              congr 1
              dsimp [N₁, N₀]
              abel
            _ ≤ ‖NH₁ y₀ - NH₀ y₀‖ + ‖Grad₁ y₀ - Grad₀ y₀‖ := norm_add_le _ _
            _ ≤ (216 * (hbar + ‖G‖ * R) * ‖a₁ - a₀‖ +
                  18 * (4 * abar + 12 * ‖P‖ * R) * ‖H₁ - H₀‖) +
                (384 * ‖B‖ * S ^ 2 * ‖a₁ - a₀‖ +
                  64 * ‖B‖ * S * ‖v₁ - v₀‖) :=
              add_le_add (hCrossHess y₀ hy₀) (hCrossGrad y₀ hy₀)
            _ = _ := by ring
        exact add_le_add (hSame₁ y₁ y₀ hy₁ hy₀) hcrossN
      _ = Ky * ‖y₁ - y₀‖ + Ka * ‖a₁ - a₀‖ +
            Kv * ‖v₁ - v₀‖ + Kh * ‖H₁ - H₀‖ := by
        simp [Ky, Ka, Kv, Kh, Hcoef, Gcoef]
        ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.JointAffineBackgroundLipschitz
