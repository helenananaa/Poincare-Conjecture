import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ForcingGraphScalarProduct
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open scoped Topology BoundedContinuousFunction
/-- Multiplication by a scalar Holder coefficient acts on the true normalized increment graph. -/
theorem exists_forcing_scalar_product
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T alpha : ℝ) (a : ForcingJet ℝ T) (ha : a ∈ forcingGraph ℝ T alpha) :
    ∃ M : ForcingJet V T →L[ℝ] ForcingJet V T, ‖M‖ ≤ 2*‖a‖ ∧
      (∀ z p, (M z).1 p = a.1 p • z.1 p) ∧
      (∀ z p, (M z).2 p = a.1 p.1.1 • z.2 p + a.2 p • z.1 p.1.2) ∧
      ∀ z ∈ forcingGraph V T alpha, M z ∈ forcingGraph V T alpha :=
/- SWARM_PROOF_BEGIN -/
by
  let firstRaw (z : ForcingJet V T) : Slab T → V :=
    fun p => a.1 p • z.1 p
  let secondRaw (z : ForcingJet V T) : Pair T → V :=
    fun p => a.1 p.1.1 • z.2 p + a.2 p • z.1 p.1.2
  have hpair : Continuous (fun p : Pair T => (p.1 : Slab T × Slab T)) :=
    continuous_subtype_val
  have hleft : Continuous (fun p : Pair T => p.1.1) := continuous_fst.comp hpair
  have hright : Continuous (fun p : Pair T => p.1.2) := continuous_snd.comp hpair
  have firstCont (z : ForcingJet V T) : Continuous (firstRaw z) := by
    dsimp [firstRaw]
    exact continuous_smul.comp (a.1.continuous.prodMk z.1.continuous)
  have secondCont (z : ForcingJet V T) : Continuous (secondRaw z) := by
    dsimp [secondRaw]
    exact
      (continuous_smul.comp
        ((a.1.continuous.comp hleft).prodMk z.2.continuous)).add
      (continuous_smul.comp
        (a.2.continuous.prodMk (z.1.continuous.comp hright)))
  have firstRawBound (z : ForcingJet V T) (p : Slab T) :
      ‖firstRaw z p‖ ≤ ‖a.1‖ * ‖z.1‖ := by
    calc
      ‖firstRaw z p‖ = ‖a.1 p‖ * ‖z.1 p‖ := by
        simp [firstRaw, norm_smul]
      _ ≤ ‖a.1‖ * ‖z.1‖ :=
        mul_le_mul (a.1.norm_coe_le_norm p) (z.1.norm_coe_le_norm p)
          (norm_nonneg _) (norm_nonneg _)
  have secondRawBound (z : ForcingJet V T) (p : Pair T) :
      ‖secondRaw z p‖ ≤ ‖a.1‖ * ‖z.2‖ + ‖a.2‖ * ‖z.1‖ := by
    calc
      ‖secondRaw z p‖ ≤
          ‖a.1 p.1.1 • z.2 p‖ + ‖a.2 p • z.1 p.1.2‖ := by
            exact norm_add_le _ _
      _ ≤ ‖a.1‖ * ‖z.2‖ + ‖a.2‖ * ‖z.1‖ := by
        apply add_le_add
        · calc
            ‖a.1 p.1.1 • z.2 p‖ = ‖a.1 p.1.1‖ * ‖z.2 p‖ := by simp [norm_smul]
            _ ≤ ‖a.1‖ * ‖z.2‖ :=
              mul_le_mul (a.1.norm_coe_le_norm _) (z.2.norm_coe_le_norm p)
                (norm_nonneg _) (norm_nonneg _)
        · calc
            ‖a.2 p • z.1 p.1.2‖ = ‖a.2 p‖ * ‖z.1 p.1.2‖ := by simp [norm_smul]
            _ ≤ ‖a.2‖ * ‖z.1‖ :=
              mul_le_mul (a.2.norm_coe_le_norm p) (z.1.norm_coe_le_norm _)
                (norm_nonneg _) (norm_nonneg _)
  let firstField (z : ForcingJet V T) : Slab T →ᵇ V :=
    BoundedContinuousFunction.ofNormedAddCommGroup (firstRaw z) (firstCont z)
      (‖a.1‖ * ‖z.1‖) (firstRawBound z)
  let secondField (z : ForcingJet V T) : Pair T →ᵇ V :=
    BoundedContinuousFunction.ofNormedAddCommGroup (secondRaw z) (secondCont z)
      (‖a.1‖ * ‖z.2‖ + ‖a.2‖ * ‖z.1‖) (secondRawBound z)
  have firstFieldNorm (z : ForcingJet V T) :
      ‖firstField z‖ ≤ ‖a.1‖ * ‖z.1‖ := by
    change ‖BoundedContinuousFunction.ofNormedAddCommGroup (firstRaw z)
      (firstCont z) (‖a.1‖ * ‖z.1‖) (firstRawBound z)‖ ≤ _
    exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
      (firstCont z) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (firstRawBound z)
  have secondFieldNorm (z : ForcingJet V T) :
      ‖secondField z‖ ≤ ‖a.1‖ * ‖z.2‖ + ‖a.2‖ * ‖z.1‖ := by
    change ‖BoundedContinuousFunction.ofNormedAddCommGroup (secondRaw z)
      (secondCont z) (‖a.1‖ * ‖z.2‖ + ‖a.2‖ * ‖z.1‖) (secondRawBound z)‖ ≤ _
    exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
      (secondCont z)
      (add_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
      (secondRawBound z)
  let M0 : ForcingJet V T →ₗ[ℝ] ForcingJet V T := {
    toFun := fun z => (firstField z, secondField z)
    map_add' := by
      intro z w
      apply Prod.ext
      · apply BoundedContinuousFunction.ext
        intro p
        change a.1 p • (z.1 p + w.1 p) =
          a.1 p • z.1 p + a.1 p • w.1 p
        rw [smul_add]
      · apply BoundedContinuousFunction.ext
        intro p
        change a.1 p.1.1 • (z.2 p + w.2 p) +
            a.2 p • (z.1 p.1.2 + w.1 p.1.2) =
          (a.1 p.1.1 • z.2 p + a.2 p • z.1 p.1.2) +
            (a.1 p.1.1 • w.2 p + a.2 p • w.1 p.1.2)
        rw [smul_add, smul_add]
        abel
    map_smul' := by
      intro c z
      apply Prod.ext
      · apply BoundedContinuousFunction.ext
        intro p
        change a.1 p • (c • z.1 p) = c • (a.1 p • z.1 p)
        exact smul_comm _ _ _
      · apply BoundedContinuousFunction.ext
        intro p
        change a.1 p.1.1 • (c • z.2 p) +
            a.2 p • (c • z.1 p.1.2) =
          c • (a.1 p.1.1 • z.2 p + a.2 p • z.1 p.1.2)
        rw [smul_comm (a.1 p.1.1) c (z.2 p),
          smul_comm (a.2 p) c (z.1 p.1.2), ← smul_add]
  }
  have hM0 (z : ForcingJet V T) : ‖M0 z‖ ≤ (2 * ‖a‖) * ‖z‖ := by
    have ha1 : ‖a.1‖ ≤ ‖a‖ := norm_fst_le a
    have ha2 : ‖a.2‖ ≤ ‖a‖ := norm_snd_le a
    have hz1 : ‖z.1‖ ≤ ‖z‖ := norm_fst_le z
    have hz2 : ‖z.2‖ ≤ ‖z‖ := norm_snd_le z
    change max ‖firstField z‖ ‖secondField z‖ ≤ _
    apply max_le
    · calc
        ‖firstField z‖ ≤ ‖a.1‖ * ‖z.1‖ := firstFieldNorm z
        _ ≤ ‖a‖ * ‖z‖ := mul_le_mul ha1 hz1 (norm_nonneg _) (norm_nonneg _)
        _ ≤ (2 * ‖a‖) * ‖z‖ := by nlinarith [norm_nonneg a, norm_nonneg z]
    · calc
        ‖secondField z‖ ≤ ‖a.1‖ * ‖z.2‖ + ‖a.2‖ * ‖z.1‖ := secondFieldNorm z
        _ ≤ ‖a‖ * ‖z‖ + ‖a‖ * ‖z‖ := by
          apply add_le_add
          · exact mul_le_mul ha1 hz2 (norm_nonneg _) (norm_nonneg _)
          · exact mul_le_mul ha2 hz1 (norm_nonneg _) (norm_nonneg _)
        _ = (2 * ‖a‖) * ‖z‖ := by ring
  let M : ForcingJet V T →L[ℝ] ForcingJet V T :=
    M0.mkContinuous (2 * ‖a‖) hM0
  refine ⟨M, LinearMap.mkContinuous_norm_le M0 (by positivity) hM0, ?_, ?_, ?_⟩
  · intro z p
    change firstRaw z p = a.1 p • z.1 p
    rfl
  · intro z p
    change secondRaw z p = a.1 p.1.1 • z.2 p + a.2 p • z.1 p.1.2
    rfl
  · intro z hz p
    change a.1 p.1.1 • z.2 p + a.2 p • z.1 p.1.2 =
      (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        (a.1 p.1.1 • z.1 p.1.1 - a.1 p.1.2 • z.1 p.1.2)
    let r : ℝ := (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹
    let A : ℝ := a.1 p.1.1
    let B : ℝ := a.1 p.1.2
    let x : V := z.1 p.1.1
    let y : V := z.1 p.1.2
    have hz' : z.2 p = r • (x - y) := by
      simpa [r, x, y] using hz p
    have ha' : a.2 p = r • (A - B) := by
      simpa [r, A, B] using ha p
    have hsplit : A • x - B • y = A • (x - y) + (A - B) • y := by
      calc
        A • x - B • y = (A • x - A • y) + (A • y - B • y) := by abel
        _ = A • (x - y) + (A - B) • y := by rw [smul_sub, sub_smul]
    change A • z.2 p + a.2 p • y = r • (A • x - B • y)
    rw [hz', ha']
    calc
      A • (r • (x - y)) + (r • (A - B)) • y =
          r • (A • (x - y)) + r • ((A - B) • y) := by
        congr 1
        · exact smul_comm A r (x - y)
        · exact (smul_smul r (A - B) y).symm
      _ = r • (A • (x - y) + (A - B) • y) := by rw [← smul_add]
      _ = r • (A • x - B • y) := by rw [← hsplit]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ForcingGraphScalarProduct
