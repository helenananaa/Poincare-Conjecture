import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ForcingGraphBilinearProduct
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open scoped Topology BoundedContinuousFunction
/-- A genuine bilinear product acts on forcing graphs, with the full product increment rule. -/
theorem exists_forcing_bilinear_product
    {V W Z : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (B : V →L[ℝ] W →L[ℝ] Z) (T alpha : ℝ)
    (a : ForcingJet V T) (ha : a ∈ forcingGraph V T alpha) :
    ∃ M : ForcingJet W T →L[ℝ] ForcingJet Z T,
      ‖M‖ ≤ 2 * ‖B‖ * ‖a‖ ∧
      (∀ f p, (M f).1 p = B (a.1 p) (f.1 p)) ∧
      (∀ f p, (M f).2 p = B (a.1 p.1.1) (f.2 p) + B (a.2 p) (f.1 p.1.2)) ∧
      ∀ f ∈ forcingGraph W T alpha, M f ∈ forcingGraph Z T alpha :=
/- SWARM_PROOF_BEGIN -/
by
  let firstRaw (f : ForcingJet W T) : Slab T → Z :=
    fun p => B (a.1 p) (f.1 p)
  let secondRaw (f : ForcingJet W T) : Pair T → Z :=
    fun p => B (a.1 p.1.1) (f.2 p) + B (a.2 p) (f.1 p.1.2)
  have hpair : Continuous (fun p : Pair T => (p.1 : Slab T × Slab T)) :=
    continuous_subtype_val
  have hleft : Continuous (fun p : Pair T => p.1.1) := continuous_fst.comp hpair
  have hright : Continuous (fun p : Pair T => p.1.2) := continuous_snd.comp hpair
  have firstCont (f : ForcingJet W T) : Continuous (firstRaw f) := by
    dsimp [firstRaw]
    exact B.continuous₂.comp (a.1.continuous.prodMk f.1.continuous)
  have secondCont (f : ForcingJet W T) : Continuous (secondRaw f) := by
    dsimp [secondRaw]
    exact
      (B.continuous₂.comp
        ((a.1.continuous.comp hleft).prodMk f.2.continuous)).add
      (B.continuous₂.comp
        (a.2.continuous.prodMk (f.1.continuous.comp hright)))
  have firstRawBound (f : ForcingJet W T) (p : Slab T) :
      ‖firstRaw f p‖ ≤ ‖B‖ * ‖a.1‖ * ‖f.1‖ := by
    calc
      ‖firstRaw f p‖ ≤ ‖B‖ * ‖a.1 p‖ * ‖f.1 p‖ := B.le_opNorm₂ _ _
      _ ≤ ‖B‖ * ‖a.1‖ * ‖f.1‖ := by
        gcongr <;> exact (by apply BoundedContinuousFunction.norm_coe_le_norm)
  have secondRawBound (f : ForcingJet W T) (p : Pair T) :
      ‖secondRaw f p‖ ≤ ‖B‖ * ‖a.1‖ * ‖f.2‖ +
        ‖B‖ * ‖a.2‖ * ‖f.1‖ := by
    calc
      ‖secondRaw f p‖ ≤
          ‖B (a.1 p.1.1) (f.2 p)‖ + ‖B (a.2 p) (f.1 p.1.2)‖ := norm_add_le _ _
      _ ≤ ‖B‖ * ‖a.1‖ * ‖f.2‖ + ‖B‖ * ‖a.2‖ * ‖f.1‖ := by
        apply add_le_add
        · calc
            ‖B (a.1 p.1.1) (f.2 p)‖ ≤
                ‖B‖ * ‖a.1 p.1.1‖ * ‖f.2 p‖ := B.le_opNorm₂ _ _
            _ ≤ ‖B‖ * ‖a.1‖ * ‖f.2‖ := by
              gcongr <;> exact (by apply BoundedContinuousFunction.norm_coe_le_norm)
        · calc
            ‖B (a.2 p) (f.1 p.1.2)‖ ≤
                ‖B‖ * ‖a.2 p‖ * ‖f.1 p.1.2‖ := B.le_opNorm₂ _ _
            _ ≤ ‖B‖ * ‖a.2‖ * ‖f.1‖ := by
              gcongr <;> exact (by apply BoundedContinuousFunction.norm_coe_le_norm)
  let firstField (f : ForcingJet W T) : Slab T →ᵇ Z :=
    BoundedContinuousFunction.ofNormedAddCommGroup (firstRaw f) (firstCont f)
      (‖B‖ * ‖a.1‖ * ‖f.1‖) (firstRawBound f)
  let secondField (f : ForcingJet W T) : Pair T →ᵇ Z :=
    BoundedContinuousFunction.ofNormedAddCommGroup (secondRaw f) (secondCont f)
      (‖B‖ * ‖a.1‖ * ‖f.2‖ + ‖B‖ * ‖a.2‖ * ‖f.1‖) (secondRawBound f)
  have firstFieldNorm (f : ForcingJet W T) :
      ‖firstField f‖ ≤ ‖B‖ * ‖a.1‖ * ‖f.1‖ := by
    change ‖BoundedContinuousFunction.ofNormedAddCommGroup (firstRaw f)
      (firstCont f) (‖B‖ * ‖a.1‖ * ‖f.1‖) (firstRawBound f)‖ ≤ _
    exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
      (firstCont f) (by positivity) (firstRawBound f)
  have secondFieldNorm (f : ForcingJet W T) :
      ‖secondField f‖ ≤ ‖B‖ * ‖a.1‖ * ‖f.2‖ + ‖B‖ * ‖a.2‖ * ‖f.1‖ := by
    change ‖BoundedContinuousFunction.ofNormedAddCommGroup (secondRaw f)
      (secondCont f) (‖B‖ * ‖a.1‖ * ‖f.2‖ + ‖B‖ * ‖a.2‖ * ‖f.1‖)
      (secondRawBound f)‖ ≤ _
    exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
      (secondCont f) (by positivity) (secondRawBound f)
  have firstField_eval (f : ForcingJet W T) (p : Slab T) :
      firstField f p = B (a.1 p) (f.1 p) := by
    change firstRaw f p = B (a.1 p) (f.1 p)
    rfl
  have secondField_eval (f : ForcingJet W T) (p : Pair T) :
      secondField f p = B (a.1 p.1.1) (f.2 p) + B (a.2 p) (f.1 p.1.2) := by
    change secondRaw f p = _
    rfl
  let M0 : ForcingJet W T →ₗ[ℝ] ForcingJet Z T := {
    toFun := fun f => (firstField f, secondField f)
    map_add' := by
      intro f g
      apply Prod.ext
      · apply BoundedContinuousFunction.ext
        intro p
        change B (a.1 p) (f.1 p + g.1 p) = firstField f p + firstField g p
        rw [firstField_eval, firstField_eval]
        exact map_add _ _ _
      · apply BoundedContinuousFunction.ext
        intro p
        change B (a.1 p.1.1) (f.2 p + g.2 p) +
            B (a.2 p) (f.1 p.1.2 + g.1 p.1.2) =
          secondField f p + secondField g p
        rw [secondField_eval, secondField_eval]
        rw [map_add, map_add]
        abel
    map_smul' := by
      intro c f
      apply Prod.ext
      · apply BoundedContinuousFunction.ext
        intro p
        change B (a.1 p) (c • f.1 p) = c • firstField f p
        rw [firstField_eval]
        exact map_smul _ _ _
      · apply BoundedContinuousFunction.ext
        intro p
        change B (a.1 p.1.1) (c • f.2 p) +
            B (a.2 p) (c • f.1 p.1.2) =
          c • secondField f p
        rw [secondField_eval]
        rw [map_smul, map_smul, smul_add]
  }
  have hM0 (f : ForcingJet W T) :
      ‖M0 f‖ ≤ (2 * ‖B‖ * ‖a‖) * ‖f‖ := by
    have ha1 : ‖a.1‖ ≤ ‖a‖ := norm_fst_le a
    have ha2 : ‖a.2‖ ≤ ‖a‖ := norm_snd_le a
    have hf1 : ‖f.1‖ ≤ ‖f‖ := norm_fst_le f
    have hf2 : ‖f.2‖ ≤ ‖f‖ := norm_snd_le f
    change max ‖firstField f‖ ‖secondField f‖ ≤ _
    apply max_le
    · calc
        ‖firstField f‖ ≤ ‖B‖ * ‖a.1‖ * ‖f.1‖ := firstFieldNorm f
        _ ≤ ‖B‖ * ‖a‖ * ‖f‖ := by gcongr
        _ = (‖B‖ * ‖a‖) * ‖f‖ := by ring
        _ ≤ (2 * ‖B‖ * ‖a‖) * ‖f‖ := by
          nlinarith [mul_nonneg (norm_nonneg B) (mul_nonneg (norm_nonneg a) (norm_nonneg f))]
    · calc
        ‖secondField f‖ ≤
            ‖B‖ * ‖a.1‖ * ‖f.2‖ + ‖B‖ * ‖a.2‖ * ‖f.1‖ := secondFieldNorm f
        _ ≤ ‖B‖ * ‖a‖ * ‖f‖ + ‖B‖ * ‖a‖ * ‖f‖ := by gcongr
        _ = (2 * ‖B‖ * ‖a‖) * ‖f‖ := by ring
  let M : ForcingJet W T →L[ℝ] ForcingJet Z T :=
    M0.mkContinuous (2 * ‖B‖ * ‖a‖) hM0
  refine ⟨M, LinearMap.mkContinuous_norm_le M0 (by positivity) hM0, ?_, ?_, ?_⟩
  · intro f p
    change firstRaw f p = B (a.1 p) (f.1 p)
    rfl
  · intro f p
    change secondRaw f p = B (a.1 p.1.1) (f.2 p) + B (a.2 p) (f.1 p.1.2)
    rfl
  · intro f hf p
    let r : ℝ := (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹
    let A : V := a.1 p.1.1
    let C : V := a.1 p.1.2
    let x : W := f.1 p.1.1
    let y : W := f.1 p.1.2
    have hf' : f.2 p = r • (x - y) := by
      simpa [r, x, y] using hf p
    have ha' : a.2 p = r • (A - C) := by
      simpa [r, A, C] using ha p
    have hsplit : B A x - B C y = B A (x - y) + B (A - C) y := by
      calc
        B A x - B C y = (B A x - B A y) + (B A y - B C y) := by abel
        _ = B A (x - y) + B (A - C) y := by
          rw [← map_sub, ← B.map_sub₂]
    change B A (f.2 p) + B (a.2 p) y = r • (B A x - B C y)
    rw [hf', ha']
    calc
      B A (r • (x - y)) + B (r • (A - C)) y =
          r • B A (x - y) + r • B (A - C) y := by rw [map_smul, B.map_smul₂]
      _ = r • (B A (x - y) + B (A - C) y) := by rw [← smul_add]
      _ = r • (B A x - B C y) := by rw [← hsplit]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ForcingGraphBilinearProduct
