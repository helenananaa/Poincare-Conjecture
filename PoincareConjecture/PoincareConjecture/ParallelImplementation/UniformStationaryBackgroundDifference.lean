import PoincareConjecture.ParallelImplementation.UniformInitialDifferenceQuotient
import PoincareConjecture.ParallelImplementation.ForcingSpatialTranslation
import PoincareConjecture.ParallelImplementation.SpatialHolderToParabolicForcing
import PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.UniformStationaryBackgroundDifference
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ForcingSpatialTranslation
open scoped Topology BigOperators ContDiff BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "V1" => E3 →L[ℝ] E6
local notation "V2" => E3 →L[ℝ] E3 →L[ℝ] E6
local instance : NormedAddCommGroup V1 := inferInstance
local instance : NormedSpace ℝ V1 := inferInstance
local instance : NormedAddCommGroup V2 := inferInstance
local instance : NormedSpace ℝ V2 := inferInstance
/-- Uniform spatial difference bounds in the actual stationary forcing norms.
The forcing jets are arbitrary given witnesses of the original data: they are
not replaced by unrelated witnesses from another existence theorem. -/
theorem uniform_stationary_background_differences
    (u : E3 → E6) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 ≤ T →
      ∀ (Fu : ForcingJet E6 T) (FA : ForcingJet V1 T) (FH : ForcingJet V2 T),
        Fu ∈ forcingGraph E6 T alpha →
        FA ∈ forcingGraph V1 T alpha →
        FH ∈ forcingGraph V2 T alpha →
        (∀ p : Slab T, Fu.1 p = u p.2) →
        (∀ p : Slab T, FA.1 p = fderiv ℝ u p.2) →
        (∀ p : Slab T, FH.1 p = fderiv ℝ (fderiv ℝ u) p.2) →
        ∀ (i : Fin 3) (h : ℝ), h ≠ 0 →
          ‖h⁻¹ • (translateForcingJet i h Fu - Fu)‖ ≤ C ∧
          ‖h⁻¹ • (translateForcingJet i h FA - FA)‖ ≤ C ∧
          ‖h⁻¹ • (translateForcingJet i h FH - FH)‖ ≤ C :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨K, hKpos, hjets⟩ :=
    PoincareConjecture.ParallelImplementation.UniformInitialDifferenceQuotient.exists_uniform_initial_difference_jets
      u hu hc alpha ha ha1
  have hKnonneg : 0 ≤ K := le_of_lt hKpos
  have holder_of_derivative_bound
      {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : E3 →ᵇ V) (df : E3 → (E3 →L[ℝ] V)) (B : ℝ) (hB : 0 ≤ B)
      (hderiv : ∀ x, HasFDerivAt f (df x) x)
      (hdf : ∀ x, ‖df x‖ ≤ B) (hf : ∀ x, ‖f x‖ ≤ B) :
      ∀ x y : E3, ‖f x - f y‖ ≤ (2 * B) * ‖x-y‖^alpha := by
    intro x y
    let d : ℝ := ‖x-y‖
    by_cases hd : d ≤ 1
    · have hdf' : ∀ z : E3, ‖fderiv ℝ (f : E3 → V) z‖ ≤ B := by
        intro z
        rw [(hderiv z).fderiv]
        exact hdf z
      have hmv : ‖f x - f y‖ ≤ B * ‖x-y‖ :=
        convex_univ.norm_image_sub_le_of_norm_fderiv_le
          (fun z _ => (hderiv z).differentiableAt)
          (fun z _ => hdf' z) (x := y) (y := x) (Set.mem_univ _) (Set.mem_univ _)
      have hdPow : ‖x-y‖ ≤ ‖x-y‖^alpha := by
        have h := Real.rpow_le_rpow_of_exponent_ge'
          (norm_nonneg (x-y)) (by simpa [d] using hd) ha.le ha1
        simpa [Real.rpow_one] using h
      calc
        ‖f x-f y‖ ≤ B * ‖x-y‖ := hmv
        _ ≤ B * ‖x-y‖^alpha := mul_le_mul_of_nonneg_left hdPow hB
        _ ≤ (2*B) * ‖x-y‖^alpha := by
          have hp := Real.rpow_nonneg (norm_nonneg (x-y)) alpha
          nlinarith
    · have hdlarge : 1 ≤ d := le_of_not_ge hd
      have hnorm : ‖f x-f y‖ ≤ 2*B := by
        calc
          ‖f x-f y‖ ≤ ‖f x‖+‖f y‖ := norm_sub_le _ _
          _ ≤ B+B := add_le_add (hf x) (hf y)
          _ = 2*B := by ring
      have hpow : 1 ≤ ‖x-y‖^alpha := by
        exact Real.one_le_rpow (by simpa [d] using hdlarge) ha.le
      calc
        ‖f x-f y‖ ≤ 2*B := hnorm
        _ ≤ (2*B)*‖x-y‖^alpha := by
          nlinarith [mul_le_mul_of_nonneg_left hpow (show 0 ≤ 2*B by positivity)]
  let graphSubmodule {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (T alpha : ℝ) : Submodule ℝ (ForcingJet V T) := {
    carrier := forcingGraph V T alpha
    zero_mem' := by intro p; simp
    add_mem' := by
      intro z w hz hw p
      change z.2 p+w.2 p =
        (PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
          ((z.1+w.1) p.1.1-(z.1+w.1) p.1.2)
      rw [hz p, hw p]
      simp [sub_eq_add_neg, smul_add]
      abel
    smul_mem' := by
      intro c z hz p
      change c • z.2 p =
        (PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
          ((c • z.1) p.1.1-(c • z.1) p.1.2)
      rw [hz p]
      simp [smul_sub, smul_smul, mul_comm]
  }
  refine ⟨2*K, by positivity, ?_⟩
  intro T hT Fu FA FH hFu hFA hFH hFuval hFAval hFHval i h hne
  let v : E3 := EuclideanSpace.single i 1
  have hv : ‖v‖ ≤ 1 := by simp [v]
  obtain ⟨u0, A0, H0, hvalues, hu0deriv, hA0deriv,
      hu0norm, hA0norm, hH0norm, hH0holder⟩ := hjets h hne v hv
  have hu0bound (x : E3) : ‖u0 x‖ ≤ K :=
    (u0.norm_coe_le_norm x).trans hu0norm
  have hA0bound (x : E3) : ‖A0 x‖ ≤ K :=
    (A0.norm_coe_le_norm x).trans hA0norm
  have hH0bound (x : E3) : ‖H0 x‖ ≤ K :=
    (H0.norm_coe_le_norm x).trans hH0norm
  have hUholder : ∀ x y : E3, ‖u0 x-u0 y‖ ≤ (2*K)*‖x-y‖^alpha :=
    holder_of_derivative_bound (V := E6) u0 (fun x => A0 x) K hKnonneg hu0deriv
      (fun x => hA0bound x) hu0bound
  have hAholder : ∀ x y : E3, ‖A0 x-A0 y‖ ≤ (2*K)*‖x-y‖^alpha :=
    holder_of_derivative_bound (V := V1) A0 (fun x => H0 x) K hKnonneg hA0deriv
      (fun x => hH0bound x) hA0bound
  have hHholder : ∀ x y : E3, ‖H0 x-H0 y‖ ≤ (2*K)*‖x-y‖^alpha := by
    intro x y
    calc
      ‖H0 x-H0 y‖ ≤ K*‖x-y‖^alpha := hH0holder x y
      _ ≤ (2*K)*‖x-y‖^alpha := by
        have hp : 0 ≤ ‖x-y‖^alpha := Real.rpow_nonneg (norm_nonneg _) alpha
        nlinarith
  obtain ⟨G0, hG0graph, hG0val, hG0norm⟩ :=
    PoincareConjecture.ParallelImplementation.SpatialHolderToParabolicForcing.exists_stationary_parabolic_forcing
      T alpha (2*K) ha (by positivity) u0 hUholder
  obtain ⟨G1, hG1graph, hG1val, hG1norm⟩ :=
    PoincareConjecture.ParallelImplementation.SpatialHolderToParabolicForcing.exists_stationary_parabolic_forcing
      T alpha (2*K) ha (by positivity) A0 hAholder
  obtain ⟨G2, hG2graph, hG2val, hG2norm⟩ :=
    PoincareConjecture.ParallelImplementation.SpatialHolderToParabolicForcing.exists_stationary_parabolic_forcing
      T alpha (2*K) ha (by positivity) H0 hHholder
  have hG0bound : ‖G0‖ ≤ 2*K := by
    calc
      ‖G0‖ ≤ max ‖u0‖ (2*K) := hG0norm
      _ ≤ 2*K := max_le (le_trans hu0norm (by linarith)) (le_rfl)
  have hG1bound : ‖G1‖ ≤ 2*K := by
    calc
      ‖G1‖ ≤ max ‖A0‖ (2*K) := hG1norm
      _ ≤ 2*K := max_le (le_trans hA0norm (by linarith)) (le_rfl)
  have hG2bound : ‖G2‖ ≤ 2*K := by
    calc
      ‖G2‖ ≤ max ‖H0‖ (2*K) := hG2norm
      _ ≤ 2*K := max_le (le_trans hH0norm (by linarith)) (le_rfl)
  have hquotient_deriv {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : E3 → V) (hf : Differentiable ℝ f) :
      fderiv ℝ (fun x => h⁻¹ • (f (x+h•v)-f x)) =
        fun x => h⁻¹ • (fderiv ℝ f (x+h•v)-fderiv ℝ f x) := by
    funext x
    have hshift : Differentiable ℝ (fun y : E3 => f (y+h•v)) :=
      hf.comp (differentiable_id.add_const (h•v))
    have hdiff : DifferentiableAt ℝ (fun y : E3 => f (y+h•v)-f y) x :=
      (hshift x).sub (hf x)
    rw [fderiv_fun_const_smul hdiff (h⁻¹)]
    change h⁻¹ • fderiv ℝ ((fun y : E3 => f (y+h•v))-f) x = _
    rw [fderiv_sub (hshift x) (hf x), fderiv_comp_add_right]
  have huDiff : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hD1cd : ContDiff ℝ 3 (fderiv ℝ u) := by
    have h := hu.fderiv_right (m := 3)
      (show (4 : ℕ∞ω) ≤ ∞ from
        WithTop.coe_le_coe.mpr (show (4 : ℕ∞) ≤ ⊤ from le_top))
    simpa using h
  have hD1Diff : Differentiable ℝ (fderiv ℝ u) := hD1cd.differentiable (by norm_num)
  have hD2cd : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ u)) := by
    have h := hD1cd.fderiv_right (m := 2) (by norm_num)
    simpa using h
  have hD2Diff : Differentiable ℝ (fderiv ℝ (fderiv ℝ u)) := hD2cd.differentiable (by norm_num)
  let Q : E3 → E6 := fun x => h⁻¹ • (u (x+h•v)-u x)
  let R : E3 → V1 := fun x => h⁻¹ • (fderiv ℝ u (x+h•v)-fderiv ℝ u x)
  let S : E3 → V2 := fun x => h⁻¹ •
    (fderiv ℝ (fderiv ℝ u) (x+h•v)-fderiv ℝ (fderiv ℝ u) x)
  have hQderiv : fderiv ℝ Q = R := by
    simpa [Q, R] using hquotient_deriv (V := E6) u huDiff
  have hRderiv : fderiv ℝ R = S := by
    simpa [R, S] using hquotient_deriv (V := V1) (fderiv ℝ u) hD1Diff
  have hQvalue (x : E3) : u0 x = Q x := by
    rcases hvalues x with ⟨hu0, _, _⟩
    simpa [Q, PoincareConjecture.ParallelImplementation.UniformInitialDifferenceQuotient.differenceQuotient, v] using hu0
  have hAvalue (x : E3) : A0 x = R x := by
    rcases hvalues x with ⟨_, hA0, _⟩
    calc
      A0 x = fderiv ℝ (PoincareConjecture.ParallelImplementation.UniformInitialDifferenceQuotient.differenceQuotient u h v) x := hA0
      _ = R x := by
        change (fderiv ℝ Q) x = R x
        exact congrFun hQderiv x
  have hHvalue (x : E3) : H0 x = S x := by
    rcases hvalues x with ⟨_, _, hH0⟩
    calc
      H0 x = fderiv ℝ (fderiv ℝ (PoincareConjecture.ParallelImplementation.UniformInitialDifferenceQuotient.differenceQuotient u h v)) x := hH0
      _ = fderiv ℝ (fderiv ℝ Q) x := by rfl
      _ = fderiv ℝ R x := by rw [hQderiv]
      _ = S x := congrFun hRderiv x
  let Uactual : ForcingJet E6 T := h⁻¹ • (translateForcingJet i h Fu - Fu)
  let Aactual : ForcingJet V1 T := h⁻¹ • (translateForcingJet i h FA - FA)
  let Hactual : ForcingJet V2 T := h⁻¹ • (translateForcingJet i h FH - FH)
  have hUactualGraph : Uactual ∈ forcingGraph E6 T alpha := by
    change Uactual ∈ graphSubmodule (V := E6) T alpha
    exact (graphSubmodule (V := E6) T alpha).smul_mem _
      ((graphSubmodule (V := E6) T alpha).sub_mem
        ((forcing_translation_properties T alpha i h).1 Fu |>.2 hFu) hFu)
  have hAactualGraph : Aactual ∈ forcingGraph V1 T alpha := by
    change Aactual ∈ graphSubmodule (V := V1) T alpha
    exact (graphSubmodule (V := V1) T alpha).smul_mem _
      ((graphSubmodule (V := V1) T alpha).sub_mem
        ((forcing_translation_properties T alpha i h).1 FA |>.2 hFA) hFA)
  have hHactualGraph : Hactual ∈ forcingGraph V2 T alpha := by
    change Hactual ∈ graphSubmodule (V := V2) T alpha
    exact (graphSubmodule (V := V2) T alpha).smul_mem _
      ((graphSubmodule (V := V2) T alpha).sub_mem
        ((forcing_translation_properties T alpha i h).1 FH |>.2 hFH) hFH)
  have hUvalue : ∀ p : Slab T, Uactual.1 p = G0.1 p := by
    intro p
    change h⁻¹ • ((translateForcingJet i h Fu).1 p-Fu.1 p) = G0.1 p
    rw [hG0val p, hQvalue p.2]
    simp [Q, translateForcingJet,
      PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.pullbackBCF,
      PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.spatialShiftSlabMap,
      PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.shiftPoint,
      PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.spatialUnit,
      v,
      hFuval]
  have hAvalue' : ∀ p : Slab T, Aactual.1 p = G1.1 p := by
    intro p
    change h⁻¹ • ((translateForcingJet i h FA).1 p-FA.1 p) = G1.1 p
    rw [hG1val p, hAvalue p.2]
    simp [R, translateForcingJet,
      PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.pullbackBCF,
      PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.spatialShiftSlabMap,
      PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.shiftPoint,
      PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.spatialUnit,
      v,
      hFAval]
  have hHvalue' : ∀ p : Slab T, Hactual.1 p = G2.1 p := by
    intro p
    change h⁻¹ • ((translateForcingJet i h FH).1 p-FH.1 p) = G2.1 p
    rw [hG2val p, hHvalue p.2]
    simp [S, translateForcingJet,
      PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.pullbackBCF,
      PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.spatialShiftSlabMap,
      PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.shiftPoint,
      PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.spatialUnit,
      v,
      hFHval]
  have hUeq := PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality.forcing_jet_eq_of_value_eq
    T alpha Uactual G0 hUactualGraph hG0graph hUvalue
  have hAeq := PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality.forcing_jet_eq_of_value_eq
    T alpha Aactual G1 hAactualGraph hG1graph hAvalue'
  have hHeq := PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality.forcing_jet_eq_of_value_eq
    T alpha Hactual G2 hHactualGraph hG2graph hHvalue'
  refine ⟨?_, ?_, ?_⟩
  · change ‖Uactual‖ ≤ 2*K
    rw [hUeq]
    exact hG0bound
  · change ‖Aactual‖ ≤ 2*K
    rw [hAeq]
    exact hG1bound
  · change ‖Hactual‖ ≤ 2*K
    rw [hHeq]
    exact hG2bound
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.UniformStationaryBackgroundDifference
