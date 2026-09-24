import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ZeroTraceValueSmallness
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph
open scoped Topology BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- The actual interior time derivative and zero initial value imply smallness up to both endpoints. -/
theorem zero_trace_value_smallness (T alpha : ℝ) (hT : 0 ≤ T)
    (z : FullJet T) (hz : z ∈ fullParabolicJetSet T alpha hT) :
    (∀ t : Set.Icc (0:ℝ) T, ∀ x : E3,
      ‖z.1.1.1.1 (t,x)‖ ≤ (t:ℝ) * ‖z.1.2‖) ∧
      ‖z.1.1.1.1‖ ≤ T * ‖z.1.2‖ :=
/- SWARM_PROOF_BEGIN -/
by
  simp only [fullParabolicJetSet] at hz
  rcases hz with ⟨_, hgraph, _, hzero⟩
  change ∀ t : Set.Icc (0 : ℝ) T, 0 < (t : ℝ) → (t : ℝ) < T → ∀ x : E3,
    HasDerivAt (timeExtension z.1.1.1.1 x) (z.1.2 (t,x)) (t : ℝ) at hgraph
  have hpoint : ∀ t : Set.Icc (0 : ℝ) T, ∀ x : E3,
      ‖z.1.1.1.1 (t,x)‖ ≤ (t : ℝ) * ‖z.1.2‖ := by
    intro t x
    by_cases hTzero : T = 0
    · have htval : (t : ℝ) = 0 := by
        exact le_antisymm (by simpa [hTzero] using t.2.2) t.2.1
      have ht : t = ⟨0, le_rfl, by simpa [hTzero] using hT⟩ :=
        Subtype.ext htval
      rw [ht]
      simpa using hzero x
    · have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hTzero)
      by_cases htzero : (t : ℝ) = 0
      · have ht : t = ⟨0, le_rfl, hT⟩ := Subtype.ext htzero
        rw [ht]
        simpa using hzero x
      · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm htzero)
        let f : ℝ → EuclideanSpace ℝ (Fin 6) :=
          fun s => timeExtension z.1.1.1.1 x s
        have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) T) := by
          apply continuousOn_iff_continuous_restrict.mpr
          let slice : Set.Icc (0 : ℝ) T → Slab T := fun u => (u,x)
          have hslice : Continuous slice := by
            change Continuous (fun u : Set.Icc (0 : ℝ) T => (u,x))
            exact continuous_id.prodMk continuous_const
          have heq : (Set.Icc (0 : ℝ) T).restrict f =
              fun u : Set.Icc (0 : ℝ) T => z.1.1.1.1 (u,x) := by
            funext u
            change (if h : (u : ℝ) ∈ Set.Icc (0 : ℝ) T then
              z.1.1.1.1 (⟨(u : ℝ), h⟩,x) else 0) = _
            rw [dif_pos u.2]
          rw [heq]
          exact z.1.1.1.1.continuous.comp hslice
        have hfzero : f 0 = 0 := by
          change timeExtension z.1.1.1.1 x 0 = 0
          have hmem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
          rw [timeExtension, dif_pos hmem]
          simpa using hzero x
        let C : ℝ := ‖z.1.2‖
        have hnear (a : ℝ) (ha : 0 < a) (hat : a ≤ (t : ℝ)) :
            ‖f (t : ℝ) - f a‖ ≤ C * ((t : ℝ) - a) := by
          have hsegcont : ContinuousOn f (Set.Icc a (t : ℝ)) :=
            hfcont.mono (by
              intro s hs
              exact ⟨(le_trans ha.le hs.1), (le_trans hs.2 t.2.2)⟩)
          have hderiv : ∀ s ∈ Set.Ico a (t : ℝ),
              HasDerivWithinAt f (timeExtension z.1.2 x s) (Set.Ici s) s := by
            intro s hs
            have hspos : 0 < s := lt_of_lt_of_le ha hs.1
            have hsT : s < T := lt_of_lt_of_le hs.2 t.2.2
            let u : Set.Icc (0 : ℝ) T := ⟨s, ⟨hspos.le, hsT.le⟩⟩
            have hd := hgraph u hspos hsT x
            have hsIcc : s ∈ Set.Icc (0 : ℝ) T := ⟨hspos.le, hsT.le⟩
            have hvalue : timeExtension z.1.2 x s = z.1.2 (u,x) := by
              simp [timeExtension, u, hsIcc]
            have hd' : HasDerivAt f (timeExtension z.1.2 x s) s := by
              change HasDerivAt (timeExtension z.1.1.1.1 x)
                (timeExtension z.1.2 x s) s
              rw [← hvalue] at hd
              exact hd
            exact hd'.hasDerivWithinAt
          have hderivBound : ∀ s ∈ Set.Ico a (t : ℝ),
              ‖timeExtension z.1.2 x s‖ ≤ C := by
            intro s hs
            have hspos : 0 < s := lt_of_lt_of_le ha hs.1
            have hsT : s < T := lt_of_lt_of_le hs.2 t.2.2
            let u : Set.Icc (0 : ℝ) T := ⟨s, ⟨hspos.le, hsT.le⟩⟩
            have hsIcc : s ∈ Set.Icc (0 : ℝ) T := ⟨hspos.le, hsT.le⟩
            have hvalue : timeExtension z.1.2 x s = z.1.2 (u,x) := by
              simp [timeExtension, u, hsIcc]
            rw [hvalue]
            exact BoundedContinuousFunction.norm_coe_le_norm z.1.2 (u,x)
          have hseg := norm_image_sub_le_of_norm_deriv_right_le_segment
            hsegcont hderiv hderivBound
          have htmem : (t : ℝ) ∈ Set.Icc a (t : ℝ) := ⟨hat, le_rfl⟩
          simpa [C] using hseg (t : ℝ) htmem
        let e : ℕ → ℝ := fun n => (t : ℝ) / ((n : ℝ) + 1)
        have he : Filter.Tendsto e Filter.atTop (𝓝 0) := by
          dsimp [e]
          simpa [div_eq_mul_inv] using
            (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (t : ℝ))
        have hepos (n : ℕ) : 0 < e n := by
          dsimp [e]
          positivity
        have hele (n : ℕ) : e n ≤ (t : ℝ) := by
          dsimp [e]
          apply (div_le_iff₀ (by positivity)).2
          nlinarith [mul_nonneg (le_of_lt htpos) (show 0 ≤ (n : ℝ) by positivity)]
        have hewithin : Filter.Tendsto e Filter.atTop (𝓝[Set.Icc (0 : ℝ) T] 0) :=
          tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within e he
            (Filter.Eventually.of_forall fun n =>
              ⟨(hepos n).le, (hele n).trans t.2.2⟩)
        have hfe : Filter.Tendsto (fun n => f (e n)) Filter.atTop (𝓝 (f 0)) :=
          (hfcont.continuousWithinAt ⟨le_rfl, hT⟩).tendsto.comp hewithin
        have hmain : Filter.Tendsto (fun n => C * ((t : ℝ) - e n)) Filter.atTop
            (𝓝 (C * (t : ℝ))) := by
          simpa using tendsto_const_nhds.mul (tendsto_const_nhds.sub he)
        have herr : Filter.Tendsto (fun n => ‖f (e n) - f 0‖) Filter.atTop (𝓝 0) := by
          have hsub : Filter.Tendsto (fun n => f (e n) - f 0) Filter.atTop (𝓝 (f 0 - f 0)) :=
            hfe.sub tendsto_const_nhds
          simpa [norm_zero] using hsub.norm
        have htotal : Filter.Tendsto
            (fun n => C * ((t : ℝ) - e n) + ‖f (e n) - f 0‖) Filter.atTop
            (𝓝 (C * (t : ℝ))) := by
          simpa using hmain.add herr
        have hineq (n : ℕ) :
            ‖f (t : ℝ) - f 0‖ ≤ C * ((t : ℝ) - e n) + ‖f (e n) - f 0‖ := by
          have h := hnear (e n) (hepos n) (hele n)
          calc
            ‖f (t : ℝ) - f 0‖ =
                ‖(f (t : ℝ) - f (e n)) + (f (e n) - f 0)‖ := by congr 1 <;> abel
            _ ≤ ‖f (t : ℝ) - f (e n)‖ + ‖f (e n) - f 0‖ := norm_add_le _ _
            _ ≤ C * ((t : ℝ) - e n) + ‖f (e n) - f 0‖ := add_le_add h le_rfl
        have hbound : ‖f (t : ℝ) - f 0‖ ≤ C * (t : ℝ) :=
          le_of_tendsto_of_tendsto tendsto_const_nhds htotal
            (Filter.Eventually.of_forall hineq)
        have hvalue : f (t : ℝ) = z.1.1.1.1 (t,x) := by
          change timeExtension z.1.1.1.1 x (t : ℝ) = z.1.1.1.1 (t,x)
          rw [timeExtension, dif_pos t.2]
        simpa [hvalue, hfzero, C, mul_comm] using hbound
  refine ⟨hpoint, ?_⟩
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hT (norm_nonneg _))).2
  intro p
  rcases p with ⟨t, x⟩
  exact (hpoint t x).trans (mul_le_mul_of_nonneg_right t.2.2 (norm_nonneg _))
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ZeroTraceValueSmallness
