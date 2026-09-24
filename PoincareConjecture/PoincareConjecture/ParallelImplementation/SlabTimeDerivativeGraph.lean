import PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open scoped Topology BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
def timeExtension {T : ℝ} (F : Slab T →ᵇ E6) (x : E3) (s : ℝ) : E6 := by
  classical
  exact if hs : s ∈ Set.Icc (0:ℝ) T then F (⟨s, hs⟩, x) else 0
def slabTimeDerivativeGraph (T : ℝ) :
    Set ((Slab T →ᵇ E6) × (Slab T →ᵇ E6)) :=
  {z | ∀ t : Set.Icc (0:ℝ) T, 0 < (t:ℝ) → (t:ℝ) < T → ∀ x : E3,
    HasDerivAt (timeExtension z.1 x) (z.2 (t,x)) (t:ℝ)}
/-- Uniform limits retain actual interior time derivatives on the fixed closed slab. -/
theorem slab_time_derivative_graph_closed (T : ℝ) :
    IsClosed (slabTimeDerivativeGraph T) :=
/- SWARM_PROOF_BEGIN -/
by
  apply IsSeqClosed.isClosed
  intro seq z hseq hlim
  have hlim₁ : Filter.Tendsto (fun n => (seq n).1) Filter.atTop (𝓝 z.1) :=
    hlim.fst_nhds
  have hlim₂ : Filter.Tendsto (fun n => (seq n).2) Filter.atTop (𝓝 z.2) :=
    hlim.snd_nhds
  have zeroExtension_uniform
      {F : ℕ → Slab T →ᵇ E6} {f : Slab T →ᵇ E6}
      (hF : Filter.Tendsto F Filter.atTop (𝓝 f)) (x : E3) :
      TendstoUniformly (fun n s => timeExtension (F n) x s)
        (timeExtension f x) Filter.atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [(Metric.tendsto_nhds.mp hF) ε hε] with n hn
    intro s
    by_cases hs : s ∈ Set.Icc (0 : ℝ) T
    · simp only [timeExtension, dif_pos hs]
      exact lt_of_le_of_lt
        (BoundedContinuousFunction.dist_coe_le_dist
          (f := f) (g := F n) ((⟨s, hs⟩, x) : Slab T))
        (by simpa [dist_comm] using hn)
    · simpa [timeExtension, hs] using hε
  have hfuniform := zeroExtension_uniform hlim₁
  have hderivUniformAll := zeroExtension_uniform hlim₂
  have hderivUniform (x : E3) : TendstoUniformlyOn
      (fun n s => timeExtension (seq n).2 x s)
      (timeExtension z.2 x) Filter.atTop (Set.Ioo (0 : ℝ) T) := by
    exact (tendstoUniformlyOn_univ.mpr (hderivUniformAll x)).mono (Set.subset_univ _)
  rw [slabTimeDerivativeGraph]
  intro t ht0 htT x
  let tx : Set.Icc (0 : ℝ) T := ⟨(t : ℝ), ⟨ht0.le, htT.le⟩⟩
  have hderiv : ∀ᶠ n in Filter.atTop, ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt (fun s => timeExtension (seq n).1 x s)
        (timeExtension (seq n).2 x s) s := by
    filter_upwards [Filter.Eventually.of_forall hseq] with n hn
    intro s hs
    let ts : Set.Icc (0 : ℝ) T := ⟨s, ⟨hs.1.le, hs.2.le⟩⟩
    have h := hn ts hs.1 hs.2 x
    have hv : timeExtension (seq n).2 x s = (seq n).2 (ts, x) := by
      simp [timeExtension, ts, hs.1.le, hs.2.le]
    simpa only [hv] using h
  have hpointwise : ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) T →
      Filter.Tendsto (fun n => timeExtension (seq n).1 x s) Filter.atTop
        (𝓝 (timeExtension z.1 x s)) := by
    intro s hs
    exact (hfuniform x).tendsto_at s
  have htIoo : (t : ℝ) ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hlimderiv := hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo
    (hderivUniform x) hderiv hpointwise htIoo
  simpa [timeExtension, tx, Set.mem_Icc, ht0.le, htT.le] using hlimderiv
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph
