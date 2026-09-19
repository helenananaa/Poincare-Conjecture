import ReferenceBridges.Transport.DiniInfApproximate
import ReferenceBridges.Transport.EpsilonIntrinsicDistance
import PoincareConjecture.ParallelMath.Variational.Core
import Mathlib
import HatcherLib.Ch1.Sphere
import PoincareConjecture.ParallelMath.Transport.TorusUniversal
import PoincareConjecture.Topology.FiberSaturation.Sphere

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology
open PoincareConjecture.ParallelMath.Transport.Reference
open PoincareConjecture.ParallelMath.Variational
namespace TransportReferenceSanity
/-- **Math.** The approximate-competitor Dini result works with a genuinely unattained infimum. -/
example : MorganTianLib.ForwardDiffQuotientLE
    (fun _t : ℝ => leastCost (fun x : Ioi (0 : ℝ) => (x : ℝ))) 0 0 := by
  letI : Nonempty (Ioi (0 : ℝ)) := ⟨⟨1, by norm_num⟩⟩
  have hinf : leastCost (fun x : Ioi (0 : ℝ) => (x : ℝ)) = 0 := by
    unfold leastCost
    have h : range (fun x : Ioi (0 : ℝ) => (x : ℝ)) = Ioi (0 : ℝ) := by
      ext x
      exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x,hx⟩,rfl⟩⟩
    rw [h]
    exact csInf_Ioi
  apply leastCost_forwardDiff_of_approximate_competitors
    (fun _t (x : Ioi (0 : ℝ)) => (x : ℝ)) 0 0 (fun _t x => x.property.le)
  intro eta heta
  refine ⟨1, by norm_num, ?_⟩
  intro h hh _hsmall
  refine ⟨⟨eta*h/2, by change 0 < eta*h/2; positivity⟩, ?_, ?_⟩
  · change eta*h/2 ≤ leastCost (fun x : Ioi (0 : ℝ) => (x : ℝ))+eta*h
    rw [hinf]
    nlinarith [mul_pos heta hh]
  · change eta*h/2 ≤ eta*h/2+(0+eta)*h
    nlinarith [mul_pos heta hh]

/-- **Math.** The covering result applies to the actual standard sphere and any twist. -/
example (phi : PoincareConjecture.Topology.FiberSaturation.Sphere2 ≃ₜ
    PoincareConjecture.Topology.FiberSaturation.Sphere2) :
    IsCoveringMap (PoincareConjecture.Topology.FiberSaturation.MappingTorus.proj phi 1) ∧
      SimplyConnectedSpace (PoincareConjecture.Topology.FiberSaturation.Sphere2 × ℝ) := by
  letI : SimplyConnectedSpace PoincareConjecture.Topology.FiberSaturation.Sphere2 :=
    HatcherLib.standardSphereSimplyConnected 0
  have h := PoincareConjecture.ParallelMath.Transport.mappingTorus_universal_cover_data
    phi 1 (by norm_num)
  exact ⟨h.1, h.2.1⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
/-- **Math.** The computed distances are the canonical Riemannian extended distances for the supplied metrics. -/
example {epsilon : ℝ} (g0 g : Riemannian.RiemannianMetric I M)
    (h : MorganTianLib.EpsilonClose epsilon g0 g) (x y : M) :
    ENNReal.ofReal (Real.sqrt (1-epsilon)) *
      @Manifold.riemannianEDist E _ _ H _ I M _ _ (MorganTianLib.metricENorm g0) x y ≤
      @Manifold.riemannianEDist E _ _ H _ I M _ _ (MorganTianLib.metricENorm g) x y ∧
    @Manifold.riemannianEDist E _ _ H _ I M _ _ (MorganTianLib.metricENorm g) x y ≤
      ENNReal.ofReal (Real.sqrt (1+epsilon)) *
        @Manifold.riemannianEDist E _ _ H _ I M _ _ (MorganTianLib.metricENorm g0) x y := by
  simpa only [MorganTianLib.metricIntrinsicEDist_eq_riemannianEDist] using
    epsilonClose_intrinsic_edist_twoSided g0 g h x y
end TransportReferenceSanity
