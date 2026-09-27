import PoincareConjecture.ProofContract.Refinement20260927.AmbientApproximationLeaves
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory
open scoped Manifold ContDiff Topology
/-- **Math.** Raw Euclidean approximants need not preserve endpoints or lie in a tubular domain.
Their actual existence with uniform first-derivative approximation remains a research obligation. -/
structure AmbientApproximationData (N : CompactSmoothThree.{u})
    (g : Riemannian.RiemannianMetric (𝓡 3) N) (D : BasedSphereClass N) where
  reference : C(SweepDomain,N)
  ends : EqOn reference (ContinuousMap.const SweepDomain D.base) sweepoutEnds
  correct_class : reference.HomotopicRel D.reference.continuousMap sweepoutEnds
  differentiable : ∀ s : SweepParameter, MDifferentiable (𝓡 2) (𝓡 3) (fun p => reference (s,p))
  integrable : ∀ s : SweepParameter,
    Integrable (sphereEnergyDensity N g (fun p => reference (s,p))) sphereEnergyMeasure
  dimension : ℕ
  embedding : CompactEuclideanEmbedding N dimension
  C : ℝ
  C_nonneg : 0 ≤ C
  derivative_bound : ∀ (s : SweepParameter) p i,
    ‖embeddedSphereVector embedding (fun p => reference (s,p)) p i‖ ≤ C
  raw_approximants : ∀ delta : ℝ, 0 < delta → ∃ a : ℝ × Sphere2 → ApproxAmbient dimension,
    ContMDiff SweepModel 𝓘(ℝ,ApproxAmbient dimension) ∞ a ∧
    (∀ q : SweepDomain, dist (a ((q.1:ℝ),q.2)) (embedding.map (reference q)) < delta) ∧
    ∀ (s : SweepParameter) p i, ‖ambientSliceVector (fun z => a ((s:ℝ),z)) p i -
      embeddedSphereVector embedding (fun z => reference (s,z)) p i‖ ≤ delta
/-- **Math.** Four independent estimates turn raw ambient approximants into the required
smooth manifold-valued based sweepouts, preserving the original reference and embedding. -/
theorem AmbientApproximationData.toEmbedding (frames : EmbeddedNormalFrameStatement.{u})
    (control : CompactRetractionControlStatement.{u}) (chain : SphereCompositionEstimateStatement)
    (correct : AmbientEndpointCorrectionStatement) (confine : AmbientSweepoutConfinementStatement)
    {N : CompactSmoothThree.{u}} {g : Riemannian.RiemannianMetric (𝓡 3) N}
    {D : BasedSphereClass N} (r : AmbientApproximationData N g D) :
    ∃ out : EmbeddingApproximationData N g D, out.reference = r.reference := by
  let n := r.dimension
  let e := r.embedding
  obtain ⟨R,hR⟩ := retraction_from_embedded_frames frames N n e
  have hfix (p : N) : R.localRetract (e.map p) = p := by
    rw [← hR]
    exact (R.agrees _ (R.contains p)).trans (R.retract_embed p)
  let P := embeddedRetractMap R
  obtain ⟨hP,Q,hQ,ctrl⟩ := control N n R
  let F : C(SweepDomain,ApproxAmbient n) := e.map.comp r.reference
  have hFends : EqOn F (ContinuousMap.const SweepDomain (e.map D.base)) sweepoutEnds := by
    intro q hq
    exact congrArg e.map (r.ends hq)
  refine ⟨{ reference := r.reference
            ends := r.ends
            correct_class := r.correct_class
            differentiable := r.differentiable
            integrable := r.integrable
            dimension := n
            embedding := e
            C := r.C
            C_nonneg := r.C_nonneg
            derivative_bound := r.derivative_bound
            approximants := ?_ },rfl⟩
  intro eps heps
  let eta := min eps (eps/(Q+r.C+1))
  have hden : 0 < Q+r.C+1 := by linarith [r.C_nonneg]
  have heta : 0 < eta := lt_min heps (div_pos heps hden)
  have heta_eps : eta ≤ eps := min_le_left _ _
  have hcost : eta*(Q+r.C) ≤ eps := by
    have h := (le_div_iff₀ hden).mp (min_le_right eps (eps/(Q+r.C+1)))
    change eta*(Q+r.C+1) ≤ eps at h
    nlinarith
  obtain ⟨rho,hrho,hctrl⟩ := ctrl eta heta
  let tau := min (eta/2) (rho/4)
  have htau : 0 < tau := lt_min (by positivity) (by positivity)
  have htwo_eta : 2*tau ≤ eta := by have h := min_le_left (eta/2) (rho/4); change tau ≤ eta/2 at h; linarith
  have htwo_rho : 2*tau < rho := by have h := min_le_right (eta/2) (rho/4); change tau ≤ rho/4 at h; linarith
  obtain ⟨a,ha,hclose,hvec⟩ := r.raw_approximants tau htau
  obtain ⟨hc,hends,hcclose,hcvec⟩ := correct n a F (e.map D.base) tau htau ha hFends hclose hvec
  let c := correctAmbientEnds a (e.map D.base)
  have hxrange (q : SweepDomain) : F q ∈ range R.embed :=
    ⟨r.reference q,by change R.embed (r.reference q) = e.map (r.reference q); rw [hR]⟩
  have hdata (q : SweepDomain) := hctrl (F q) (hxrange q) (c ((q.1:ℝ),q.2))
    ((hcclose q).trans htwo_rho)
  have hcU : ∀ q : ℝ × Sphere2, q.1 ∈ Icc (0:ℝ) 1 → c q ∈ R.domain := by
    intro q hq
    exact (hdata (⟨q.1,hq⟩,q.2)).1
  obtain ⟨b,hb,heq,hbU⟩ := confine n c R.domain R.open_domain hc hcU
  have hbsame (q : SweepDomain) : b ((q.1:ℝ),q.2) = c ((q.1:ℝ),q.2) :=
    heq ⟨q.1.property,mem_univ _⟩
  let h : SmoothBasedSweepout N D.base := {
    map := R.localRetract ∘ b
    smooth := contMDiffOn_univ.mp (R.smooth_localRetract.comp hb.contMDiffOn (fun q _ => hbU q))
    ends := by
      intro p
      constructor
      · change R.localRetract (b (0,p)) = D.base
        rw [heq (by exact ⟨by norm_num,mem_univ _⟩),show c (0,p) = e.map D.base from (hends p).1]
        exact hfix _
      · change R.localRetract (b (1,p)) = D.base
        rw [heq (by exact ⟨by norm_num,mem_univ _⟩),show c (1,p) = e.map D.base from (hends p).2]
        exact hfix _ }
  refine ⟨h,?_,?_⟩
  · intro q
    have hval := (hdata q).2.1
    change dist (R.embed (R.localRetract (c ((q.1:ℝ),q.2)))) (F q) < eta at hval
    change dist (e.map (R.localRetract (b ((q.1:ℝ),q.2)))) (F q) < eps
    rw [hbsame q,← hR]
    exact hval.trans_le heta_eps
  · intro s p i
    let aa : Sphere2 → ApproxAmbient n := fun z => b ((s:ℝ),z)
    let bb : Sphere2 → ApproxAmbient n := fun z => F (s,z)
    let v := sphereEnergyFrame p i
    have hda : MDifferentiableAt (𝓡 2) 𝓘(ℝ,ApproxAmbient n) aa p :=
      ((hb.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable (by simp)) p
    have hdb : MDifferentiableAt (𝓡 2) 𝓘(ℝ,ApproxAmbient n) bb p :=
      ((e.smooth.mdifferentiable (by simp)).comp (r.differentiable s)) p
    have hbinside : bb p ∈ R.domain := by
      change e.map (r.reference (s,p)) ∈ R.domain
      rw [← hR]
      exact R.contains _
    have hdPa : DifferentiableAt ℝ P (aa p) :=
      (hP.contDiffAt (R.open_domain.mem_nhds (hbU ((s:ℝ),p)))).differentiableAt (by simp)
    have hdPb : DifferentiableAt ℝ P (bb p) :=
      (hP.contDiffAt (R.open_domain.mem_nhds hbinside)).differentiableAt (by simp)
    have hPb : P ∘ bb = bb := by
      funext z
      change R.embed (R.localRetract (e.map (r.reference (s,z)))) = e.map (r.reference (s,z))
      rw [hfix,hR]
    have hbounds := (hdata (s,p)).2.2
    have hdiff : ‖fderiv ℝ P (aa p) - fderiv ℝ P (bb p)‖ ≤ eta := by
      change ‖fderiv ℝ P (b ((s:ℝ),p)) - fderiv ℝ P (F (s,p))‖ ≤ eta
      rw [hbsame (s,p)]
      exact hbounds.1
    have hnorm : ‖fderiv ℝ P (aa p)‖ ≤ Q := by
      change ‖fderiv ℝ P (b ((s:ℝ),p))‖ ≤ Q
      rw [hbsame (s,p)]
      exact hbounds.2
    have haa : aa = fun z => c ((s:ℝ),z) := funext fun z => hbsame (s,z)
    have hdelta : ‖ambientDirectionalDerivative aa p v - ambientDirectionalDerivative bb p v‖ ≤ eta := by
      rw [haa]
      exact (hcvec s p i).trans htwo_eta
    have hC : ‖ambientDirectionalDerivative bb p v‖ ≤ r.C := r.derivative_bound s p i
    have result := chain n P aa bb p v Q r.C eta hda hdb hdPa hdPb hPb
      hQ r.C_nonneg heta.le hnorm hdiff hdelta hC
    have hm : e.map ∘ (fun z => h.map ((s:ℝ),z)) = P ∘ aa := by
      funext z
      change e.map (R.localRetract (b ((s:ℝ),z))) = R.embed (R.localRetract (b ((s:ℝ),z)))
      rw [hR]
    have hv : embeddedSphereVector e (fun z => h.map ((s:ℝ),z)) p i =
        ambientDirectionalDerivative (P ∘ aa) p v := by
      unfold embeddedSphereVector ambientDirectionalDerivative
      rw [hm]
    rw [hv]
    exact result.trans hcost
#print axioms AmbientApproximationData.toEmbedding
end PoincareConjecture.ProofContract.Refinement20260927
