import YM.Integration.FVA1Physical.CommonCover.ForestWilsonReading

/-! At finite coupling the continued model may suppress a gauge-invariant
exceptional set while preserving the entire independently prescribed Wilson
table. The action, Gaussian, Haar Jacobian, all marks and the joint vacuum
division enter the original RG02 prescription. The penalty only changes its
off-chart continuation. The physical cost of a change of law is separate. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.FVA1Physical.OlderPrice
open Filter Function Set Finset RG Wilson Gauge Precision Tree Lattice Exterior
open Comparison.RG02 Order Marker Multi Integral Actual
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {I : Type} [DecidableEq I] [Fintype I] {R : Census I} {G : Gauge} {c f : Side}
variable {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}

/-- The supplement is measured in action units; the physical inverse
temperature cancels exactly the two powers of g in the added supplement. -/
def dampedWilson (W : Bulk.Colors R G f) (A : Set (Config G f)) (d : ℝ→ℝ) : Bulk.Colors R G f where
  vac g U := if U∈A then W.vac g U else W.vac g U+g^2*d g
  mark := W.mark
  power := W.power

private theorem represented_home :
    Tendsto (fun z : ℝ × fieldDir G f 1 => represent z.2) (𝓝 0) (𝓝 (1:Config G f)) := by
  have hc : Continuous (fun z : ℝ × fieldDir G f 1 => represent z.2) := by
    apply continuous_pi;intro e
    simp only [Work.F03.represent_link]
    exact G.lieExp_cont.comp ((continuous_apply _).comp continuous_snd)
  have zero : represent (0:fieldDir G f 1)=1 := by
    funext e;simp only [Work.F03.represent_link,Pi.zero_apply,G.mat_lieExp_zero,Pi.one_apply]
  simpa only [Prod.snd_zero,zero] using hc.tendsto 0

omit [Fintype I] in
theorem damped_wilson_well (W : Bulk.Colors R G f) (well : Bulk.Well W)
    (A : Set (Config G f)) (an:A∈𝓝 1) (am:MeasurableSet A)
    (ag:∀k U,Lattice.gauge k U∈A ↔ U∈A) (d : ℝ→ℝ) : Bulk.Well (dampedWilson W A d) := by
  refine ⟨well.suppose_vac.depends ?_,well.suppose_mark,?_,well.gauges,?_,well.prices⟩
  · filter_upwards [represented_home.eventually an] with z hz
    change represent z.2∈A at hz
    change W.vac z.1 (represent z.2)=if represent z.2∈A then _ else _
    rw [if_pos hz]
  · intro h k U
    change (if Lattice.gauge k U∈A then W.vac h (Lattice.gauge k U) else W.vac h (Lattice.gauge k U)+h^2*d h)=_
    simp only [ag,well.natural h k U];rfl
  · intro h
    exact Envelope.piece am (well.envelope h) ((well.envelope h).add (Envelope.const _))

omit [Fintype I] in
theorem damped_wilson_weight (W : Bulk.Colors R G f) (A:Set (Config G f)) (d:ℝ→ℝ)
    (g c₀:ℝ) (hg:g≠0) (U:Config G f) :
    weight g c₀ U (dampedWilson W A d) p P =
      (if U∈A then 1 else Real.exp (-d g))*weight g c₀ U W p P := by
  by_cases h : U∈A
  · simp only [Integral.weight,localClassic,dampedWilson,if_pos h,one_mul]
  · simp only [Integral.weight,localClassic,dampedWilson,if_neg h,←Real.exp_add]
    congr 1
    unfold temperature
    field_simp [hg];ring

theorem damped_wilson_coefficients (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (t:S.Choices)
    (W : Bulk.Colors R G f) (A:Set (Config G f)) (an:A∈𝓝 1) (d:ℝ→ℝ) (x:fieldDir G c 1) (m:ℕ) :
    Bulk.Fk K F t (dampedWilson W A d) x m=Bulk.Fk K F t W x m := by
  let J:=Bulk.Joint S F (G:=G)
  have live : ContinuousAt (Work.F03.live (G:=G) F) 0:=by
    apply continuousAt_pi.mpr;intro e
    exact (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.tendsto_nhds_iff.mpr
      (Work.F03.live_smooth (G:=G) F e).continuousAt.tendsto
  have near : ∀ᶠ z:J in 𝓝 0,Work.F03.live F z.2∈A:= by
    have ht:=live.tendsto.comp (continuous_snd.tendsto (0:J))
    rw [Work.F03.live_zero] at ht
    exact ht.eventually an
  have ge : Bulk.geometric K F t (dampedWilson W A d) =ᶠ[𝓝 0] Bulk.geometric K F t W := by
    filter_upwards [near] with z hz
    change Work.F03.live F z.2∈A at hz
    simp only [Bulk.geometric,Bulk.fee,Bulk.supplement,Bulk.posed,dampedWilson,if_pos hz]
  have generators (i:Hot (Board R m)) :
      Assembly.generator (Bulk.stage K F x) (Bulk.hinge F) W.power (Bulk.markFn S F W)
        (Bulk.geometric K F t (dampedWilson W A d)) m i =
      Assembly.generator (Bulk.stage K F x) (Bulk.hinge F) W.power (Bulk.markFn S F W)
        (Bulk.geometric K F t W) m i := by
    unfold Assembly.generator Assembly.naked
    simp_rw [(ge.iteratedFDeriv ℝ _).eq_of_nhds]
  unfold Bulk.Fk Assembly.prescription
  change Cumulants.Cloud.prescription (K.covariance F t) (K.symm F t) 0
    (Assembly.generator (Bulk.stage K F x) (Bulk.hinge F) W.power (Bulk.markFn S F W) (Bulk.geometric K F t (dampedWilson W A d)) m) = _
  rw [funext generators]

end YM.Integration.FVA1Physical.OlderPrice
