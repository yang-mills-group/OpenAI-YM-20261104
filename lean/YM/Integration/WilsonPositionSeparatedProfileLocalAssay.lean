import YM.Integration.WilsonPositionSeparatedProfileLocalRegular
import YM.Integration.WilsonCoherentEarlier

/-! An all-order finite signed comparison under the actual Wilson measure.
The changed local action retains the two partition functions of the same
exterior. Both the coarse retained program and the physical read are integrable. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionSeparatedProfileLocalAssay
open Function Filter Set Finset MeasureTheory Metric Lattice RG Wilson Tree RG16 Precision PertExtension
open Source Labels RG05Readout.Address RG05Readout.Native
open OPE.Orbits MergeProof MergeProof.Accent
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction RG05Readout Pulse Many RG12
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonIncidentRegisteredMass WilsonPositionSeparatedProfileLocalPurchase
open private coefficient_mass from YM.Integration.WilsonReportingFittedWindows
open WilsonPositionSeparatedProfileLocalWave WilsonRegisteredPlaquetteReading WilsonReportingPlaquetteWindows
open scoped Classical BigOperators Topology
variable {G:Gauge} {I:Type} [Fintype I] [DecidableEq I] (R:Run G)

def field {k N per:ℕ} (d:I→ℕ) (t:ℕ) (y:∀i,R.family.label (d i)) (φ:Wave I) (r:ℝ) (ξ:Cloud I)
    (χ:ℂ→L[ℝ]ℝ) (H:Config G (R.family.side k per)→ℝ) (U:Config G (R.family.side k per)) :=
  H U*χ (WilsonPositionSeparatedProfileReportingPrimary.read R d k N per t y φ r ξ U)

def model {m N per:ℕ} (live:m+1<N) (P:ChartRatio G) (q grade:ℕ) (ρ:ℝ)
    (d:I→ℕ) (t:ℕ) (y:∀i,R.family.label (d i)) (φ:Wave I) (r:ℝ) (ξ:Cloud I)
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (χ:ℂ→L[ℝ]ℝ)
    (H:Config G (R.family.side (m+1) per)→ℝ) (V:Config G (R.family.side m per)) :=
  ∑z:placements (V:=I) R.family (m+1) per t,
    retained R live P q grade ρ d y z.val T (ink R φ r ξ z.val) χ H V

def Measured {m N per:ℕ} (F:Config G (R.family.side (m+1) per)→ℝ)
    (M:Config G (R.family.side m per)→ℝ) (target:ℝ) : Prop :=
  let lower:=scene R.family.path N per m
  let upper:=scene R.family.path N per (m+1)
  Integrable M lower ∧
    (∫V,‖actualAverage R.family (N:=N) F V-M V‖ ∂lower)≤target ∧
    |(∫U,F U ∂upper)-(∫V,M V ∂lower)|≤target

private theorem physical {k N per:ℕ} (d:I→ℕ) (t:ℕ) (y:∀i,R.family.label (d i)) (φ:Wave I)
    (r:ℝ) (ξ:Cloud I) (χ:ℂ→L[ℝ]ℝ) (H:Config G (R.family.side k per)→ℝ) (eh:Envelope H) :
    Envelope (field R (N:=N) d t y φ r ξ χ H) := by
  have cont:Continuous (WilsonPositionSeparatedProfileReportingPrimary.read R d k N per t y φ r ξ) := by
    apply continuous_finsetSum;intro z _;apply continuous_const.mul
    apply continuous_finsetProd;intro i _;exact (R.family.localSection (d i)).continuous_places _ _
  have c:=χ.continuous.comp cont
  obtain ⟨b,hb⟩:=isCompact_univ.exists_bound_of_continuousOn c.continuousOn
  exact eh.mul ⟨c.measurable,b,fun U=>hb U (mem_univ _)⟩

private theorem paid {m N per:ℕ} (live:m+1≤N) {F:Config G (R.family.side (m+1) per)→ℝ}
    (ef:Envelope F) {M w:Config G (R.family.side m per)→ℝ} (em:Measurable M) {target:ℝ}
    (ew:Integrable w (scene R.family.path N per m)) (price:(∫V,w V ∂scene R.family.path N per m)≤target)
    (dom:∀V,|actualAverage R.family (N:=N) F V-M V|≤w V) : Measured R (N:=N) F M target := by
  let μ:=scene R.family.path N per m
  letI:IsProbabilityMeasure μ:=probability (p:=per) R.makes.wilson ((Nat.le_succ m).trans live)
  let f:=actualAverage R.family (N:=N) F
  have h:=WilsonCoherentEarlier.averaged R.family R.makes live ef
  have diff:Integrable (fun V=>f V-M V) μ:=ew.mono' ((h.meas.sub em).aestronglyMeasurable) (Eventually.of_forall (fun V=>by simpa only [Real.norm_eq_abs] using dom V))
  have fi:Integrable f μ:=h.integrable _
  have mi:Integrable M μ:=(fi.sub diff).congr (Eventually.of_forall (fun V=>by change f V-(f V-M V)=M V; abel))
  have charged:(∫V,‖f V-M V‖ ∂μ)≤target:=(integral_mono diff.norm ew (fun V=>by simpa only [Real.norm_eq_abs] using dom V)).trans price
  have one:actualTransport R.family (N:=N) F (Nat.le_succ m)=f:=by
    rw [actualTransport_step R.family R.makes live F (Nat.lt_succ_self m),actualTransport_base R.family R.makes live]
  obtain ⟨b,bound⟩:=ef.cost
  have first:=actualTransport_weighted_integrable R.family R.makes live (ef.meas.aestronglyMeasurable (μ:=prior G _)) bound le_rfl
  rw [actualTransport_base R.family R.makes live] at first
  have mean:=actualScene_transport R.family R.makes live first (Nat.le_succ m)
  rw [one] at mean
  refine ⟨mi,charged,?_⟩
  rw [←mean,←integral_sub fi mi,←Real.norm_eq_abs]
  exact (norm_integral_le_integral_norm _).trans charged

theorem original (stoves:Poetry R.family.path.levels) (simple:G.Simple)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (RG16.Lambda R.family.path.levels m))
    (P:ChartRatio G) (hp:LocalRatio P) (J:Voice G) (clear:Clear G J) (d:I→ℕ) (ℓ:∀i,Letter (d i)) (s q grade:ℕ)
    (ord:depth R (fun i=>kept (ℓ i)) s q+5≤grade) (φ:Wave I) (compact:HasCompactSupport φ.val)
    {ε ρ:ℝ} (ep:0<ε) (pr:0<ρ) (sr:ρ<Chart.small G P) (rv:ρ≤J.r) :
    ∀ᶠm:ℕ in atTop,∀N (live:m+1<N) (per t:ℕ),(t:ℝ)≤R.family.path.levels.clock.hatBeta (m+1)^s→
      (∀i,R.family.ref (kept (ℓ i)) ≤ (m+1) ∧ R.family.ref (d i) ≤ (m+1)) →
      ∀(x:∀i,R.family.label (kept (ℓ i))) (r:ℝ) (ξ:Cloud I)
      (T:Forest (R.family.path.levels.clock.op m per).ratio) (χ:ℂ→L[ℝ]ℝ)
      (H:Config G (R.family.side (m+1) per)→ℝ),Envelope H→GaugeInvariant H→
      let D:=fun i=>kept (ℓ i)
      let y:=fun i=>(WilsonReportingFactorySingleton.measured R.makes (ℓ i) (x i) (m+1) N per) (ℓ i)
      Measured R (N:=N) (field R (N:=N) D t y φ r ξ χ H)
        (model R live P (depth R D s q) grade ρ D t y φ r ξ T χ H)
        (ε*regulatorRun R.family N per (m+1)^q*(‖χ‖*∏i,mass R.family (D i) (x i))*
          Real.sqrt (∫U,‖H U‖^2 ∂scene R.family.path N per (m+1))) := by
  let D:=fun i=>kept (ℓ i)
  filter_upwards [WilsonPositionSeparatedProfileLocalFitted.original R stoves simple marks fees slow P hp J clear d ℓ s q grade ord φ compact ep pr sr rv,
    WilsonPositionSeparatedProfileLocalRegular.original (I:=I) R simple marks fees P hp pr sr (depth R D s q) grade]
    with m offer regular N live per t small admissible x r ξ T χ H env gi
  let y:=fun i=>(WilsonReportingFactorySingleton.measured R.makes (ℓ i) (x i) (m+1) N per) (ℓ i)
  obtain ⟨w,ok,fee,dom⟩:=offer N live per t small admissible x r ξ T χ H env gi
  have mm:Measurable (model R live P (depth R D s q) grade ρ D t y φ r ξ T χ H):=by
    unfold model;apply Finset.measurable_sum;intro z _;exact regular N live per D y z.val T (ink R φ r ξ z.val) χ H env.meas
  exact paid R live.le (physical R D t y φ r ξ χ H env) mm ok fee dom

end YM.Integration.WilsonPositionSeparatedProfileLocalAssay
