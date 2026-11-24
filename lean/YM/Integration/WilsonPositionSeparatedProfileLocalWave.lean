import YM.Integration.WilsonLocalRegisteredMarginal
import YM.Integration.WilsonPositionSeparatedProfileReportingPrimary

/-! All signed locations of the original registered reporting wave under one
Wilson conditional law, compared with the retained local polynomial experiment. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileLocalWave
open Function Filter Set Finset MeasureTheory Metric Lattice RG Wilson Tree RG16 Precision PertExtension
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonReportingForestPivots WilsonCoherentForestMeasure WilsonCoherentForestReadout
open WilsonIncidentRegisteredMass WilsonCoherentMeasuredStencil WilsonCoherentMeasuredChart
open WilsonLocalReportingConditionalCost RG05Readout RG05Readout.Pulse WilsonReportingPlaquetteWindows
open scoped Classical BigOperators Topology
variable {G:Gauge} {I:Type} [Fintype I] [DecidableEq I] (R:Run G) {m N per:ℕ}

abbrev ink (φ:Wave I) (r:ℝ) (ξ:Cloud I) (o:I→Site (R.family.side (m+1) per)) : ℂ :=
  φ.val (fun i=>r⁻¹ • (R.family.S.place (o i)-ξ i))

def charge (d:I→ℕ) (y:∀i,R.family.label (d i)) (o:I→Site (R.family.side (m+1) per)) (c:ℂ) (χ:ℂ→L[ℝ]ℝ)
    (H Z:Config G (R.family.side (m+1) per)→ℝ) (q:ℕ) (ε:ℝ) (V:Config G (R.family.side m per)) :=
  let C:=cold R m per d o
  let δ:=(ε/2)*regulatorRun R.family N per (m+1)^q
  let A:=‖χ‖*‖c‖*originalMass R d y
  let F:=fun U=>H U*Z U
  let good (h:Config G (R.family.side (m+1) per)→ℝ):=actualAverage R.family (N:=N) (C.indicator (fun U=>|h U|)) V
  (δ*good F+(2*δ*A)*good H)+actualAverage R.family (N:=N) (Cᶜ.indicator (fun U=>|F U|)) V

def retained (live:m+1<N) (P:ChartRatio G) (q grade:ℕ) (ρ:ℝ) (d:I→ℕ) (y:∀i,R.family.label (d i))
    (o:I→Site (R.family.side (m+1) per)) (T:Forest (R.family.path.levels.clock.op m per).ratio)
    (c:ℂ) (χ:ℂ→L[ℝ]ℝ) (H:Config G (R.family.side (m+1) per)→ℝ) (V:Config G (R.family.side m per)) :=
  let B:=incident R T d o
  let θ:=(R.family.path.rep N per (m+1)).p.threshold
  ∫z in panel R m per d o T ρ,WilsonLocalRetainedReportingWeight.adjusted P q R live grade T B V z *
    H (state T B z) * χ (c*polynomial T B R d θ y o (q+2*reserve R d) z) ∂law P ρ T B

theorem original (stoves:Poetry R.family.path.levels) (simple:G.Simple)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (RG16.Lambda R.family.path.levels m))
    (P:ChartRatio G) (hp:LocalRatio P) (J:Voice G) (clear:Clear G J) (d:I→ℕ) (q grade:ℕ) (ord:q+5≤grade)
    {ε ρ:ℝ} (ep:0<ε) (pr:0<ρ) (sr:ρ<Chart.small G P) (rv:ρ≤J.r) :
    ∀ᶠm:ℕ in atTop,∀N (live:m+1<N) per t (y:∀i,R.family.label (d i)) (φ:Wave I) (r:ℝ) (ξ:Cloud I)
      (T:Forest (R.family.path.levels.clock.op m per).ratio) (χ:ℂ→L[ℝ]ℝ)
      (H:Config G (R.family.side (m+1) per)→ℝ),Envelope H→GaugeInvariant H→
    let S:=placements (V:=I) R.family (m+1) per t
    let c:=fun z:S=>ink R φ r ξ z.val
    let Z:=fun z:S=>mark R d z.val (R.family.path.rep N per (m+1)).p.threshold y (c z) χ
    let bill:=fun z:S=>charge R (N:=N) d y z.val (c z) χ H (Z z) q ε
    let model:=fun z:S=>retained R live P q grade ρ d y z.val T (c z) χ H
    let upper:=scene R.family.path N per (m+1)
    let lower:=scene R.family.path N per m
    Integrable (fun V=>∑z:S,bill z V) lower ∧
    (∫V,∑z:S,bill z V ∂lower)≤ε*regulatorRun R.family N per (m+1)^q*
      ∑z:S,(Real.sqrt (∫U,‖H U*Z z U‖^2 ∂upper)+‖χ‖*‖c z‖*originalMass R d y*Real.sqrt (∫U,‖H U‖^2 ∂upper)) ∧
    ∀V,|actualAverage R.family (N:=N) (fun U=>H U*χ (WilsonPositionSeparatedProfileReportingPrimary.read R d (m+1) N per t y φ r ξ U)) V-
        ∑z:S,model z V|≤∑z:S,bill z V := by
  filter_upwards [WilsonLocalRegisteredMarginal.original R stoves simple marks fees slow P hp J clear d q grade ord ep pr sr rv]
    with m market N live per t y φ r ξ T χ H eh gh
  intro S c Z bill model upper lower
  have finance (z:S):= (market N live per y z.val T (c z) χ H eh gh).2
  have each (z:S):Integrable (bill z) lower ∧
      (∫V,bill z V ∂lower)≤ε*regulatorRun R.family N per (m+1)^q*
        (Real.sqrt (∫U,‖H U*Z z U‖^2 ∂upper)+‖χ‖*‖c z‖*originalMass R d y*Real.sqrt (∫U,‖H U‖^2 ∂upper)) ∧
      ∀V,|actualAverage R.family (N:=N) (fun U=>H U*Z z U) V-model z V|≤bill z V:=finance z
  refine ⟨integrable_finsetSum _ (fun z _=>(each z).1),?_,?_⟩
  · rw [integral_finsetSum _ (fun z _=>(each z).1),Finset.mul_sum]
    exact Finset.sum_le_sum fun z _=>(each z).2.1
  · intro V
    have payable (z:S):=eh.mul (legitimate R d z.val (R.family.path.rep N per (m+1)).p.threshold y (c z) χ).1
    have integrable (z:S):Integrable (fun U=>actualConditionalDensity R.family N per m V U • (H U*Z z U)) (prior G _) := by
      obtain ⟨ms,B,uniform⟩:=payable z
      exact actualAverage_integrable R.family R.makes live.le ms.aestronglyMeasurable uniform V
    have sum : actualAverage R.family (N:=N) (fun U=>H U*χ (WilsonPositionSeparatedProfileReportingPrimary.read R d (m+1) N per t y φ r ξ U)) V=
        ∑z:S,actualAverage R.family (N:=N) (fun U=>H U*Z z U) V := by
      unfold actualAverage
      rw [←integral_finsetSum _ fun z _=>integrable z]
      apply integral_congr_ae
      filter_upwards with U
      simp only [WilsonPositionSeparatedProfileReportingPrimary.read,map_sum,Finset.mul_sum,Finset.smul_sum]
      rfl
    rw [sum,←Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z _=>(each z).2.2 V)

end YM.Integration.WilsonPositionSeparatedProfileLocalWave
