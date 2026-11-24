import YM.Integration.WilsonPositionSeparatedProfileLocalPurchase
import YM.Integration.WilsonReportingFittedWindows

/-! Every genuine differentiated factory singleton is priced by its original
input mass in the full correlated, signed local reporting experiment. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionSeparatedProfileLocalFitted
open Function Filter Set Finset MeasureTheory Metric Lattice RG Wilson Tree RG16 Precision PertExtension
open Source Labels RG05Readout.Address RG05Readout.Native
open OPE.Orbits MergeProof MergeProof.Accent
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction RG05Readout Pulse Many RG12
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonIncidentRegisteredMass WilsonPositionSeparatedProfileLocalPurchase
open private coefficient_mass from YM.Integration.WilsonReportingFittedWindows
open scoped Classical BigOperators Topology
variable {G:Gauge} {I:Type} [Fintype I] [DecidableEq I] (R:Run G)

theorem original (stoves:Poetry R.family.path.levels) (simple:G.Simple)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (RG16.Lambda R.family.path.levels m))
    (P:ChartRatio G) (hp:LocalRatio P) (J:Voice G) (clear:Clear G J) (d:I→ℕ) (ℓ:∀i,Letter (d i)) (s q grade:ℕ)
    (ord:depth R (fun i=>kept (ℓ i)) s q+5≤grade) (φ:Wave I) (compact:HasCompactSupport φ.val)
    {ε ρ:ℝ} (ep:0<ε) (pr:0<ρ) (sr:ρ<Chart.small G P) (rv:ρ≤J.r) :
    ∀ᶠm:ℕ in atTop,∀N (live:m+1<N) (per t:ℕ),(t:ℝ)≤R.family.path.levels.clock.hatBeta (m+1)^s→
      (∀i,R.family.ref (kept (ℓ i)) ≤ (m + 1) ∧ R.family.ref (d i) ≤ (m + 1)) →
      ∀(x:∀i,R.family.label (kept (ℓ i))) (r:ℝ) (ξ:Cloud I)
      (T:Forest (R.family.path.levels.clock.op m per).ratio) (χ:ℂ→L[ℝ]ℝ)
      (H:Config G (R.family.side (m+1) per)→ℝ),Envelope H→GaugeInvariant H→
      let y:=fun i=>(WilsonReportingFactorySingleton.measured R.makes (ℓ i) (x i) (m+1) N per) (ℓ i)
      Accepted R live P (depth R (fun i=>kept (ℓ i)) s q) grade ρ (fun i=>kept (ℓ i)) t y φ r ξ T χ H
        (ε * regulatorRun R.family N per (m+1)^q * (‖χ‖*∏i,mass R.family (kept (ℓ i)) (x i)) *
          Real.sqrt (∫U,‖H U‖^2 ∂scene R.family.path N per (m+1))) := by
  let B:ℝ:=2^Fintype.card I
  have bp:0<B:=pow_pos (by norm_num) _
  have fit : ∀ᶠk:ℕ in atTop,∀i:I,∀{N per:ℕ} (x:R.family.label (kept (ℓ i))),
      R.family.ref (kept (ℓ i))≤k→R.family.ref (d i)≤k→k≤N→
      size (C:=R.family) (WilsonReportingFactorySingleton.measured R.makes (ℓ i) x k N per)≤2*mass R.family (kept (ℓ i)) x := by
    rw [Filter.eventually_all];intro i
    filter_upwards [WilsonReportingFactorySingleton.fitted R.makes simple (d i)] with k fund N per x h e live
    exact fund (ℓ i) x h e live
  filter_upwards [(tendsto_add_atTop_nat 1).eventually fit,WilsonPositionSeparatedProfileLocalPurchase.original R stoves simple marks fees slow
    P hp J clear (fun i=>kept (ℓ i)) s q grade ord φ compact (div_pos ep bp) pr sr rv]
    with m fund sold N live per t span ages x r ξ T χ H eh gh y
  obtain ⟨w,reg,amount,actual⟩:=sold N live per t span y r ξ T χ H eh gh
  refine ⟨w,reg,amount.trans ?_,actual⟩
  let e:=fun i=>kept (ℓ i)
  have each (i:I):(R.family.labels.level (e i)).coeffSize (y i)≤2*mass R.family (e i) (x i):=
    (coefficient_mass (C:=R.family) R.makes (ℓ i) (x i) (m+1) N per).trans_le
      (fund i (x i) (ages i).1 (ages i).2 live.le)
  have total : originalMass R e y≤B*∏i,mass R.family (e i) (x i) := by
    calc
      _ ≤ ∏i,(2*mass R.family (e i) (x i)):=prod_le_prod (fun i _=>sum_nonneg fun _ _=>norm_nonneg _) (fun i _=>each i)
      _ = _ := by rw [prod_mul_distrib];simp [B]
  let g:=regulatorRun R.family N per (m+1)
  let X:=Real.sqrt (∫U,‖H U‖^2 ∂scene R.family.path N per (m+1))
  have gp:0≤g:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have xp:0≤X:=Real.sqrt_nonneg _
  have cost:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left total (norm_nonneg χ)) (mul_nonneg (div_nonneg ep.le bp.le) (pow_nonneg gp q))) xp
  apply cost.trans_eq
  change (ε/B*g^q)*(‖χ‖*(B*∏i,mass R.family (e i) (x i)))*X=ε*g^q*(‖χ‖*∏i,mass R.family (e i) (x i))*X
  field_simp [bp.ne']

end YM.Integration.WilsonPositionSeparatedProfileLocalFitted
