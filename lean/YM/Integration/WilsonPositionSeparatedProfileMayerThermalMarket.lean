import YM.Integration.WilsonPositionSeparatedProfileMayerLeadingMarket
import YM.Integration.WilsonPositionSeparatedProfileMayerMarketCalendar

/-! Every honest finite thermal order on the minimal occupied measured component before both regulators. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionSeparatedProfileMayerThermalMarket
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat.Legato
variable {G:Gauge} {c f L:Side} {S:StepData c f} {T:Tube G S} {F:Forest S.ratio} {R:Rep G f}
    {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W s μ C:ℝ} {o:Target.Order G W}
    {H:Cash W s μ L Q o C T R} {j n l k M:ℕ} {χ:Chi}

open WilsonPositionSeparatedProfileMayerMasks WilsonPositionSeparatedProfileMayerGateReturn
open WilsonCoherentMayerSubmission WilsonCoherentMayerOccurrences WilsonCoherentMayerHearing
open WilsonPositionSeparatedProfileMayerGateSafety LocalTaylorR2.Exponent
open Precision Coat Source Matrix Dict06 AnalyticBridge.LocalGaussianLaws ProbabilityTheory
open WilsonPositionSeparatedProfileMayerLeadingGaussian
variable {I:Type} [Fintype I]
open WilsonCoherentMayerEntry
private def tariff (run:Run G) (d:I→ℕ):ℝ:=∏i,∑a,unitPrice run (d i) a

private theorem unit_positive (run:Run G) (d:ℕ) (a:(run.family.labels.level d).Index):0≤unitPrice run d a:=zero_le_one.trans (le_max_left ..)
private theorem wallet_nonneg (run:Run G) {d:ℕ} (y:run.family.label d) (θ:ℝ) (χ:ℂ →L[ℝ] ℝ):0≤wallet run y θ χ:=
  mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun a _=>mul_nonneg (norm_nonneg _) (unit_positive run d a))
private theorem covered (run:Run G) (entry:Submitted run R I) (cap:∀i z,|entry.phase i z|≤‖z‖) (old:Team R) (vacant:old.own=∅):
    0≤bank entry old ∧ bank entry old≤tariff run entry.grade * WilsonCoherentReportingPivot.mass run entry.grade R.p.threshold entry.label:=by
  classical
  rw [WilsonPositionSeparatedProfileMayerGateReturn.bank,vacant,Finset.prod_empty,one_mul];constructor
  · exact Finset.prod_nonneg fun _ _=>wallet_nonneg ..
  rw [tariff,WilsonCoherentReportingPivot.counted,←Finset.prod_mul_distrib]
  apply Finset.prod_le_prod (fun _ _=>wallet_nonneg ..)
  intro i _
  have hc:‖entry.phase i‖≤1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z=>by simpa only [Real.norm_eq_abs,one_mul] using cap i z
  unfold wallet
  apply (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg fun a _=>mul_nonneg (norm_nonneg _) (unit_positive run (entry.grade i) a))).trans
  rw [one_mul,Finset.mul_sum]
  refine Finset.sum_le_sum fun a _=>?_ 
  rw [mul_comm];gcongr;apply Finset.single_le_sum (fun b _=>unit_positive run (entry.grade i) b) (Finset.mem_univ a)

theorem original (run:Run G) (d:I→ℕ) (P:Teller G) (L:Side) (D:Patch) (branch:D.Branches P.bind G) {W:ℝ} (o:Target.Order G W) (t capacity:ℕ) (ε:ℝ) (ep:0<ε):
    ∀ᶠs:ℝ in atTop,∀ {c f:Side} {S:StepData c f} (T:Tube G S) {R:Rep G f} {Q:ConnectedActivityE6.Target G P} {μ C:ℝ}
    (H:Cash W s μ L Q o C T R),S.patch=D→S.patch.L=L→0<R.beta→|Coat.gStep R.beta|≤1→0≤Pressure.temp s→Stamp T→
    ∀entry:Submitted run R I,d=entry.grade→(∀i z,|entry.phase i z|≤‖z‖)→∀old:Team R,old.own=∅→∀fresh:∀m∈old.own,∀i,m.turn≠(row entry i).turn,
    (sites entry T s).card≤capacity→∀loc:H.ThinP,loc.val=(together entry old fresh).signs S→∀ {j n k l M:ℕ} {χ:Chi} {r q a Y D' A b B C' ρ e uJ vJ θ K:ℝ},
    (N:Captain H j C' D' Y B A b r a q n χ)→Awning H N.conduit A b ρ e uJ vJ k l→Q.goal L s≤K→Mayer.Approved K θ j M→authorized H loc.val→Mayer.Start loc.val→
    let cash:=WilsonCoherentReportingPivot.mass run entry.grade R.p.threshold entry.label
    let column:=Laminate.column (together entry old fresh) loc.val H (χ:=χ) M (0:Orders M) (1:Config G c)
    |column-forecast entry T s o χ t|≤ε*(Coat.gStep R.beta)^t*cash:=by
  classical
  obtain ⟨Ctab,hc,E,rate,sold⟩:=WilsonPositionSeparatedProfileMayerLeadingMarket.original run d P L D branch o t (-(t:ℝ)-1)
  let a:ℝ:=capacity*tariff run d
  let b:=WilsonPositionSeparatedProfileMayerStencilPrice.budget run d t
  filter_upwards [sold,WilsonPositionSeparatedProfileMayerMarketCalendar.original P L D o t E rate a b Ctab hc ε ep] with s market fees
  intro c f S T R Q μ C H same patch hot scale temp stamped entry given cap old vacant fresh room₀ loc minimal j n k l M χ r q α Y D' A β B C' ρ e uJ vJ θ K N law room allow inside cohort
  specialize market T H same patch hot scale temp stamped entry given cap old vacant fresh loc minimal N law room allow inside cohort
  have stated:=fees T H same patch
  let cash:=WilsonCoherentReportingPivot.mass run entry.grade R.p.threshold entry.label
  have paid:0≤cash:=Finset.sum_nonneg fun _ _=>norm_nonneg _
  obtain ⟨bn,ticket⟩:=covered run entry cap old vacant
  have up:bank entry old≤tariff run d*cash:=by simpa only [given] using ticket
  have ta:0≤tariff run d:=Finset.prod_nonneg fun i _=>Finset.sum_nonneg fun j _=>unit_positive run (d i) j
  have ab:0≤a:=mul_nonneg (Nat.cast_nonneg _) ta
  have gate:(sites entry T s).card*E s*bank entry old≤|a*E s| * cash:=by
    calc _≤(sites entry T s).card * |E s| * bank entry old:=by gcongr;exact le_abs_self _
         _≤(capacity:ℝ) * |E s| * (tariff run d*cash):=by gcongr
         _=|a*E s| * cash:=by rw [abs_mul,abs_of_nonneg ab];dsimp [a];ring
  have cov:cash*b * |WilsonOriginalSignedSamplerMoment.fee T L P o t s|≤|b*WilsonOriginalSignedSamplerMoment.fee T L P o t s| * cash:=by
    rw [abs_mul];calc _≤cash * |b| * |WilsonOriginalSignedSamplerMoment.fee T L P o t s|:=by gcongr;exact le_abs_self _
                      _= _:=by ring
  apply market.trans
  change (sites entry T s).card*E s*bank entry old+cash*(Ctab*(Coat.gStep R.beta)^(t+1))+cash*b * |WilsonOriginalSignedSamplerMoment.fee T L P o t s|≤ε*(Coat.gStep R.beta)^t*cash
  linarith [mul_le_mul_of_nonneg_right stated paid]

end YM.Integration.WilsonPositionSeparatedProfileMayerThermalMarket
