import YM.Integration.WilsonInvariantActionFineSource
import YM.Integration.WilsonMatrixTicketLanesSelectedNormalization
import YM.Integration.WilsonMatrixTicketLanesRegisteredLoss

namespace YM.Integration.WilsonInvariantActionFineReserve
open Function Filter Set Finset MeasureTheory Lattice Wilson RG RG.Shoot Marker OPE.Therm Comparison.RG02
open Comparison.Density.RenderM Comparison.Density.RenderM.Token ActualRunPacketRetuning
open LocalComparison FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric Pert.Asymptotics
open ManuscriptQLocalOriginalConditionalTail ManuscriptQLocalRegularConditional ManuscriptQLocalSourceFourier
open RG.Supply Next.Rank Push.GridApprox WardBin.Wheels
open MergeProof PhysicalNext.Repeat.Legato PhysicalNext.Repeat Next.Scheduling Next.Scheduling.Clock
open Push.PriceCompiler Next.Foundations Source RG3.Script.Picnic PhysicalNext.ThroughLaunch WilsonLimitConstruction
open Actual Order IterationFour IterationFour.Vacuum
open WilsonInvariantActionTransportedOld WilsonInvariantActionMixedMaterial
open RG16 PertExtension Tree Precision RG17 RG12 Extraction Spec OPE Table SharpGram.Lenses Pier.Lair Overlay PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
open MergeProof.Accent


open OPE.Therm OriginalMarkedBirthStencil
open Extra.Trajectories


variable {V:Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {G:Gauge} {B:MS.Local.Physical.Deck G} (R:Run G) (simple:G.Simple)
variable (u:V→MS.Rake.Label B) (J:Request V) (A:NumericSchedule R.family J)
variable (Q:MS.Land.Prescription B)
local notation "J₀"=>ActualOriginalQPointSetup.request R u J
local notation "Γ₀"=>Stock.census V

private theorem settle {H C b g ε:ℝ} (e p q:ℕ) (hh:0≤H) (hc:0<C) (gp:0<g) (hp:0<ε)
    (hfund:H≤C*b^e) (rate:b^(e*(p+1)) ≤ (2:ℝ)^(e*(p+1))/g^(2*(e*(p+1)))):
    H^(p+1)*(ε/(C^(p+1)*(2:ℝ)^(e*(p+1)))*g^(q+2*(e*(p+1))))≤ε*g^q:=by
  let n:=e*(p+1)
  have hbound:H^(p+1)≤C^(p+1)*((2:ℝ)^n/g^(2*n)):=calc
    _≤(C*b^e)^(p+1):=pow_le_pow_left₀ hh hfund _
    _=C^(p+1)*b^n:=by rw [mul_pow,pow_mul]
    _≤_:=mul_le_mul_of_nonneg_left rate (pow_nonneg hc.le _)
  change H^(p+1)*(ε/(C^(p+1)*(2:ℝ)^n)*g^(q+2*n))≤_
  refine (mul_le_mul_of_nonneg_right hbound (by positivity)).trans_eq ?_
  rw [pow_add]
  field_simp [hc.ne',gp.ne']
  ring

theorem original (warm:Poetry R.family.path.levels) (μ:ℝ) (K p q:ℕ) {ε:ℝ} (hp:0<ε):
    ∀ᶠ m:ℕ in atTop, ∀(d:LocalFormal.Datum R.family (Γ₀)), d.level=m →
      ∀(o:V→Site (R.family.side (d.level+1) d.period)) (orders:V→ℕ), (∀i,orders i≤K) →
      ∀x:IndependentTests (J₀).tests,
      let stamp:=WilsonMatrixTicketLanesSelectedNormalization.stamp R μ d
      let charge:=ActualOriginalQInitialInput.normalizer R simple u J A d Q o stamp orders
      let X:=WilsonInvariantActionFineSource.plain R simple u J A d Q o stamp orders x
      let Y:=WilsonInvariantActionFineSource.held R simple u J A d Q o stamp orders x
      let loss:=fun T=>(charge*Poly.price (fun _:V=>1) (X T-Y T))^(p+1)
      let ν:=scene R.family.path d.cutoff d.period (d.level+1)
      Integrable loss ν ∧ (∫T,loss T ∂ν)≤ε*(Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1))^q:=by
  obtain ⟨C,hC,e,normal⟩:=WilsonMatrixTicketLanesSelectedNormalization.purchased R simple u J A Q μ K
  let n:=e*(p+1)
  have cash:=OriginalMarkedHistoryBirth.physical R simple u J A warm p (q+2*n) (ε:=ε/(C^(p+1)*(2:ℝ)^n))
    (div_pos hp (mul_pos (pow_pos hC _) (pow_pos (by norm_num : (0:ℝ)<2) _)))
  filter_upwards [cash,eventually_ge_atTop (ActualOriginalQLayout.referenceLevel R u)] with m fuel ref
  intro d md o orders ranks x stamp charge X Y loss ν
  let g:=Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
  have ready:ActualOriginalQLayout.referenceLevel R u≤d.level+1:=by omega
  have row(T:_):OriginalMarkedHistoryBirth.response R simple u J A d Q o stamp orders x le_rfl T=X T-Y T:=
    WilsonInvariantActionFineSource.birth R simple u J A d Q o stamp orders x ready T
  have owed:=fuel d md Q o stamp orders x (d.level+1) le_rfl
  let value:=fun T=>(Poly.price (fun _:V=>1) (X T-Y T))^(p+1)
  change Integrable (fun T=>(Poly.price (fun _:V=>1)
    (OriginalMarkedHistoryBirth.response R simple u J A d Q o stamp orders x le_rfl T))^(p+1)) ν ∧ _ at owed
  simp only [row] at owed
  have receipt:Integrable value ν ∧ (∫T,value T ∂ν)≤ε/(C^(p+1)*(2:ℝ)^n)*g^(q+2*n):=owed
  have factor:loss=fun T=>charge^(p+1)*value T:=funext fun _=>mul_pow _ _ _
  rw [factor,integral_const_mul]
  have hc:0≤charge:=zero_le_one.trans (le_max_left _ _)
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson d.below))
  exact ⟨receipt.1.const_mul _,(mul_le_mul_of_nonneg_left receipt.2 (pow_nonneg hc _)).trans
    (settle e p q hc hC gp hp (normal d o orders ranks)
      (WilsonMatrixTicketLanesRegisteredLoss.cutoff R d.below n))⟩

end YM.Integration.WilsonInvariantActionFineReserve
