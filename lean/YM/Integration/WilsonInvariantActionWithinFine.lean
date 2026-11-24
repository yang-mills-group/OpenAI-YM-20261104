import YM.Integration.WilsonInvariantActionFineFinance
import YM.Integration.WilsonInvariantActionConditionalRegistered
import YM.Integration.WilsonRegisteredAxialCovariance

/-! The genuine within-step connected error against an earlier regulator field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionWithinFine
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

open ActualOriginalQCharges ActualOriginalQPackets ActualOriginalQReaders

open MS.Local.Physical Finset
open WilsonMatrixOriginalIndependentFields WilsonMatrixOriginalCurvatureStock WilsonMatrixOriginalCurvatureField
open WilsonMatrixTicketLanesReportedPivot WilsonReportingPrescribedOldWardWallet


open WilsonInvariantActionCurvatureFrame WilsonMatrixOriginalIndependentColumns WilsonMatrixTicketLanesNativePrices



open WilsonInvariantActionFineCurvature Push.SectorMeasure
variable {G:Gauge} {B:Deck G} (R:Run G) (simple:G.Simple) (Q:MS.Land.Prescription B)
local notation "slots" => B.BIndex (4:ℤ) 2
local notation "sources" => WilsonReportingPrescribedOldAction.label B
variable (J:Request (B.BIndex (4:ℤ) 2)) (A:NumericSchedule R.family J) (μ:ℝ)
variable {f:Extraction.Order} {S:Table R.family.book} (Φ:Spec.Final R.family f S) (L:RG17.Layout Φ)
  (U:Ultrafilter (ℕ×ℕ)) (cut:(U:Filter (ℕ×ℕ)) ≤ L.lens)
local notation "demand" => LocalFormal.Datum R.family (Stock.census (B.BIndex (4:ℤ) 2))

private theorem distance {V:Type} [DecidableEq V] [Fintype V] (X Y:Marker.Poly (Stock.census V)):
    Poly.price (fun _:V=>1) (X-Y) ≤ Poly.price (fun _:V=>1) X+Poly.price (fun _:V=>1) Y:=by
  unfold Poly.price
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro s _
  simp only [Poly.toll,prod_const_one,one_mul]
  exact norm_sub_le _ _

theorem expense (d:LocalFormal.Datum R.family (Stock.census (B.BIndex (4:ℤ) 2)))
    (v:R.family.label 4) (o:Site (R.family.side (d.level+1) d.period)) (age:R.family.ref 4  ≤ d.level+1):
    Envelope (fun T=>R.family.O (d.level+1) d.period (center R (d.level+1) d.cutoff d.period v) o T-
      masked R simple J A Q μ d v o T):=by
  refine ⟨WilsonInvariantActionFineFinance.measurable R simple Q J A μ d v o age,?_⟩
  classical
  by_cases filled:Nonempty slots
  · letI:=filled
    let u:=WilsonReportingPrescribedOldAction.label B
    let i:=unitTest (B:=B) R J
    let z:=WilsonMatrixTicketLanesSelectedNormalization.stamp R μ d
    let P:=ActualOriginalQInitialInput.packets R simple u J A d Q (fun _=>o) z (fun _=>0)
    let g:=regulatorRun R.family d.cutoff d.period (d.level+1)
    let H:=ActualOriginalQInitialInput.normalizer R simple u J A d Q (fun _=>o) z (fun _=>0)
    let y:=stock B (amounts R B (d.level+1) d.period (center R (d.level+1) d.cutoff d.period v))
    let c:=(∑ l,‖normalization R (d.level+1)*y.2 l‖)*H
    have hh:0 ≤ H:=zero_le_one.trans (le_max_left _ _)
    have hc:0 ≤ c:=mul_nonneg (sum_nonneg fun _ _=>norm_nonneg _) hh
    have paid:=OriginalMarkedBirthStencil.paid R simple u J A d Q (fun _=>o) z (fun _=>0)
      OriginalMarkedBirthStencil.mesh g
    have bounded:∃b:ℝ,∀T,Poly.price (fun _:slots=>1) (deficit R simple J A Q μ d o T) ≤ b:=by
      let X:=WilsonInvariantActionFineSource.plain R simple u J A d Q (fun _=>o) z (fun _=>0) i
      let Y:=WilsonInvariantActionFineSource.held R simple u J A d Q (fun _=>o) z (fun _=>0) i
      refine ⟨_,fun T=>(distance (X T) (Y T)).trans (add_le_add
        (ManuscriptQLocalOriginalFineMaskLoss.original_rows P paid i T).2
        (ManuscriptQLocalOriginalFineMaskLoss.regular_rows P paid i (R.family.path.rep d.cutoff d.period (d.level+1)).p T).2)⟩
    obtain ⟨b,hb⟩:=bounded
    exact ⟨c*b,fun T=>(gross R simple J A Q μ d v o age T).trans
      (mul_le_mul_of_nonneg_left (hb T) hc)⟩
  · letI:IsEmpty slots:=not_nonempty_iff.mp filled
    refine ⟨0,fun T=>?_⟩
    rw [difference R simple J A Q μ d v o age T]
    simp

private theorem subfield {Ω:Type*} [MeasurableSpace Ω] (a b:Ω→ℂ) (aM:Envelope a) (bM:Envelope b):
    Envelope (fun T=>a T-b T):=
  ⟨aM.meas.sub bM.meas,⟨_,fun T=>(norm_sub_le _ _).trans (add_le_add (aM.cost.choose_spec T)
    (bM.cost.choose_spec T))⟩⟩

private theorem comparison {m N per:ℕ} (live:m<N) (a t b:Config G (R.family.side (m+1) per)→ℂ)
    (ha:Envelope a) (ht:Envelope t) (hb:Envelope b) (V:Config G (R.family.side m per)):
    let read:=actualAverage R.family (N:=N) (E:=ℂ) (m:=m) (p:=per)
    read (fun T=>(b T-read b V)*(a T-t T)) V=
      WilsonInvariantActionConditionalMarginal.connected R (N:=N) a b V-
        WilsonInvariantActionConditionalMarginal.connected R (N:=N) t b V:=by
  intro read
  let ν:=ActualWilsonConditionalRoots.fibre R.family (N:=N) V
  letI:IsProbabilityMeasure ν:=ActualWilsonConditionalRoots.probability R.family R.makes live V
  dsimp only [read]
  rw [WilsonRegisteredConditionalCenter.covariance R.family R.makes live b (fun T=>a T-t T) hb (subfield a t ha ht) V]
  simp_rw [←ActualWilsonConditionalRoots.average R.family R.makes live V]
  change (∫T,b T*(a T-t T) ∂ν)-(∫T,b T ∂ν)*(∫T,a T-t T ∂ν)=
    ((∫T,a T*b T ∂ν)-(∫T,a T ∂ν)*(∫T,b T ∂ν))-((∫T,t T*b T ∂ν)-(∫T,t T ∂ν)*(∫T,b T ∂ν))
  have times(T:_):b T*(a T-t T)=a T*b T-t T*b T:=by ring
  simp_rw [times]
  rw [integral_sub ((ha.mulC hb).integrableC ν) ((ht.mulC hb).integrableC ν),
    integral_sub (ha.integrableC ν) (ht.integrableC ν)]
  ring

private theorem joint {m N per:ℕ} (live:m<N) (a t b:Config G (R.family.side (m+1) per)→ℂ)
    (ha:Envelope a) (ht:Envelope t) (hb:Envelope b):
    let ν:=scene R.family.path N per (m+1)
    let μ':=scene R.family.path N per m
    (∫V,‖WilsonInvariantActionConditionalMarginal.connected R (N:=N) a b V-
      WilsonInvariantActionConditionalMarginal.connected R (N:=N) t b V‖ ∂μ')  ≤ 
      Real.sqrt (∫T,‖b T‖^2 ∂ν)*Real.sqrt (∫T,‖a T-t T‖^2 ∂ν):=by
  intro ν μ'
  let D:=fun T=>a T-t T
  let B':=fun w:Config G (R.family.side m per)×Config G (R.family.side (m+1) per)=>
    b w.2-actualAverage R.family (N:=N) b w.1
  let π:=WilsonRegisteredJointAxial.law R.family N per m
  let read:=actualAverage R.family (N:=N) (E:=ℂ) (m:=m) (p:=per)
  letI:IsProbabilityMeasure ν:=probability R.makes.wilson live
  have ed:Envelope D:=subfield a t ha ht
  have d₂:MemLp D 2 ν:=MemLp.of_bound ed.meas.aestronglyMeasurable _ (ae_of_all _ ed.cost.choose_spec)
  have fine:=WilsonRegisteredJointAxial.fine R.family R.makes live (per:=per)
  have dπ:=d₂.comp_measurePreserving fine
  have income:=WilsonRegisteredConditionalCenter.income R.family R.makes live b hb
  have hB:MemLp B' 2 π:=income.1
  have integrable:Integrable (fun w=>B' w*D w.2) π:=hB.integrable_mul dπ
  have contraction:=WilsonRegisteredAxialConditional.conditional R.family R.makes live
    (fun w=>B' w*D w.2) integrable
  have coordinate(V:_):read (fun T=>B' (V,T)*D T) V=
    WilsonInvariantActionConditionalMarginal.connected R (N:=N) a b V-
      WilsonInvariantActionConditionalMarginal.connected R (N:=N) t b V:=
    comparison R live a t b ha ht hb V
  change (∫V,‖read (fun T=>B' (V,T)*D T) V‖ ∂μ') ≤ _ at contraction
  simp_rw [coordinate] at contraction
  refine contraction.trans ?_
  have two:ENNReal.ofReal (2:ℝ)=2:=by norm_num
  have eB:MemLp B' (ENNReal.ofReal (2:ℝ)) π:=two.symm ▸ hB
  have eD:MemLp (D ∘ Prod.snd) (ENNReal.ofReal (2:ℝ)) π:=two.symm ▸ dπ
  have cs:=integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two eB eD
  simp only [Real.rpow_two,←Real.sqrt_eq_rpow,Function.comp_apply] at cs
  simp only [norm_mul]
  refine cs.trans (mul_le_mul (Real.sqrt_le_sqrt income.2) ?_ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  apply Real.sqrt_le_sqrt
  change (∫w,‖D w.2‖^2 ∂π) ≤ ∫T,‖D T‖^2 ∂scene R.family.path N per (m+1)
  rw [←fine.map_eq,integral_map fine.measurable.aemeasurable (ed.meas.norm.pow_const 2).aestronglyMeasurable]

include cut in
theorem original (warm:Poetry R.family.path.levels) (e q:ℕ) {ε:ℝ} (hp:0<ε):
    ∀ᶠ m:ℕ in atTop,∀(d:LocalFormal.Datum R.family (Stock.census (B.BIndex (4:ℤ) 2))),d.level=m →
      ∀(v:R.family.label 4) (o:Site (R.family.side (d.level+1) d.period)) (M:ℝ), 0 ≤ M →
      R.family.ref 4 ≤ d.level+1 →
      (R.family.S.a (d.level+1)^4)⁻¹*Next.UVStress.quota R.family 4 (d.level+1) d.cutoff d.period v ≤ 
        R.family.path.levels.clock.hatBeta (d.level+1)^e*M →
      ∀(b:Config G (R.family.side (d.level+1) d.period)→ℂ), Envelope b →
      let ν:=scene R.family.path d.cutoff d.period (d.level+1)
      let g:=regulatorRun R.family d.cutoff d.period (d.level+1)
      let a:=R.family.O (d.level+1) d.period (center R (d.level+1) d.cutoff d.period v) o
      let t:=masked R simple J A Q μ d v o
      let conn:=WilsonInvariantActionConditionalMarginal.connected R (N:=d.cutoff) (m:=d.level) (p:=d.period)
      (∫V,‖conn a b V-conn t b V‖ ∂scene R.family.path d.cutoff d.period d.level) ≤ 
        Real.sqrt (∫T,‖b T‖^2 ∂ν)*(ε*g^q*M):=by
  have paid:=WilsonInvariantActionFineFinance.original R simple Q J A μ Φ L U cut warm e 1 q hp
  filter_upwards [paid] with m invoice
  intro d md v o M hM age bill b hb ν g a t conn
  have price:=invoice d md v o M hM age bill
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson d.below))
  have scale:0 ≤ ε*g^q*M:=mul_nonneg (mul_nonneg hp.le (pow_nonneg gp.le _)) hM
  have ha:Envelope a:=Env.compact (R.family.continuousO (d.level+1) d.period 4 _ o)
  have eD:=expense R simple Q J A μ d v o age
  have rt:t=fun T=>a T-(a T-t T):=funext fun _=>(sub_sub_cancel _ _).symm
  have ht:Envelope t:=rt ▸ subfield a (fun T=>a T-t T) ha eD
  have pay:Real.sqrt (∫T,‖a T-t T‖^2 ∂ν) ≤ ε*g^q*M:=by
    have sq:(∫T,‖a T-t T‖^2 ∂ν) ≤ (ε*g^q*M)^2:=price.2
    exact (Real.sqrt_le_sqrt sq).trans_eq (Real.sqrt_sq scale)
  exact (joint R d.below a t b ha ht hb).trans
    (mul_le_mul_of_nonneg_left pay (Real.sqrt_nonneg _))

end YM.Integration.WilsonInvariantActionWithinFine
