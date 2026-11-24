import YM.Integration.WilsonOlderFreshSoftSocketStationFigureScale
import YM.Integration.WilsonOriginalPublicNodalCash
import YM.Integration.WilsonOriginalPublicFigureIncome

/-! The true angle and axis of the deposited Wilson panel finance its own entire marked register at the native coupling. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1800000
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketStationPanelCapital
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

open WilsonThermometerDeclaredSeeds (Choice entry)
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonOlderFreshSoftSocketMeasuredCash (packet seats ticket)
open WilsonOlderFreshSoftSocketFaces (raw fill)
open WilsonOlderFreshSoftSocketRestored (degree stopped coin)
open WilsonOlderFreshSoftSocketKinetic (kinetic)
open WilsonOlderFreshHybridClock (flat)
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonReportingAbsoluteInletForecastBooks (value)
open WilsonOriginalStarSceneWords (pole)
open WilsonReceivedFixedDigitHistory WilsonCoeffUV.Winding ActualRunPhysicalPages Pert.Asymptotics
open scoped Classical BigOperators

open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext
open WilsonOriginalPublicFigureIncome (height)
open WilsonReceivedChronologicalHeldEntrance (coords)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open ActualRunPhysicalPages
variable {G:Gauge}(R:Run G)
local notation "Hm" j:max => R.family.path.levels.clock.hatBeta j
local notation "skin" N:max per:max K:max => (R.family.path.rep N per K).p.threshold

theorem chart {N per K:ℕ}(live:K≤N):(skin N per K)⁻¹≤Hm K:=by
  let H:=Hm K
  have high:1≤H:=(R.family.path.levels.fits.delayed K).le
  have sp:=Real.sqrt_pos.mpr (zero_lt_one.trans_le high)
  have lower:(Real.sqrt H)⁻¹ ≤ (skin N per K):=by
    have same:(R.family.path.rep N per K).p=R.alloy.B.a.budget K:=(R.makes.wilson.represents N per K live).vac
    rw [same]
    exact le_mul_of_one_le_right (inv_nonneg.mpr sp.le) (Real.one_le_exp (sq_nonneg _))
  calc
    _≤((Real.sqrt H)⁻¹)⁻¹:=inv_anti₀ (inv_pos.mpr sp) lower
    _=Real.sqrt H:=inv_inv _
    _≤_:=Real.sqrt_le_iff.mpr ⟨zero_le_one.trans high,by nlinarith only [sq_nonneg (H-1),high]⟩

variable {I:Type}[Fintype I][LinearOrder I](d:I→ℕ)
local notation "F" i:max => R.family.labels.level (d i)
omit [Fintype I] [LinearOrder I] in
theorem deposited {N per K:ℕ}(live:K≤N)(z:∀i,R.family.label (d i))(i:I):
    let g:=regulatorRun R.family N per K
    let x:=fun a=>WilsonPositionProgramReportedField.entire R (d a) K (N,per) (z a)
    (∑b:(F i).Index,‖WilsonOriginalPublicTrialFigure.amount R d g x i b‖)≤(F i).coeffSize (z i)*(Hm K)^height R (d i):=by
  intro g x
  let τ:=skin N per K
  have t0:0<τ:=(R.family.path.rep N per K).p.threshold_pos
  have large:1≤Hm K:=(R.family.path.levels.fits.delayed K).le
  change _≤(∑b:(F i).Index,‖z i b‖)*_
  rw [sum_mul]
  apply sum_le_sum
  intro b _
  let l:=((F i).grades b).2
  let a:=WilsonOriginalPublicTrialFigure.amount R d g x i b
  have hit:a*(τ:ℂ)^l=z i b:=WilsonOriginalPublicNodalCash.return_at R d live z i b
  have same:‖a‖*τ^l=‖z i b‖:=by
    have h:=congrArg norm hit
    simpa only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos t0] using h
  have divided:‖a‖=‖z i b‖*(τ⁻¹)^l:=by
    rw [inv_pow,←div_eq_mul_inv]
    exact (eq_div_iff (pow_ne_zero _ t0.ne')).mpr same
  rw [divided]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (pow_le_pow_left₀ (inv_nonneg.mpr t0.le) (chart R live) _).trans
    (pow_le_pow_right₀ large (le_sup (f:=fun j:(F i).Index=>((F i).grades j).2) (mem_univ b)))

variable (gr:Fin 3→ℕ){f n N per req pow step:ℕ}{B:ℝ}(cut:f+n≤N)
    (P:WilsonMeasuredPublicEntrancePanel.Panel R gr N per f (f+n) (Nat.le_add_right f n) cut req pow step B)
local notation "paid" i:max => ((((R.family.S.a (f+n)):ℂ)^(gr i))⁻¹ • coords R gr cut P i)
theorem owned (i:Fin 3):(R.family.labels.level (gr i)).coeffSize (paid i)≤B*(Hm (f+n))^pow:=by
  let F₀:=R.family.labels.level (gr i)
  let c:=(((R.family.S.a (f+n)):ℂ)^(gr i))⁻¹
  let w:=(P.axis i).symm (fitted R (gr i) (P.slot i) N per (P.names i))
  have src:F₀.coeffSize (c • w)≤P.tuition*(Hm (f+n))^pow:=(P.fixed i).2.1
  have moved:F₀.coeffSize (c • Motion.patch F₀ (P.turn i) w)≤Motion.orbitCost F₀*F₀.coeffSize (c • w):=by
    rw [Size.smul,Size.smul,mul_left_comm]
    exact mul_le_mul_of_nonneg_left (Motion.patch_cost F₀ (P.turn i) w) (norm_nonneg _)
  calc
    _≤_:=moved
    _≤Motion.orbitCost F₀*(P.tuition*(Hm (f+n))^pow):=mul_le_mul_of_nonneg_left src (zero_le_one.trans (Motion.orbitCost_one_le _))
    _=(Motion.orbitCost F₀*P.tuition)*(Hm (f+n))^pow:=(mul_assoc ..).symm
    _≤_:=mul_le_mul_of_nonneg_right (P.priced i) (pow_nonneg (zero_le_one.trans (R.family.path.levels.fits.delayed _).le) _)

theorem roster (s:Finset (Fin 3)):
    let d:=fun i:s=>gr i
    let g:=regulatorRun R.family N per (f+n)
    let x:=fun i:s=>WilsonPositionProgramReportedField.entire R (gr i) (f+n) (N,per) (paid i)
    (∑b:(∀i:s,(R.family.labels.level (d i)).Index),‖WilsonOriginalPublicTrialFigure.weight R d g x b‖)≤
      ∏i:s,B*(Hm (f+n))^(pow+height R (gr i)):=by
  intro d g x
  simp only [WilsonOriginalPublicTrialFigure.weight,norm_prod]
  rw [←Fintype.prod_sum (fun i (b:(R.family.labels.level (d i)).Index)=>‖WilsonOriginalPublicTrialFigure.amount R d g x i b‖)]
  apply prod_le_prod (fun _ _=>sum_nonneg (fun _ _=>norm_nonneg _))
  intro i _
  have avail:=deposited R d (per:=per) cut (fun i:s=>paid i) i
  refine avail.trans ?_
  rw [pow_add,←mul_assoc]
  exact mul_le_mul_of_nonneg_right (owned R gr cut P i) (pow_nonneg (zero_le_one.trans (R.family.path.levels.fits.delayed _).le) _)

end YM.Integration.WilsonOlderFreshSoftSocketStationPanelCapital
end
