import YM.Integration.WilsonOriginalForestSplit
import YM.Integration.WilsonVacuumPreResetDepositedIntegrand

/-! The entire signed original finite Gaussian on a deposited action and all incoming group-field marks. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalOccupiedForestIntegral
open Function Finset Marker Multi Comparison.RG02 Order Cumulants PowerSeries
open Lattice Wilson RG Precision Tree Matrix Exterior PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay
open WilsonVacuumPreResetDepositedGeometric WilsonVacuumPreResetDepositedLetters
open WilsonVacuumPreResetFiniteRegister
open scoped Classical BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

variable {G:Gauge}(R:Run G)(N m p:ℕ)(hm:m<N)(F:Forest (step R m p).ratio)
variable (tag:(step R m p).Choices)(Z:SeriesA G)
variable {T:Type}[DecidableEq T][Fintype T]{J:Census T}(Q:Bulk.Colors J G (fine R m p))
variable (cash:BudgetPoint)(cap:ℕ){σ C:ℝ}(width:0<σ)(draw:Draw Z σ C)
    (low:∀a∈Z,3≤a.grade)(high:∀a∈Z,a.grade≤cap)
    (x:fieldDir G (coarse R m p) 1)(r:ℕ)(z:Key F G→ℝ)


open WilsonVacuumPreResetDepositedIntegrand PhysicalForestMarkedRay Assembly
open FreeResolvent Next.SectorChange

def names : PTable J := PowerSeries.mk fun d => lit J (fun I =>
  readJet (Q.power I+d) (chartMark (step R m p) F (saddle R N m p F)
    (model R N m p hm) x z Q I))

def numerator : Grade J r :=
  register J r (OriginalRadialSeries.observed (profile R m p F x z)
    (raiseE (opened R N m p hm F Z))) * (series J r (names R N m p hm F Q x z)).pass

include tag hm in
private theorem center :
    saddle R N m p F = reveal G (step R m p) F *
      ((reveal G (step R m p) F).transpose * saddle R N m p F):=by
  have h:=(model R N m p hm).hessian_pos F tag
  rw [OriginalMarkedHeatCovariance.precision R N m p hm F tag] at h
  apply sweeps G (step R m p) F (prediction R N m p) (lower R N m)
    (isUnit_iff_ne_zero.mpr h.det_pos.ne')
  exact horizon_step (levels R) m N hm _ _ (step R m p).sizes

include cash width draw low high in
theorem integrand (well:Bulk.Well Q)(s:(Board J r).Mode):
    Cloud.paint z (Cloud.integrand (family R N m p hm F tag Z Q cap x r) s)=
      (numerator R N m p hm F Z Q x r z).part s :=by
  let W:=source R m p Z Q cap
  let K:=model R N m p hm
  let f:=family R N m p hm F tag Z Q cap x r
  let L:=lit (Board J r) (fun I=>Cloud.paint z (f I))
  have words:curve W.power (Bulk.markFn (step R m p) F W) (Bulk.translated K F x z)=
      names R N m p hm F Q x z :=by
    have checked:Bulk.Well W :=(QuadraticLocal.Fk.well _ _ (WilsonVacuumPreResetTorusDeposit.legal Z width draw low _) Q well).1
    apply PowerSeries.ext
    intro n
    rw [curve,coeff_mk,names,coeff_mk]
    apply congrArg (lit J)
    funext I
    exact PhysicalForestMarkedRay.coefficient _ F _ K x z tag W checked I (center R N m p hm F tag) _
  have quiet:bottom J r L.pass = register J r (OriginalRadialSeries.observed (profile R m p F x z)
      (raiseE (opened R N m p hm F Z))) :=by
    apply Join.both_parts
    intro t u
    rw [bottom_value,WilsonVacuumPreResetFiniteRegister.read]
    by_cases ht:t=J.quiet
    · subst t
      rw [if_pos rfl,if_pos rfl]
      change ((lit (Board J r) (fun I=>Cloud.paint z (f I))).pass).part (Join.pair J.quiet u)=_
      rw [← Cloud.before_log]
      exact WilsonVacuumPreResetDepositedIntegrand.original R N m p hm F tag Z Q cash cap width draw low high x r z well u
    · simp only [if_neg ht,mul_zero]
  have all:L.pass=bottom J r L.pass*(series J r
      (curve W.power (Bulk.markFn (step R m p) F W) (Bulk.translated K F x z))).pass :=
    WilsonOriginalForestSplit.exponential ..
  rw [quiet,words] at all
  rw [Cloud.before_log]
  exact congrArg (fun w:Grade J r=>w.part s) all

include cash width draw low high in
theorem integrated (well:Bulk.Well Q)(s:(Board J r).Mode):
    (Bulk.Fk (model R N m p hm) F tag (source R m p Z Q cap) x r).part s =
      ∫ y, (numerator R N m p hm F Z Q x r y).part s ∂Gaussian.cloud ((model R N m p hm).covariance F tag) :=by
  let K:=model R N m p hm
  let f:=family R N m p hm F tag Z Q cap x r
  have paid:=(Cloud.gaussian (K.covariance F tag) (K.symm F tag) ((K.positive F tag).posSemidef) 0 f s).2
  simp only [zero_add,Cloud.shift_zero] at paid
  exact paid.symm.trans (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y=>
    (Cloud.before_log f y s).symm.trans (integrand R N m p hm F tag Z Q cash cap width draw low high x r y well s))))

end YM.Integration.WilsonOriginalOccupiedForestIntegral
