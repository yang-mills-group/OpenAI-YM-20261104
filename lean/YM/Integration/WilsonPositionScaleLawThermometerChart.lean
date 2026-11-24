import YM.Integration.WilsonPositionScaleLawBooked
import YM.FVA2.Scale.Select

/-! The far physical kinetic thermometer is computed from one chosen near home,
its calibrated finite purse and seven ordinary literal Maxwell marginals. The
independently normalized formal thermometer is the original finite scale flow. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawThermometerChart
open Function Filter Set Finset PowerSeries Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Rose PhysicalNext.Repeat.Legato
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawWindow (RangeSpec Ratio sweep)
open WilsonPositionScaleLawHome (positioned)
open WilsonPositionScaleLawCompactJacobian (fieldsAt)
open WilsonPositionScaleLawNative (exactOp)
open WilsonPositionScaleLawIndependent (ψ)
open WilsonPositionScaleLawKinetic (kinetic)
open WilsonPositionThermometerReading (leg)
open scoped Topology Classical BigOperators
variable [W:RangeSpec]{G:Gauge}(Z:WilsonPrescription G){R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
set_option quotPrecheck false
local notation "E"=>(Bel R.family.book).Field

def reconstruction (d:ℕ)(z:ℝ×Ratio):E d→L[ℂ]E d:=
  let D:=Z.store.survey d
  WilsonPhysicalPositionBornCandidates.operator R.family (D.route (Z.store.prepared d) (D.purse (fieldsAt F J Z.store d z)))

def marginal (z:ℝ×Ratio)(x:Points 3)(s:Badge):ℂ:=
  WilsonPositionScaleLawHome.value F J Z.store (fun i=>reconstruction Z F J 6 z (leg R.family s i)) z.1 z.2.val x

theorem reconstructed (lead:Leading F J)(d:ℕ)(raw:WilsonPositionScaleLawCompactBranch.Raw J d):∀ᶠz in sweep,
    reconstruction Z F J d z=WilsonPositionScaleLawCompactNative.exactOp F J Z.store d z:=by
  filter_upwards [WilsonPositionScaleLawCompactNative.realizes F J Z.store lead d,WilsonPositionScaleLawCompactJacobian.recovered F J Z.store lead d raw] with z realized fit
  exact (congrArg (WilsonPhysicalPositionBornCandidates.operator R.family) fit.symm).trans realized

theorem seated (lead:Leading F J)(raw:WilsonPositionScaleLawCompactBranch.Raw J 6):∀ᶠz in sweep,∀x:Points 3,∀s:Badge,
    marginal Z F J z x s=WilsonPositionThermometerReading.sample F (positioned F J Z.store) (z.2.val*z.1) x s:=by
  let T:=positioned F J Z.store
  filter_upwards [reconstructed Z F J lead 6 raw] with z root x s
  dsimp only [marginal,WilsonPositionScaleLawHome.value,WilsonPositionThermometerReading.sample,PhysMS.measured]
  rw [root,smul_smul,mul_comm z.1 z.2.val]
  apply congrArg (S.classMoment (spectator F none) _ _)
  funext i
  exact Frame.cocycle_value 6 T (leg R.family s i) z.2.val z.1 (WilsonPositionScaleLawCompactNative.positive z.2)

theorem reading (lead:Leading F J)(raw:WilsonPositionScaleLawCompactBranch.Raw J 6):∀ᶠz in sweep,
    kinetic Z F J (z.2.val*z.1)=((Rose.test Z.criterion).applyTo (fun x=>WilsonPositionThermometerConnected.value (marginal Z F J z x))).re/
      Rose.cT Z.criterion.cut G Z.criterion.image:=by
  filter_upwards [seated Z F J lead raw] with z eq
  have change: (fun x=>WilsonPositionThermometerConnected.value (marginal Z F J z x))=
      (fun x=>WilsonPositionThermometerConnected.value (WilsonPositionThermometerReading.sample F (positioned F J Z.store) (z.2.val*z.1) x)):=by
    funext x;exact congrArg WilsonPositionThermometerConnected.value (funext (eq x))
  rw [change];rfl

variable {hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)

def response (s:ℝ):FVA2.Scale.Way G 6:=Facets.couple (ψ Z M ν s) (Measure.start Z.scheme Z.criterion 6)

include H in
omit W in
theorem formal (s:ℝ):Select.meter Z.criterion (response Z M ν s)=ψ Z M ν s:=by
  let data:=H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  have rooted:=((H.details.normative ν).first.led s).start
  have thin:Jury.Thin (Measure.start Z.scheme Z.criterion 6):=(Jury.enrolled ν M Z.scheme Z.criterion σ hG data.Taylor data.still data.base).light
  rw [response,Select.media _ _ _ rooted thin,Select.overcome Z.scheme Z.criterion ν M σ hG data.Taylor data.still data.base,
    PowerSeries.subst_X (Reg.Choice.licence _ rooted)]

include H in
omit W in
theorem coefficient (s:ℝ)(k:ℕ):
    (Rose.test Z.criterion).applyTo (fun x=>coeff (k+1) (Select.Single (response Z M ν s) x))=
      (Rose.cT Z.criterion.cut G Z.criterion.image:ℂ)*coeff (k+1) (ψ Z M ν s):=by
  let c:ℂ:=Rose.cT Z.criterion.cut G Z.criterion.image
  have live:c≠0:=Complex.ofReal_ne_zero.mpr Z.criterion.fresh.ne
  have h:=congrArg (coeff (k+1)) (formal Z M H ν s)
  change coeff (k+1) (c⁻¹ • (Select.output Z.criterion (response Z M ν s)-PowerSeries.C (coeff 0 (Select.output Z.criterion (response Z M ν s)))))=_ at h
  simp only [map_smul,map_sub,coeff_C_of_ne_zero (Nat.succ_ne_zero k),sub_zero,smul_eq_mul,Select.output,coeff_mk] at h
  change _=c*_
  rw [←h,←mul_assoc,mul_inv_cancel₀ live,one_mul]

end YM.Integration.WilsonPositionScaleLawThermometerChart
end
