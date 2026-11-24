import YM.Integration.WilsonPositionScaleLawJacobian
import YM.Integration.WilsonPositionScaleLawCompactBranch

/-! The actual solution, Jacobian, and inverse on general original positive compact ratio windows. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawCompactJacobian
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS Maxwell Maxwell.Free
open XSpace XSpace.Normalize
open WilsonPositionScaleLawWindow (RangeSpec Ratio sweep)
open WilsonPositionScaleLawHome (bank)
open WilsonPositionScaleLawCompactNative WilsonPositionScaleLawCompactBranch
open WilsonPositionScaleLawJacobian (calibrated)
open WilsonPhysicalPositionBornCandidates (record faithful operator expansion)
open WilsonPhysicalPositionDiscreteBranches (field)
open scoped Topology Classical ContDiff
variable [Win:RangeSpec] {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (F:Final C f S)(J:ℝ→tower S)(V:Store G)
set_option quotPrecheck false
local notation "E" => (Bel C.book).Field

abbrev fieldsAt (d:ℕ)(z:ℝ×Ratio):Prediction G d:=bank F J V d z.1 z.2.val
abbrev chart (d:ℕ)(z:ℝ×Ratio):MoveSpace G d:=coordinates F J V d z

theorem approaches (lead:Leading F J)(d:ℕ)(raw:Raw J d):Tendsto (chart F J V d) sweep (𝓝 0):=by
  let X:=E d
  let I:=ContinuousLinearMap.id ℂ X
  letI : NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℂ (X→L[ℂ]X):=ContinuousLinearMap.toNormedSpace
  letI : NormedSpace ℝ (X→L[ℂ]X):=NormedSpace.restrictScalars ℝ ℂ _
  letI : FiniteDimensional ℝ (X→L[ℂ]X):=Module.Finite.trans ℂ (X→L[ℂ]X)
  let B:=record G C d
  obtain ⟨L,hL⟩:=LinearMap.exists_leftInverse_of_injective (K:=ℝ) B (LinearMap.ker_eq_bot.mpr (faithful C))
  have ha:Tendsto (fun z=>exactOp F J V d z-I) sweep (𝓝 0):=by
    have t:Tendsto (exactOp F J V d) sweep (𝓝 I):=transferred F J V lead d raw
    simpa only [sub_self] using t.sub_const I
  have hrecord:Tendsto (fun z=>B (chart F J V d z)) sweep (𝓝 0):=by
    apply ha.congr'
    filter_upwards [realizes F J V lead d] with z h
    rw [←h,expansion];abel
  have fin:= (L.continuous_of_finiteDimensional.tendsto (0:X→L[ℂ]X)).comp hrecord
  rw [map_zero] at fin
  exact fin.congr fun z=>DFunLike.congr_fun hL (chart F J V d z)

theorem recovered (lead:Leading F J)(d:ℕ)(raw:Raw J d):∀ᶠz in sweep,
    chart F J V d z=(V.survey d).route (V.prepared d) ((V.survey d).purse (fieldsAt F J V d z)):=by
  let D:=V.survey d
  let P:=fieldsAt F J V d
  let a:=chart F J V d
  have input:Tendsto (fun z=>(D.purse (P z),a z)) sweep (𝓝 D.opening):=
    (WilsonPositionScaleLawWindow.original F J V lead d).prodMk_nhds (approaches F J V lead d raw)
  filter_upwards [exactEquation F J V lead d,bothHomes.eventually
    (calibrated F J V lead d),input.eventually (D.pathway (V.prepared d))] with z hfar hit localEq
  have same:Fray.SetEq (V.measure d) ((guide G d).symm (a z)) (P z):=by
    change (V.measure d).D (recruit (field (a z)) (P z))=_
    rw [hfar]
    exact hit
  have hg:=(D.means _ _).mp same
  rw [(guide G d).apply_symm_apply] at hg
  exact (localEq.mp hg).symm

def derivative (d:ℕ)(z:ℝ×Ratio):MoveSpace G d→L[ℝ]MoveSpace G d:=
  (V.survey d).delta ((V.survey d).purse (fieldsAt F J V d z),chart F J V d z)

theorem original (lead:Leading F J)(d:ℕ)(raw:Raw J d):
    Tendsto (derivative F J V d) sweep (𝓝 1) ∧
    (∀ᶠ z in sweep,(derivative F J V d z).IsInvertible) ∧
    Tendsto (fun z=>(derivative F J V d z).inverse) sweep (𝓝 1):=by
  let D:=V.survey d
  let H:=V.prepared d
  have input:Tendsto (fun z=>(D.purse (fieldsAt F J V d z),chart F J V d z)) sweep (𝓝 D.opening):=
    (WilsonPositionScaleLawWindow.original F J V lead d).prodMk_nhds (approaches F J V lead d raw)
  have hj:= (D.continuous_steps.tendsto D.opening).comp input
  have inv:= ((D.pin_inv H).contDiffAt_map_inverse (n:=1)).continuousAt.tendsto.comp hj
  have at0:(D.delta D.opening).inverse=(1:MoveSpace G d→L[ℝ]MoveSpace G d):=by
    rw [D.unpin H];exact ContinuousLinearMap.inverse_equiv (.refl ℝ _)
  rw [at0] at inv
  rw [D.unpin H] at hj
  exact ⟨hj,input.eventually (D.unhit H),inv⟩

end YM.Integration.WilsonPositionScaleLawCompactJacobian
end
