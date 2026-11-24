import YM.Integration.WilsonOriginalMicroscopicEntranceHeldMasterRead
import YM.Integration.WilsonMeasuredPublicEntranceSignedAtK
/-! Each signed N-to-K entrance has a genuine integrable density on the one earlier Wilson prior. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceHeldPhaseIncome
open Function Finset Lattice Wilson RG Marker Labels Source QuadraticLocal
open MeasureTheory PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonMeasuredPublicEntranceOrder WilsonMeasuredPublicEntranceSignedEar
open WilsonAddressedFiniteGuardTrial (printed submitted)
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){V:Type}[Fintype V][DecidableEq V](d:V → ℕ)
  {N per K u:ℕ}(kn:K ≤ N)(uk:u ≤ K)(sites:V → Site (R.family.side K per))
  (v:∀a,R.family.label (d a))(z:V → ℂ)
local notation "C" => R.family
local notation "fired" => WilsonOriginalAlternativeFiniteSource.fired (V:=V)

theorem income (label:∀a,(C).label (d a))(o:V → Site ((C).side N per))(dose:V → ℂ)
    (s:(Stock.census V).Mode):
    let raw:=fun U=>∏a∈s.val,dose a*(C).O N per (label a) (o a) U
    let trial:=printed R d (N:=N) sites v z fired s
    Integrable (fun U=>((C).path.rep N per K).eval U •
      (actualTransport (C) (N:=N) raw kn U-trial U)) (prior G _):=by
  intro raw trial
  have capital:=WilsonMeasuredPublicEntranceUnmasked.salary R d (N:=N) sites v z s.val
  have repaired:submitted R d v z fired=(fun a=>z a • v a):=by
    funext a
    simp [submitted,WilsonOriginalAlternativeFiniteSource.fired]
  have entire:WilsonOriginalMicroscopicEntranceDeposits.funded trial:=by
    change WilsonOriginalMicroscopicEntranceDeposits.funded (printed R d (N:=N) sites v z fired s)
    rw [(WilsonAddressedFiniteGuardTrial.original R d kn sites v z fired s).1,repaired]
    exact capital.2
  obtain ⟨bound,cash⟩:=entire.2
  have physical:WilsonOriginalMicroscopicEntranceDeposits.funded raw:=by
    apply WilsonSeparatedPrefixCohortUnscale.salary s.val (fun a U=>dose a*(C).O N per (label a) (o a) U)
    intro a
    have smooth:Continuous (fun U=>dose a*(C).O N per (label a) (o a) U):=
      continuous_const.mul ((C).continuousO N per (d a) (label a) (o a))
    obtain ⟨B,used⟩:=(isCompact_range smooth.norm).bddAbove
    exact ⟨smooth.measurable,B,fun U=>used ⟨U,rfl⟩⟩
  have earlier:=actualTransport_weighted_integrable (C) R.makes (le_refl N)
    physical.1.aestronglyMeasurable physical.2.choose_spec kn
  have bought:Integrable (fun U=>((C).path.rep N per K).eval U • trial U) (prior G _):=by
    exact WilsonMeasuredPublicEntranceOrder.integrable (C) R.makes kn
      (show BoundedAt (C) trial from ⟨entire.1.aestronglyMeasurable,bound,cash⟩)
  simpa only [Pi.sub_def,smul_sub] using earlier.sub bought

open WilsonReflectedPublicCommonDose (dose)
open WilsonReflectedMixedThermalArms (rent)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonReflectedPublicCommonDose (dose)
open WilsonReflectedMixedThermalArms (rent)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonAddressedAlignedColumn WilsonReflectedPublicOrientedFaces
open WilsonThermometerReflectedTrajectory WilsonThermometerOwnOffsetRadii WilsonThermometerOwnOffsetTale
open WilsonReflectedFundedHearing WilsonReflectedPublicGuardedColumns
open Labels Source RG12 Extra.Histories Motion Bandage Trace.Physical.GermGraph
open WilsonMeasuredPublicEntranceSignedEar (weighted)
open WilsonMeasuredPublicEntrancePanel
open WilsonMeasuredPublicEntrancePrescribedCampus
variable {f requested power t:ℕ} {B:ℝ} {fk:f≤K}
variable (A:Panel R d N per f K fk kn requested power t B)
def entry (s:(Stock.census V).Mode)(U:Config G ((C).side K per)):ℂ:=
  actualTransport (C) (N:=N) (Raw R d A s) kn U-Guard R d A s U

theorem original (s:(Stock.census V).Mode):
    Integrable (fun U=>((C).path.rep N per K).eval U • entry R d kn A s U) (prior G _):=by
  exact income R d kn (fun a=>((C).S.toDepth fk per).embed (A.loc a))
    (fun a=>Motion.patch ((C).labels.level (d a)) (A.turn a)
      ((A.axis a).symm (fitted R (d a) (A.slot a) N per (A.names a))))
    (fun a=>(charged R d A a:ℂ)*(((C).S.a K:ℂ)^(d a))⁻¹)
    (fun a=>displayed R (d a) (A.names a) (A.turn a))
    (fun a=>WilsonThermometerReflectedTrajectory.anchorAt R (A.loc a) N)
    (fun a=>(charged R d A a:ℂ)) s

end YM.Integration.WilsonOriginalMicroscopicEntranceHeldPhaseIncome
end
