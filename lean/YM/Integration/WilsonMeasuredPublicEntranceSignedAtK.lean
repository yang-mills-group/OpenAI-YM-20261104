import YM.Integration.WilsonMeasuredPublicEntranceUnmasked
import YM.Integration.WilsonAddressedFiniteGuardTrial
/-! The paid original sources define a signed entrance at K under the same earlier Wilson law. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceSignedAtK
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

theorem original (label:∀a,(C).label (d a))(o:V → Site ((C).side N per))(dose:V → ℂ)
    (s:(Stock.census V).Mode)(W:Config G ((C).side u per)):
    let raw:=fun U=>∏a∈s.val,dose a*(C).O N per (label a) (o a) U
    let trial:=printed R d (N:=N) sites v z fired s
    let enter:=fun U=>actualTransport (C) (N:=N) raw kn U-trial U
    actualTransport (C) (N:=N) enter uk W=actualTransport (C) (N:=N) raw (uk.trans kn) W-
      actualTransport (C) (N:=N) trial uk W:=by
  intro raw trial enter
  have capital:=WilsonMeasuredPublicEntranceUnmasked.salary R d (N:=N) sites v z s.val
  have repaired:submitted R d v z fired=(fun a=>z a • v a):=by
    funext a
    simp [submitted,WilsonOriginalAlternativeFiniteSource.fired]
  have entire:WilsonOriginalMicroscopicEntranceDeposits.funded trial:=by
    change WilsonOriginalMicroscopicEntranceDeposits.funded (printed R d (N:=N) sites v z fired s)
    rw [(WilsonAddressedFiniteGuardTrial.original R d kn sites v z fired s).1,repaired]
    exact capital.2
  obtain ⟨bound,cash⟩:=entire.2
  have weighted:=weighted_integrable R kn (show BoundedAt (C) trial from ⟨entire.1.aestronglyMeasurable,bound,cash⟩)
  have physical:WilsonOriginalMicroscopicEntranceDeposits.funded raw:=by
    apply WilsonSeparatedPrefixCohortUnscale.salary s.val (fun a U=>dose a*(C).O N per (label a) (o a) U)
    intro a
    have smooth:Continuous (fun U=>dose a*(C).O N per (label a) (o a) U):=
      continuous_const.mul ((C).continuousO N per (d a) (label a) (o a))
    obtain ⟨B,used⟩:=(isCompact_range smooth.norm).bddAbove
    exact ⟨smooth.measurable,B,fun U=>used ⟨U,rfl⟩⟩
  exact WilsonMeasuredPublicEntranceHeldDifference.withdraw R (le_refl N) kn uk raw trial physical weighted W

end YM.Integration.WilsonMeasuredPublicEntranceSignedAtK
end
