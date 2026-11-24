import YM.Integration.WilsonSeparatedPrefixMovingHomeEars
import YM.Integration.WilsonSeparatedOriginalSlabHeldProxy
import YM.Integration.WilsonThermometerUnitFilingFlatTelescope

/-! Compare one genuine cutoff credit and one integrable mounted face at the
same original flat, with the physical capture date chosen independently. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixScreenedCredit
open Function Set Filter Finset MeasureTheory Lattice RG Wilson Source Labels
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato Trace Trace.Physical Trace.Physical.GermGraph
open RG16 RG16.Literal RG12 Bid Extra.Histories Extra.Histories.Relay MergeProof MergeProof.Accent
open WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFlatTelescope
open WilsonSeparatedPrefixMovingHomeEars (returned)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){N p K f b:ℕ}
local notation "C" => R.family
local notation "X" j:max => Config G ((C).side j p)
local notation "P" => (C).path.rep N p f

theorem original (live:f≤N)(top:K≤N)(bf:b≤f)(bk:b≤K)(Y:Cut (C) N p)(cont:Continuous Y)
    (B:X f → ℂ)(Z:ℝ)(bill:returned (R:=R) live bf Y B 1 Z):
    ‖reading R (N:=N) (credit (C) N p 0 Y K top) b bk-
      reading R (N:=N) (numerator R N p f B) b bf‖≤Z:=by
  let F:=actualTransport (C) (N:=N) Y live
  have change:numerator R N p f F=credit (C) N p 0 Y f live:=by
    funext U
    have pay:=WilsonSeparatedOriginalSlabHeldProxy.normalized R live Y U
    have positive:=Multi.AxisShift.chosen_positive R.makes.wilson live U
    have key:((P).eval U:ℂ)≠0:=Complex.ofReal_ne_zero.mpr positive.ne'
    change ((P).eval U:ℂ)*F U=_
    rw [mul_comm]
    exact ((div_eq_iff key).mp pay).symm
  have pooled:reading R (N:=N) (credit (C) N p 0 Y K top) b bk=
      reading R (N:=N) (numerator R N p f F) b bf:=by
    unfold reading
    rw [change,WilsonThermometerUnitFilingCoarse.cutoff R top bk Y cont,
      WilsonThermometerUnitFilingCoarse.cutoff R live bf Y cont]
  obtain ⟨paid,cap⟩:=bill
  have Bfin:Integrable (fun U=>(P).eval U • B U) (prior G _):=by
    simpa only [Complex.real_smul] using paid
  obtain ⟨capY,bnd⟩:=(isCompact_range cont.norm).bddAbove
  have Ffin:=actualTransport_weighted_integrable (C) R.makes (N:=N) (p:=p) (le_rfl:N≤N)
    cont.measurable.aestronglyMeasurable (fun U=>bnd ⟨U,rfl⟩) live
  have hear (g:X f → ℂ):reading R (N:=N) (numerator R N p f g) b bf=
      actualTransport (C) (N:=N) g bf 1:=WilsonThermometerUnitFilingPosterior.weighted R g bf
  rw [pooled,hear,hear]
  have separated:=congrFun (ActualWilsonAbsoluteTransport.sub (C) R.makes live Ffin Bfin bf) 1
  change actualTransport (C) (N:=N) (fun U=>F U-B U) bf 1=
    actualTransport (C) (N:=N) F bf 1-actualTransport (C) (N:=N) B bf 1 at separated
  rw [←separated];exact cap

end YM.Integration.WilsonSeparatedPrefixScreenedCredit
end
