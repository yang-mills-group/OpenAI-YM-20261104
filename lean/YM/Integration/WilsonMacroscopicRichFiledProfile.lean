import YM.Integration.WilsonMacroscopicRichRawHearing
import YM.Integration.WilsonSeparatedOriginalSlabFiledFilm

/-! Measure the exact gross-financed joint smooth source on a fixed lower date,
including its original paid hard and regular fields and the receipt's own terminal label. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichFiledProfile
open Function Filter Set Lattice Wilson RG Source Labels Analysis Next.Foundations Next.UVStress Push.Local Bid
open ProjectorNext.Equivariance Trace.Physical Trace.Physical.GermGraph RG16 RG16.Literal
open PhysicalNext.Repeat.Legato RGComparison.Core16 OPE PhysMS Spec FilteredWilsonProduct
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open Extra.Histories.Relay PhysicalNext
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}(R:Run G)
set_option quotPrecheck false


theorem original (h:ℕ):
    ∃P:Finset (Probe G h),∀u:ℕ,∀doors:∀per,Opened R.family h u per,∃L:ℝ,0≤L ∧
    ∀(b N per u₀:ℕ)(bN:b<N)(_:u₀≤u)(ub:u≤b)(_:Slices R.family.path.levels per)(η bound:ℝ)
      (Y:Cut R.family N per),Continuous Y → GaugeInvariant Y →
      WilsonSeparatedOriginalSlabFiledFilm.Filing R Y u₀ h bN η bound →
    ∃(fee:ℝ)(Q:Coefficient (R.family.labels.level h) (R.family.side b per))(z:R.family.label h),
      fee≤bound ∧ Q.Format 0 R.family.params (R.family.path.rep N per b) ∧ Q.remBound 0 (R.family.path.rep N per b) (kappa R.family.path b) fee ∧
      (R.family.labels.level h).coeffSize Q.x≤fee ∧
      credit R.family N per h Y b bN.le=Q.density 0 (R.family.localSection h) (R.family.path.rep N per b) ∧
      let E:=WilsonMacroscopicRichCaptureFilingBudget.capital R.family b fee η
      quota R.family h b N per z≤2*E ∧
      mCost R.family h N per u (topReport R.family N per h R.makes u (doors per) (ub.trans bN.le) Y-
        (R.family.factory h N per).terminal.symm z)≤E/gainChart R.family.path b u ∧
      ∀trial:R.family.label h,‖trial-(label (C:=R.family) (D:=h) (w:=(N,per)) R.makes (doors per)
        (ub.trans bN.le) Y:R.family.label h)‖≤L*WilsonMacroscopicRichIndependentHearing.debit R P (doors per)
          ub (ub.trans bN.le) trial (Q.density 0 (R.family.localSection h) (R.family.path.rep N per b)):=by
  obtain ⟨P,hears⟩:=WilsonMacroscopicRichRawHearing.measured R h
  refine ⟨P,?_⟩
  intro u doors
  obtain ⟨L,pos,price⟩:=hears u doors
  refine ⟨L,pos,?_⟩
  intro b N per u₀ bN ou ub T η bound Y ct gi filing
  obtain ⟨fee,fb,⟨Q,form,rem,amount,account⟩,z,deposited⟩:=filing
  obtain ⟨cap,all⟩:=deposited
  obtain ⟨book,step⟩:=all u ou ub (doors per)
  exact ⟨fee,Q,z,fb,form,rem,amount,account,cap,step,
    price N per b T ub bN.le (ub.trans_lt bN) Y _ ct gi book account⟩

end YM.Integration.WilsonMacroscopicRichFiledProfile
