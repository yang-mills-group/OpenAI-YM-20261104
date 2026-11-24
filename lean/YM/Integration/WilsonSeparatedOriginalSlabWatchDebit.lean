import YM.Integration.WilsonSeparatedOriginalSlabWatchTransfer
import YM.Integration.WilsonMacroscopicRichFiledProfile

/-! Testing the actual earlier filing of a whole Wilson observable against any submitted label on the same macroscopic detector. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchDebit
open Function Filter Set Lattice Wilson RG Source Labels Analysis Next.Foundations Next.UVStress Push.Local Bid
open ProjectorNext.Equivariance Trace.Physical Trace.Physical.GermGraph RG16 RG16.Literal
open PhysicalNext.Repeat.Legato RGComparison.Core16 OPE PhysMS Spec FilteredWilsonProduct
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open Extra.Histories.Relay PhysicalNext WilsonSeparatedOriginalSlabWatchTransfer
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}

theorem original (F:Final R.family f S)(W:Watch R.family)(h:ℕ):
    ∃P:Finset (Probe G h),∀u:ℕ,∀doors:∀p,Opened R.family h u p,∃L:ℝ,0≤L ∧ ∀ᶠt:ℕ×ℕ in f.fuse,
    ∀(b u₀:ℕ)(bN:b<t.1)(_:u₀≤u)(ub:u≤b)(_:Slices R.family.path.levels t.2)(η bound:ℝ)
      (Y:C(Config G (R.family.side t.1 t.2),ℂ)),GaugeInvariant Y →
      WilsonSeparatedOriginalSlabFiledFilm.Filing R Y u₀ h bN η bound →
    ∃(fee:ℝ)(Q:Coefficient (R.family.labels.level h) (R.family.side b t.2)),fee≤bound ∧
      Q.Format 0 R.family.params (R.family.path.rep t.1 t.2 b) ∧
      Q.remBound 0 (R.family.path.rep t.1 t.2 b) (kappa R.family.path b) fee ∧
      credit R.family t.1 t.2 h Y b bN.le=Q.density 0 (R.family.localSection h) (R.family.path.rep t.1 t.2 b) ∧
      ∀trial:R.family.label h,let live:=ub.trans bN.le
      ‖contrast W t Y (label (C:=R.family) (D:=h) (w:=t) R.makes (doors t.2) live Y)‖≤
        ‖contrast W t Y trial‖+L*WilsonMacroscopicRichIndependentHearing.debit R P (doors t.2) ub live trial
          (Q.density 0 (R.family.localSection h) (R.family.path.rep t.1 t.2 b)):=by
  obtain ⟨P,paid⟩:=WilsonMacroscopicRichFiledProfile.original R h
  obtain ⟨K,Kp,earns⟩:=WilsonSeparatedOriginalSlabWatchTransfer.cost F W h
  refine ⟨P,?_⟩;intro u doors;obtain ⟨J,Jp,filed⟩:=paid u doors
  refine ⟨K*J,mul_nonneg Kp.le Jp,?_⟩
  filter_upwards [earns] with t hear b u₀ bN start ub slices η bound Y good captured
  obtain ⟨fee,Q,z,bill,form,rem,_,cash,_,_,test⟩:=filed b t.1 t.2 u₀ bN start ub slices η bound Y Y.continuous good captured
  refine ⟨fee,Q,bill,form,rem,cash,?_⟩;intro trial;dsimp only
  exact (hear Y trial _).trans (by rw [mul_assoc];gcongr;exact test trial)

end YM.Integration.WilsonSeparatedOriginalSlabWatchDebit
