import YM.Integration.WilsonSeparatedOriginalSlabWatchSignedDebit
import YM.Integration.WilsonSeparatedOriginalSlabWatchDebit

/-! The original filed label and every macroscopic detector are tested by one signed microscopic residual against an arbitrary trial. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchDirect
open Function Filter Set Lattice Wilson RG Source Labels Analysis Next.Foundations Next.UVStress Push.Local Bid
open ProjectorNext.Equivariance Trace.Physical Trace.Physical.GermGraph RG16 RG16.Literal
open PhysicalNext.Repeat.Legato RGComparison.Core16 OPE PhysMS Spec FilteredWilsonProduct
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open Extra.Histories.Relay PhysicalNext WilsonSeparatedOriginalSlabWatchTransfer WilsonSeparatedOriginalSlabWatchSignedDebit
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}

theorem original (F:Final R.family f S)(h:ℕ):
    ∃P:Finset (Probe G h),∀u:ℕ,∀doors:∀p,Opened R.family h u p,∃L:ℝ,0≤L ∧
    ∀W:Watch R.family,∃K:ℝ,0<K ∧ ∀ᶠt:ℕ×ℕ in f.fuse,
    ∀(b u₀:ℕ)(bN:b<t.1)(_:u₀≤u)(ub:u≤b)(T:Slices R.family.path.levels t.2)(η bound:ℝ)
      (Y:C(Config G (R.family.side t.1 t.2),ℂ)),GaugeInvariant Y → WilsonSeparatedOriginalSlabFiledFilm.Filing R Y u₀ h bN η bound →
    ∀trial:R.family.label h,let live:=ub.trans bN.le
      let z:=label (C:=R.family) (D:=h) (w:=t) R.makes (doors t.2) live Y
      let charge:=∑s∈P,‖hearing R T live Y trial s‖
      ‖trial-z‖≤L*charge ∧ ‖contrast W t Y z‖≤‖contrast W t Y trial‖+K*(L*charge):=by
  obtain ⟨P,paid⟩:=WilsonMacroscopicRichFiledProfile.original R h
  refine ⟨P,?_⟩;intro u doors;obtain ⟨L,Lp,entry⟩:=paid u doors;refine ⟨L,Lp,?_⟩
  intro W;obtain ⟨K,Kp,earns⟩:=WilsonSeparatedOriginalSlabWatchTransfer.cost F W h
  refine ⟨K,Kp,?_⟩;filter_upwards [earns] with t test b u₀ bN lo ub T η bound Y gi filed trial
  obtain ⟨fee,Q,z,fb,form,rem,size,cash,quota,previous,assay⟩:=entry b t.1 t.2 u₀ bN lo ub T η bound Y Y.continuous gi filed
  obtain ⟨_,_,_,_,_,program⟩:=filed
  have booked:=(program u lo ub (doors t.2)).1
  have bill:=assay trial
  rw [WilsonSeparatedOriginalSlabWatchSignedDebit.original R T (doors t.2) ub bN Y Y.continuous gi booked _ cash trial P] at bill
  exact ⟨bill,(test Y trial _).trans (add_le_add_right (mul_le_mul_of_nonneg_left bill Kp.le) _)⟩

end YM.Integration.WilsonSeparatedOriginalSlabWatchDirect
