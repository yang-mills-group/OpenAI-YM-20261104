import YM.Integration.WilsonCenteredCommonGerm
import YM.Integration.WilsonCapturedPrimarySection
import YM.RG16.Unmasked.Report

/-! Read a booked original cutoff observable through a different funded
presentation of the same Wilson density, at any finite engineering horizon. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredCanonicalFiling
open Function Lattice RG Wilson Labels Source Work.G08 Next.Foundations
open Trace.Physical Trace.Physical.GermGraph RG16 RG16.Literal RG12 Bid
open PhysicalNext.Repeat.Legato Push.Local
open scoped Classical

variable {G : Gauge} (R : Run G)
local notation "F" d:max => R.family.labels.level d
local notation "vac" N:max p:max i:max => R.family.path.rep N p i

theorem original {d N p i : ℕ} (Y : Cut R.family N p)
    (opened : Opened R.family d i p) (date : R.t d ≤ i) (live : i ≤ N)
    (book : Booked R.family N p d Y i live)
    {P : Rep G (R.family.side i p)} (aligned : P.p=(vac N p i).p)
    (quiet : ∀U,(vac N p i).eval U=P.eval U)
    (q : Coefficient (F d) (R.family.side i p)) (fmt : q.Format 0 R.family.params P)
    {κ t : ℝ} (paid : q.remBound 0 P κ t)
    (printed : ∀U,credit R.family N p d Y i live U=q.density 0 (R.family.localSection d) P U) :
    readPage R.family N p d Y i live=Germ.projection (F d) R.family.params P.p.threshold 0 q ∧
    topReport R.family N p d R.makes i opened live Y = (fitting d N p i R.makes opened live).symm
      (Germ.projection (F d) R.family.params P.p.threshold 0 q) :=by
  have originalPoint : (vac N p i).p=R.family.path.levels.budget i := (R.makes.wilson.represents N p i live).vac
  obtain ⟨price,registered,full⟩ := book.sheet
  let actual := sheet R.family N p d Y i live
  have reader := (WilsonCapturedPrimarySection.original R date (vac N p i) originalPoint).1
  have shared : Germ.projection (F d) R.family.params (vac N p i).p.threshold 0 actual =
      Germ.projection (F d) R.family.params P.p.threshold 0 q :=
    WilsonCenteredCommonGerm.original aligned.symm reader registered.1 fmt registered.2 paid quiet
      (fun U => (congrFun full U).symm.trans (printed U))
  have page : readPage R.family N p d Y i live=Germ.projection (F d) R.family.params P.p.threshold 0 q :=by
    change Germ.projection (F d) R.family.params (R.family.path.levels.budget i).threshold 0 actual=_
    exact (congrArg (fun a : BudgetPoint => Germ.projection (F d) R.family.params a.threshold 0 actual) originalPoint.symm).trans shared
  exact ⟨page,congrArg (fitting d N p i R.makes opened live).symm page⟩

end YM.Integration.WilsonCenteredCanonicalFiling
