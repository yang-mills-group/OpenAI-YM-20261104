import YM.Integration.WilsonMacroscopicRichCapturePropagation
import YM.Integration.WilsonMacroscopicRichFixedProbeTariff

/-! Compare any proposed physical label with the earlier Wilson report by finitely many measurements of the entire original captured numerator. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichCapturedProbes
open Filter Function Set Lattice Wilson RG Source Labels Analysis Next.Foundations Push.Local Bid
open ProjectorNext.Equivariance Trace.Physical Trace.Physical.GermGraph RG16 RG16.Literal
open PhysicalNext.Repeat.Legato RGComparison.Core16 OPE PhysMS Spec FilteredWilsonProduct
open WilsonMacroscopicRichCapturePropagation WilsonMacroscopicRichFixedProbeTariff
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}(R:Run G)(S:Table R.family.book)

def forecast {h N p u:ℕ}(door:Opened R.family h u p)(uN:u≤N)(z:R.family.label h):R.family.label h:=
  fitting h N p u R.makes door uN ((R.family.factory h N p).terminal.symm z)

theorem measured (h:ℕ):
    ∃P:Finset (Probe G h),∀u:ℕ,∀doors:∀p,Opened R.family h u p,∃L:ℝ,0≤L ∧
    ∀ (N p b:ℕ)(_:Slices R.family.path.levels p)(ub:u≤b)(bN:b≤N)(uN:u<N)
      (Y:Cut R.family N p)(Z:Config G (R.family.side b p)→ℂ),
    Continuous Y → GaugeInvariant Y → Booked R.family N p h Y u uN.le →
    credit R.family N p h Y b bN=Z →
    ∀ (z:R.family.label h)(c:ℝ),0≤c →
      (∀t∈P,‖runProbe (R.family.labels.level h) t (forecast R (doors p) uN.le z)-
        Germ.jet R.family.params t (R.family.path.rep N p u).p.threshold 0 (returned R (N:=N) ub h Z)‖≤c) →
      ‖S.project h z-S.project h (label (w:=(N,p)) R.makes (doors p) uN.le Y)‖≤L*c:=by
  obtain ⟨P,sale⟩:=WilsonMacroscopicRichFixedProbeTariff.purchased R.makes S h
  refine ⟨P,?_⟩
  intro u doors
  obtain ⟨L,nn,tariff⟩:=sale u doors
  refine ⟨L,nn,?_⟩
  intro N p b T ub bN uN Y Z ct gi booked credit z c cc test
  let M:=topReport R.family N p h R.makes u (doors p) uN.le Y
  let A:=fitting h N p u R.makes (doors p) uN.le
  have good:=WilsonMacroscopicRichMeasuredProbe.measured R T uN h Y ct gi (doors p) booked
  have account:=WilsonMacroscopicRichCapturePropagation.original R T ub bN h Y Z credit
  have aligned (t:Probe G h):runProbe (R.family.labels.level h) t (A M)=
      Germ.jet R.family.params t (R.family.path.rep N p u).p.threshold 0 (returned R (N:=N) ub h Z):=
    (good t).trans (congrArg (Germ.jet R.family.params t (R.family.path.rep N p u).p.threshold 0) account.symm)
  have priced (t:Probe G h)(ht:t∈P):‖runProbe (R.family.labels.level h) t (forecast R (doors p) uN.le z)-
      runProbe (R.family.labels.level h) t (A M)‖≤c:=
    (congrArg (fun e:ℂ=>‖runProbe (R.family.labels.level h) t (forecast R (doors p) uN.le z)-e‖) (aligned t)).le.trans (test t ht)
  have price:‖issued R.makes S (doors p) uN.le (forecast R (doors p) uN.le z)-
      issued R.makes S (doors p) uN.le (A M)‖≤L*c:=tariff N p uN.le _ _ c cc priced
  have left:issued R.makes S (doors p) uN.le (forecast R (doors p) uN.le z)=S.project h z:=by
    change S.project h ((R.family.factory h N p).terminal (A.symm (A ((R.family.factory h N p).terminal.symm z))))=_
    rw [A.symm_apply_apply,LinearEquiv.apply_symm_apply]
  have right:issued R.makes S (doors p) uN.le (A M)=S.project h (label (w:=(N,p)) R.makes (doors p) uN.le Y):=by
    change S.project h ((R.family.factory h N p).terminal (A.symm (A M)))=_
    rw [A.symm_apply_apply]
    rfl
  rwa [left,right] at price

end YM.Integration.WilsonMacroscopicRichCapturedProbes
