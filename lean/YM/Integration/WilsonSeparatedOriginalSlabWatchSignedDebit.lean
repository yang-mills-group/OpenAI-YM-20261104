import YM.Integration.WilsonSeparatedOriginalSlabWatchFiling
import YM.Integration.WilsonMacroscopicRichChildRegistration

/-! The earlier probe invoice is the actual Wilson conditional of the whole signed microscopic difference. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchSignedDebit
open Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Analysis Next.Foundations Next.UVStress Push.Local Bid
open ProjectorNext.Equivariance Trace.Physical Trace.Physical.GermGraph RG16 RG16.Literal Extraction Spec Cells RG17
open PhysicalNext.Repeat.Legato RGComparison.Core16 OPE OPE.Orbits PhysMS FilteredWilsonProduct
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Extra.Histories.Relay PhysicalNext
open WilsonMacroscopicRichCapturedProbes WilsonMacroscopicRichCapturePropagation
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}(R:Run G){b N p u h:ℕ}
set_option quotPrecheck false
local notation "C"=>R.family

theorem subtract (door:Opened C h u p)(live:u≤N)(Y:Cut C N p)(ct:Continuous Y)(trial:(C).label h)
    (paid:Booked C N p h Y u live):
    let P:=(C).O N p trial 0
    Booked C N p h (Y-P) u live ∧ topReport C N p h R.makes u door live (Y-P)=
      topReport C N p h R.makes u door live Y-((C).factory h N p).terminal.symm trial:=by
  intro P;let A:Fin 2→Cut C N p:=![Y,P];let a:Fin 2→ℂ:=![1,-1]
  obtain ⟨book,read⟩:=WilsonMacroscopicRichChildRegistration.issued C R.makes trial door live
  have continuous:∀i,Continuous (A i):=by intro i;fin_cases i;exact ct;exact (C).continuousO ..
  have ready:∀i,Booked C N p h (A i) u live:=by intro i;fin_cases i;exact paid;exact book
  have cash:=IntrinsicProductLinearity.booked_sum C N p h u R.makes door live a A continuous ready
  have same:(∑i,a i • A i)=Y-P:=by simp [Fin.sum_univ_two,a,A,sub_eq_add_neg]
  rw [same] at cash;refine ⟨cash.1,?_⟩;rw [cash.2];simp [Fin.sum_univ_two,a,A,P,read,sub_eq_add_neg]

def hearing (T:Slices (C).path.levels p)(live:u≤N)(Y:Cut C N p)(trial:(C).label h)(t:Probe G h):ℂ:=
  Germ.jet (C).params t ((C).path.rep N p u).p.threshold 0 (WilsonMacroscopicRichReportedPosterior.observation R T live h (Y-(C).O N p trial 0))

theorem signed (T:Slices (C).path.levels p)(door:Opened C h u p)(ub:u≤b)(bN:b<N)(Y:Cut C N p)
    (ct:Continuous Y)(gi:GaugeInvariant Y)(paid:Booked C N p h Y u (ub.trans bN.le))
    (Z:Cut C b p)(entries:credit C N p h Y b bN.le=Z)(trial:(C).label h)(t:Probe G h):
    runProbe ((C).labels.level h) t (forecast R door (ub.trans bN.le) trial)-
      Germ.jet (C).params t ((C).path.rep N p u).p.threshold 0 (returned R (N:=N) ub h Z)=
      -hearing R T (ub.trans bN.le) Y trial t:=by
  let O:=(C).O N p trial 0
  obtain ⟨bs,diff⟩:=subtract R door (ub.trans bN.le) Y ct trial paid
  have obs:=WilsonMacroscopicRichMeasuredProbe.measured R T (ub.trans_lt bN) h Y ct gi door paid t
  have neg:GaugeInvariant (Y-O):=fun τ U=>congrArg₂ (·-·) (gi τ U) ((C).invariant R.makes N p h trial 0 τ U)
  have ob:=WilsonMacroscopicRichMeasuredProbe.measured R T (ub.trans_lt bN) h (Y-O) (ct.sub ((C).continuousO ..)) neg door bs t
  change runProbe ((C).labels.level h) t (fitting h N p u R.makes door (ub.trans bN.le) (topReport C N p h R.makes u door (ub.trans bN.le) (Y-O)))=hearing R T (ub.trans bN.le) Y trial t at ob
  rw [show topReport C N p h R.makes u door (ub.trans bN.le) (Y-O)=_ from diff] at ob
  let F:=fitting h N p u R.makes door (ub.trans bN.le)
  let L:=runProbe ((C).labels.level h) t
  have linear (x y:(C).label h):L (F (x-y))=L (F x)-L (F y):=(congrArg L (F.map_sub x y)).trans (L.map_sub _ _)
  have signs: L (F (topReport C N p h R.makes u door (ub.trans bN.le) Y))-L (F (((C).factory h N p).terminal.symm trial))=
      hearing R T (ub.trans bN.le) Y trial t:=(linear _ _).symm.trans ob
  rw [WilsonMacroscopicRichCapturePropagation.original R T ub bN.le h Y Z entries,←obs,←signs]
  change L (F (((C).factory h N p).terminal.symm trial))-_ = -(_-_);abel

theorem original (T:Slices (C).path.levels p)(door:Opened C h u p)(ub:u≤b)(bN:b<N)(Y:Cut C N p)
    (ct:Continuous Y)(gi:GaugeInvariant Y)(paid:Booked C N p h Y u (ub.trans bN.le))
    (Z:Cut C b p)(entries:credit C N p h Y b bN.le=Z)(trial:(C).label h)(P:Finset (Probe G h)):
    WilsonMacroscopicRichIndependentHearing.debit R P door ub (ub.trans bN.le) trial Z=
      ∑t∈P,‖hearing R T (ub.trans bN.le) Y trial t‖:=by
  unfold WilsonMacroscopicRichIndependentHearing.debit;apply Finset.sum_congr rfl;intro t _
  rw [signed R T door ub bN Y ct gi paid Z entries trial t,norm_neg]

end YM.Integration.WilsonSeparatedOriginalSlabWatchSignedDebit
