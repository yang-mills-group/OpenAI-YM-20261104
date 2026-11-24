import YM.Integration.WilsonSeparatedOriginalSlabWatchPosterior
import YM.Integration.WilsonSeparatedOriginalSlabWatchDirect

/-! Subtracting the same field's earlier registered coefficient cancels its original held angular germ through the reporting horizon. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchProjection
open Function MeasureTheory Lattice Wilson RG Source Labels Analysis Next.Foundations Next.UVStress Push.Local Bid
open ProjectorNext.Equivariance Trace.Physical Trace.Physical.GermGraph RG16 RG16.Literal
open PhysicalNext.Repeat.Legato RGComparison.Core16 OPE PhysMS Spec FilteredWilsonProduct
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Extra.Histories.Relay PhysicalNext
open WilsonSeparatedOriginalSlabWatchSignedDebit WilsonSeparatedOriginalSlabWatchPosterior WilsonMacroscopicRichFlatPosteriorLaw
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}(R:Run G){N p u h:ℕ}
local notation "C"=>R.family

theorem filed (T:Slices (C).path.levels p)(live:u<N)(door:Opened C h u p)(Y:Cut C N p)
    (ct:Continuous Y)(gi:GaugeInvariant Y)(paid:Booked C N p h Y u live.le)(t:Probe G h):
    let z:=label («C»:=R.family) (D:=h) (w:=(N,p)) R.makes door live.le Y
    hearing R T live.le Y z t=0:=by
  let z:=label («C»:=R.family) (D:=h) (w:=(N,p)) R.makes door live.le Y
  let O:=(C).O N p z 0
  obtain ⟨sold,entries⟩:=WilsonSeparatedOriginalSlabWatchSignedDebit.subtract R door live.le Y ct z paid
  have zero:topReport C N p h R.makes u door live.le (Y-O)=0:=by
    rw [entries];change topReport C N p h _ _ _ _ Y-((C).factory h N p).terminal.symm (((C).factory h N p).terminal (topReport C N p h _ _ _ _ Y))=0
    simp
  have same:GaugeInvariant (Y-O):=fun τ U=>congrArg₂ (·-·) (gi τ U) ((C).invariant R.makes N p h z 0 τ U)
  have measured:=WilsonMacroscopicRichMeasuredProbe.measured R T live h (Y-O) (ct.sub ((C).continuousO ..)) same door sold t
  change runProbe ((C).labels.level h) t (fitting h N p u R.makes door live.le (topReport C N p h R.makes u door live.le (Y-O)))=hearing R T live.le Y z t at measured
  rw [zero] at measured
  let F:=fitting h N p u R.makes door live.le
  let L:=runProbe ((C).labels.level h) t
  exact measured.symm.trans ((congrArg L F.map_zero).trans L.map_zero)

theorem zeroth (live:u<N)(Y:Cut C N p)(trial:(C).label h)(t:Probe G h)(zero:t.2.val=0):
    measureJet R live Y trial t=((C).S.a u:ℂ)^h*∫W,(Y W-(C).O N p trial 0 W) ∂law R N p live 1:=by
  have flat:(C).params.testLinks h (0:Site ((C).side u p)) (((C).path.rep N p u).p.threshold • t.1) 0=1:=by
    funext e;simp only [Hol.testLinks,(C).params.flat];rfl
  simp only [measureJet,Germ.jet,zero,iteratedDeriv_zero,Function.comp_apply,flat]

theorem held (T:Slices (C).path.levels p)(live:u<N)(door:Opened C h u p)(Y:Cut C N p)
    (ct:Continuous Y)(gi:GaugeInvariant Y)(paid:Booked C N p h Y u live.le):
    let z:=label («C»:=R.family) (D:=h) (w:=(N,p)) R.makes door live.le Y
    ∫W,(Y W-(C).O N p z 0 W) ∂law R N p live 1=0:=by
  let z:=label («C»:=R.family) (D:=h) (w:=(N,p)) R.makes door live.le Y
  let t:Probe G h:=⟨0,0⟩
  have diff:=filed R T live door Y ct gi paid t
  change hearing R T live.le Y z t=0 at diff
  rw [WilsonSeparatedOriginalSlabWatchPosterior.original R T live Y ct z t,zeroth R live Y z t rfl] at diff
  exact (mul_eq_zero.mp diff).resolve_left (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr ((C).S.a_pos u).ne'))

end YM.Integration.WilsonSeparatedOriginalSlabWatchProjection
