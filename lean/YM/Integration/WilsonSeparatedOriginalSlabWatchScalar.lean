import YM.Integration.WilsonSeparatedOriginalSlabWatchProjection
import YM.RG05Readout.Suede.Silver

/-! Horizon zero reads the complete physical conditional at the identity and puts that scalar back on the same unshifted experimental detector. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchScalar
open Function Set MeasureTheory Lattice Wilson RG Source Labels Analysis Next.Foundations Next.UVStress Push.Local Bid
open ProjectorNext.Equivariance Trace.Physical Trace.Physical.GermGraph RG16 RG16.Literal
open RG05Readout Address Native Many Pulse Flatten PhysicalNext.Repeat.Legato RGComparison.Core16 OPE PhysMS Spec FilteredWilsonProduct
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Extra.Histories.Relay PhysicalNext
open WilsonMacroscopicRichFlatPosteriorLaw WilsonMacroscopicRichWatchLaw WilsonMacroscopicRichWatchLabels
open WilsonSeparatedOriginalSlabWatchProjection WilsonSeparatedOriginalSlabWatchTransfer
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}(R:Run G){N p u:ℕ}
local notation "C"=>R.family

private theorem cylinder (start:(C).ref 0≤N)(y:(C).label 0)(W:Config G ((C).side N p)):
    (C).O N p y 0 W=y 0:=by
  let a:=Address.chunk («C»:=R.family) Suede.pip y
  have line:=congrArg (fun b:Palette R.family 0=>b Suede.pip) (Suede.letter_sum a)
  change val a (Suede.mother R.family) • Suede.firstC R.family Suede.pip=a Suede.pip at line
  simp only [Suede.first_chunk,a,Address.val,Suede.mother,chunk_self] at line
  have one:=(C).constant R.makes 0 start (0:Site ((C).side N p))
  simp only [Family.refUnit,Source.unitVec,pow_zero,one_smul] at one
  let e:=((C).labels.level 0).e0
  have h:y=y 0 • e:=line.symm
  calc
    _=(C).O N p (y 0 • e) 0 W:=congrArg (fun v:(C).label 0=>(C).O N p v 0 W) h
    _=y 0*((C).O N p e 0 W):=congrFun (((C).linearO N p 0 0).map_smul (y 0) e) W
    _=y 0:=by rw [(show (C).O N p e 0 W=1 from congrFun one W),mul_one]

theorem original (T:Slices (C).path.levels p)(live:u<N)(door:Opened C 0 u p)(Y:Cut C N p)
    (ct:Continuous Y)(gi:GaugeInvariant Y)(paid:Booked C N p 0 Y u live.le):
    let z:=label («C»:=R.family) (D:=0) (w:=(N,p)) R.makes door live.le Y
    z 0 = ∫W,Y W ∂law R N p live 1:=by
  let z:=label («C»:=R.family) (D:=0) (w:=(N,p)) R.makes door live.le Y
  let μ:=WilsonMacroscopicRichFlatPosteriorLaw.law R N p live 1
  letI:IsProbabilityMeasure μ:=WilsonMacroscopicRichFlatPosteriorLaw.prob R live le_rfl 1
  have held:=WilsonSeparatedOriginalSlabWatchProjection.held R T live door Y ct gi paid
  have point (W): (C).O N p z 0 W=z 0:=cylinder R (door.post.trans live.le) z W
  change ∫W,(Y W-(C).O N p z 0 W) ∂μ=0 at held
  simp_rw [point] at held
  rw [integral_sub (ct.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (integrable_const _)] at held
  have value:(∫W,Y W ∂μ)-z 0=0:=by simpa only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul] using held
  exact (sub_eq_zero.mp value).symm

theorem detector (T:Slices (C).path.levels p)(live:u<N)(door:Opened C 0 u p)(Y:C(Config G ((C).side N p),ℂ))
    (gi:GaugeInvariant Y)(paid:Booked C N p 0 Y u live.le)(W:Watch C):
    let z:=label («C»:=R.family) (D:=0) (w:=(N,p)) R.makes door live.le Y
    contrast W (N,p) Y z=Wilson.moment ((C).beta N p) (fun U=>Y U*W.plot N p U)-
      (∫V,Y V ∂law R N p live 1)*Wilson.moment ((C).beta N p) (W.plot N p):=by
  let z:=label («C»:=R.family) (D:=0) (w:=(N,p)) R.makes door live.le Y
  have raw:=original R T live door Y Y.continuous gi paid
  change z 0=_ at raw
  have constant:source C 0 N p z = z 0 • (1:C(Config G ((C).side N p),ℂ)):=by
    ext U;change (C).O N p z 0 U=z 0*1;rw [cylinder R (door.post.trans live.le),mul_one]
  change meter C W (Y-source C 0 N p z)=_
  rw [constant,map_sub,map_smul,raw,WilsonMacroscopicRichWatchLaw.same,WilsonMacroscopicRichWatchLaw.same]
  simp only [ContinuousMap.one_apply,one_mul,smul_eq_mul]

end YM.Integration.WilsonSeparatedOriginalSlabWatchScalar
