import YM.Integration.WilsonReflectedPublicOrientedFaces

/-! Literal reflected copies of one compensated source on its original
hierarchy. The entire forced profile is carried with the two smooth entries. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReflectedPublicDoseField
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Push.Local
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonThermometerOwnOffsetTale WilsonThermometerOwnOffsetNectar
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {N p k d:ℕ}
open WilsonThermometerReflectedTrajectory
open WilsonThermometerMarchSource
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext Work.G08 Next.Rank Extra.Multi Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetCylinder WilsonAddressedAlignedColumn

private theorem commute {n:Side}(a b:ℂ)(w:Three G n):a • (b • w)=b • (a • w):=by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext U
    change a*(b*w.1 U)=b*(a*w.1 U)
    ring
  · funext U
    change a*(b*w.2.1 U)=b*(a*w.2.1 U)
    ring
  · funext i U
    change a*(b*w.2.2 i U)=b*(a*w.2.2 i U)
    ring

theorem marked_real (z:Site (R.family.side N p))(s:Motion)(c:Site (R.family.side k p))
    (V:Sight R.family d p)(r:Emblems R.family d)(y:Palette R.family d)(t:ℝ)(j:ℕ):
    marked R z s c V r ((t:ℂ) • y) j=(t:ℂ) • marked R z s c V r y j:=by
  unfold marked
  split
  next h=>
    have linear: strand R V r h.1 ((t:ℂ) • y)=(t:ℂ) • strand R V r h.1 y:=by
      unfold strand
      rw [map_smul,map_smul]
      rfl
    let π:=Classical.choice ((R.makes.wilson.represents N p j h.2).good.labels.moves s.1 (point R z s c j))
    let a:=WilsonThermometerOwnOffsetNectar.factor R k j d
    change a • View.spin s π (strand R V r h.1 ((t:ℂ) • y))=(t:ℂ) • (a • View.spin s π (strand R V r h.1 y))
    rw [linear]
    exact (congrArg (fun Z=>a • Z) (View.spin_real (R:=R.family.path.rep N p j)
      (x:=point R z s c j) (P:=strand R V r h.1 y) s π (t:ℂ) (scalar_real s t))).trans (commute ..)
  next=>simp only [smul_zero]

variable {I:Type}(d:I→ℕ)(x:(i:I)→R.family.label (d i))(turn:I→Motion)
  (c:I→Site (R.family.side k p))(est:∀i,Opened R.family (d i) k p)(hk:k≤N)
  (V:(i:I)→Sight R.family (d i) p)(u:(i:I)→Emblems R.family (d i))
  (t:I→ℝ)
open WilsonAddressedAlignedColumn
local notation "base_" i:max => reduce (offer R (x i) (est i) hk)
theorem arm (raw:∀i,Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) k N p (d i)
      (digits R N p 0) (V i) (u i))(ref:∀i e,e≤d i→R.family.ref e≤N)(i:I):
    WilsonThermometerReflectedRoster.source R d (fun _=>0) turn c (fun j=>(t j:ℂ) • (base_ j)) u hk i=
      ((t i:ℂ)*((WilsonThermometerMarchSource.charge (offer R (x i) (est i) hk):ℝ):ℂ)⁻¹) •
        R.family.O N p (WilsonReflectedPublicOrientedFaces.displayed R (d i) (x i) (turn i)) (anchorAt R (c i) N):=by
  have original:=WilsonReflectedPublicOrientedFaces.arm R d x V u est hk raw ref turn c i
  rw [←smul_smul,←original]
  let α:=t i
  let D:=R.family.factory (d i) N p
  let val:= base_ i
  let y:=D.terminal (finer (u i) hk val (primaryLetter (d i)))
  have head:D.terminal (finer (u i) hk ((α:ℂ) • val) (primaryLetter (d i)))=(α:ℂ) • y:=by
    rw [map_smul,Pi.smul_apply]
    exact D.terminal.map_smul _ _
  let a:ℂ:=((R.family.S.a k:ℂ)^(d i))
  change stepUp (turn i) (anchorAt R (c i) N) (a • R.family.O N p
    (D.terminal (finer (u i) hk ((α:ℂ) • val) (primaryLetter (d i)))) 0)=
      (α:ℂ) • stepUp (turn i) (anchorAt R (c i) N) (a • R.family.O N p y 0)
  rw [head,(R.family.linearO N p (d i) 0).map_smul,smul_comm a (α:ℂ)]
  funext U
  change scalar (turn i) ((t i:ℂ)*_)=((t i:ℂ)*_)
  rw [scalar_mul,scalar_real]
  rfl

end YM.Integration.WilsonReflectedPublicDoseField
end
