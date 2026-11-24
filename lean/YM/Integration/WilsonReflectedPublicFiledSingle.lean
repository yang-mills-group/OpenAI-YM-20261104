import YM.Integration.WilsonReflectedPublicOpticalEstate
import YM.Integration.WilsonReflectedPublicSignedFare
/-! Identifying the authentic funded singleton within the entire deposited panel
with the same real conditional arm used by the fixed-cutoff replacement. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicFiledSingle
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) {N p k : ℕ} {I : Type} [Fintype I] [DecidableEq I]
local notation "C₀" => R.family

open WilsonReflectedPublicOrientedFaces WilsonReflectedOriginalTwoDeposit
open WilsonThermometerReflectedTrajectory
open OPE.Therm

theorem field (d:ℕ) (live:k≤N)(x:(C₀).label d)(m:Motion)(c:Site ((C₀).side k p))
    (ready:(C₀).ref d≤N):
    (C₀).O N p (displayed R d x m) (anchorAt R c N)=
      raw R (WilsonReflectedPlacedArm.original R d live x m.2 m.1 c) :=by
  let b:=anchorAt R c N
  have pin:b=((C₀).S.toDepth live p).embed c:=by simp [b,anchorAt,Mix.camp,live]
  funext W
  have place: (C₀).O N p (displayed R d x m) b W =
      (C₀).O N p (if m.2 then star x else x) 0 (pull m.1 b W) :=by
    simpa [displayed,affine] using
      (C₀).rotated R.makes ready (if m.2 then star x else x) m.1 0 b W
  refine place.trans ?_
  change _=Push.RelayDifference.hand m.2 ((C₀).O N p x 0 (pull m.1 (((C₀).S.toDepth live p).embed c) W))
  rw [←pin]
  cases ht:m.2 <;> simp only [Bool.false_eq_true,if_false,if_true,Push.RelayDifference.hand]
  exact (C₀).reality R.makes ready x 0 _

theorem original (d:I→ℕ) (x:(i:I)→(C₀).label (d i))
    (V:(i:I)→Sight C₀ (d i) p)(u:(i:I)→Emblems C₀ (d i))
    (est:∀i,Opened C₀ (d i) k p)(cut:k≤N)
    (paid:∀i,Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) k N p (d i)
      (digits R N p 0) (V i) (u i))(ref:∀i e,e≤d i→(C₀).ref e≤N)
    (turn:I→Motion)(c:I→Site ((C₀).side k p))(names:Census I)(t:ℕ):
    let y:=fun i=>offer R (x i) (est i) cut
    let data:=fun i=>reduce (y i)
    WilsonThermometerReflectedRoster.filed R d (fun _=>0) turn c data V u names cut t →
    ∀i W, (marked R (N:=N) 0 (turn i) (c i) (V i) (u i) (data i) k).1 W =
      ((charge (y i):ℝ):ℂ)⁻¹ * (((C₀).path.rep N p k).eval W:ℂ)*
        held R (WilsonReflectedPlacedArm.original R (d i) cut (x i) (turn i).2 (turn i).1 (c i)) k W :=by
  intro y data posted i W
  let col:=WilsonReflectedPlacedArm.original R (d i) cut (x i) (turn i).2 (turn i).1 (c i)
  let χ:=((charge (y i):ℝ):ℂ)⁻¹
  have trace:=WilsonReflectedPublicOrientedFaces.original R d x V u est cut paid ref turn c names t posted k cut (names.fire i) W
  have observed:=(posted k le_rfl cut).2.1 i
  have exactRead:=(WilsonThermometerReflectedTrajectory.live R (z:=0) (s:=turn i) (c:=c i)
       (V:=V i) (r:=u i) (y:=data i) (paid i) (le_refl k) cut).read
  have pay:(fun W'=>∏v∈(names.fire i).val,
      ((charge (y v):ℝ):ℂ)⁻¹*(C₀).O N p (displayed R (d v) (x v) (turn v)) (anchorAt R (c v) N) W') =
      χ • raw R col :=by
    funext W';simp only [Census.fire,Finset.prod_singleton]
    exact congrArg (χ*·) (congrFun (field R (d i) cut (x i) (turn i) (c i) (ref i _ le_rfl)) W')
  have full := (congrFun exactRead W).symm.trans ((congrFun observed W).symm.trans trace)
  refine full.trans ?_
  rw [pay,Complex.real_smul,WilsonReflectedPlacedArm.linear R (le_refl N) cut _ (Envelope.compactC (WilsonReflectedOriginalTwoDeposit.continuous R col))]
  change _=χ*_*held R col k W
  rw [WilsonReflectedOriginalTwoDeposit.held,dif_pos cut];ring

end YM.Integration.WilsonReflectedPublicFiledSingle
end
