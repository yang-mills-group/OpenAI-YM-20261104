import YM.Integration.WilsonOriginalPublicTrialPhaseCross
import YM.Integration.WilsonReflectedPublicGuardedMotion
import YM.Integration.WilsonMeasuredPublicEntranceCellWords

/-! The two halves of a reflected fitted product, measured before the turn
and at the actual cutoff, with the same engineering scalar on both sides. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseMotion
open Finset Function MeasureTheory Lattice Wilson RG Source Labels Cells Extra.Histories Motion
open Planned.GuardedAtom MergeProof Push Local PhysicalNext.Repeat.Legato ProjectorNext.Equivariance
open WilsonPositionProgramBlockedTrialAddBack WilsonMovingForkMixedSeed
open WilsonMeasuredPublicEntranceCellWords
open WilsonMovingForkHeterogeneousCut (Filed)
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G){N per K f:ℕ}
local notation "C" => R.family
local notation "P" => (C).path.rep N per K

theorem rotated (d:ℕ)(w:(C).label d)(σ:Signed)(x y:Site ((C).side K per))(U:Config G ((C).side K per)):
    uncut R d N per K (affine σ y x) (((C).labels.level d).act σ.ortho w) U=
      uncut R d N per K x w (pull σ y U):=by
  unfold uncut names
  rw [act_at_zero,←core_act,((C).labels.level d).scaling]
  rw [((C).localSection d).placed_signed (R.makes.sections d)]

theorem barred (d:ℕ)(w:(C).label d)(x:Site ((C).side K per))(U:Config G ((C).side K per)):
    uncut R d N per K x (star w) U=star (uncut R d N per K x w U):=by
  unfold uncut names
  rw [Pi.star_apply,star_add,core_star,scaled_star]
  exact congrArg (fun z:ℂ=>star (w 0)+z) ((R.makes.sections d).ordinary_real ..)

theorem square (d:ℕ)(w:(C).label d)(σ:Signed)(x y:Site ((C).side K per))(U:Config G ((C).side K per)):
    let a:=(((C).S.a K:ℂ)^d)⁻¹
    uncut R d N per K (affine σ y x) (a • Motion.patch ((C).labels.level d) (σ,true) w) U=
      star (uncut R d N per K x (a • w) (pull σ y U)):=by
  intro a
  have scalar:Motion.scalar (σ,true) a=a:=by simp [a,Motion.scalar]
  rw [←scalar,←Motion.patch_smul,scalar]
  change uncut R d N per K _ (star (((C).labels.level d).act σ.ortho (a • w))) U=_
  rw [barred,rotated]

theorem plain (d:ℕ)(w:(C).label d):Motion.patch ((C).labels.level d) (1,false) w=w:=by
  simp [Motion.patch,show (1:Signed).ortho=1 from map_one Signed.inclusionO,Frame.act_one]

end YM.Integration.WilsonOriginalPublicTrialPhaseMotion
