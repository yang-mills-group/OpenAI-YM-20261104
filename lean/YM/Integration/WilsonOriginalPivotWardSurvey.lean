import YM.Integration.WilsonOriginalPivotWardRun

/-! Use the appointed finite survey's Wilson group stencil for the actual Ward spectator. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPivotWardSurvey

open Lattice RG Wilson Source Labels PowerSeries PertExtension PertExtension.Orb XSpace
open FormalOPE.RG10 FormalOPE.RG10.InversionTop FormalOPE.RG10.InversionWard
open XSpace.Rose XSpace.Cirrus
open FVA2 PhysicalNext.Repeat.Legato SlotEvaluation
open WilsonOriginalPivotWardEuler (direction)
open WilsonOriginalPivotWardTree (heard)
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (W:Initialize G) (Y:Sample 2) (d : ℕ)
    (i : (R.family.labels.level d).Index) (b : Edge (Site Y.F.p.side)) (x : Site Y.F.p.side)

/-- One group section represents the appointed independent survey on all real group fields. -/
def sectionAt := ((W.surveys d).prepares (R.family.labels.level d)).choose

theorem issued : (W.surveys d).Represents (R.family.labels.level d) (sectionAt R W d) :=
  ((W.surveys d).prepares (R.family.labels.level d)).choose_spec

theorem sampled :
    Bare.scalar (G:=G) (W.tree Y.F.p) (X^((R.family.labels.level d).grades i).2) *
      Bare.raw (W.tree Y.F.p) (W.surveys d) x ((R.family.labels.level d).basis i).val =
    BareOrb.stencil (W.tree Y.F.p) (fieldAt (sectionAt R W d) i x) := by
  let F := R.family.labels.level d
  let T := W.tree Y.F.p
  have raw := Bare.raw_calculation T (W.surveys d) x F _ (issued R W d)
    (F.grades i).1 (F.grades i).2 (F.pure i)
  rw [F.coords_basis] at raw
  have real (v) : (sectionAt R W d).places (Pi.single i 1) x (T.links v) =
      Complex.ofRealCLM (fieldAt (sectionAt R W d) i x (T.links v)) :=
    (scalar_real (issued R W d).1).symm
  simp_rw [real] at raw
  simpa [Bare.scalar, BareOrb.stencil, TreeFormal.enter, Function.comp_def, F, T] using raw

theorem basis (clear : off b ((sectionAt R W d).footprint x)) :
    Bare.normalized (W.tree Y.F.p) G (WilsonOriginalPivotWardRun.adjustment W Y b *
      Bare.raw (W.tree Y.F.p) (W.surveys d) x ((R.family.labels.level d).basis i).val) = 0 := by
  let T := W.tree Y.F.p
  let E := WilsonOriginalPivotWardRun.adjustment W Y b
  let S := sectionAt R W d
  let f := fieldAt S i x
  let n := ((R.family.labels.level d).grades i).2
  have scope : LocalOn (S.footprint x) f := fun U V shift =>
    congrArg Complex.re (S.placed_local x (Pi.single i 1) U V shift)
  have proxy : Proxy f := (field_proxy _ S (Pi.single i 1) x).after Complex.reCLM Complex.reCLM.contDiff
  have dir := (WilsonOriginalPivotWardEuler.issued (G:=G) b).1
  have test : PreTest f := (pre_field S (issued R W d).1 (issued R W d).2.1 i x).1
  have free : heard T (coupled b (direction b) f) = 0 := by
    have eq : heard T (coupled b (direction b) f) = replyCoeff (coupled b (direction b) f) :=
      BareOrb.diagram_eq T (dir.contact proxy test.gauge)
    rw [eq,isolated b scope clear (direction b),reply_nil (G:=G) (even_iff_two_dvd.mpr Y.F.p.even)]
  have zero : Bare.normalized T G (E * BareOrb.stencil T f) = 0 := by
    have value := WilsonOriginalPivotWardTree.contact T dir proxy test.gauge
    rw [free,mul_zero] at value
    unfold E WilsonOriginalPivotWardRun.adjustment
    rw [sub_mul,mul_assoc,map_sub,Bare.normalized_scalar,←WilsonOriginalPivotWardProduct.product T dir.effort test,
      ←WilsonOriginalPivotWardProduct.product T dir.fallout test]
    exact value
  let A := Bare.raw T (W.surveys d) x ((R.family.labels.level d).basis i).val
  have cleared : X^n * Bare.normalized T G (E * A) = 0 := by
    rw [← Bare.normalized_scalar, ← mul_left_comm E, sampled R W Y d i x, zero]
  exact (mul_eq_zero.mp cleared).resolve_left (pow_ne_zero _ PowerSeries.X_ne_zero)

end YM.Integration.WilsonOriginalPivotWardSurvey
