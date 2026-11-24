import YM.Integration.WilsonReportingGuardedSource

/-! Full signed prescribed source, including its rough part, inside the earlier Wilson measure. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingMeasuredWardIntake
open Lattice Wilson RG Source Labels MS.Local.Physical MS.Theater MS.Land
open PhysicalNext.Repeat.Legato Trace.Physical Trace.Physical.GermGraph
open WilsonReportingPrescribedOldFreeArms WilsonReportingMeasuredWardFees
open WilsonReportingPrescribedOldWardWallet
open WilsonReportingMeasuredWardSource WilsonReportingMeasuredWardSourceGerm
open private born from YM.Integration.WilsonReportingMeasuredWardSourceGerm
open scoped BigOperators Classical

variable {G:Gauge} {B:Deck G} {R:Run G} {T:Campaign R} (W:Campaign.Pillars R T)
    (Q:Prescription B) {m N per:ℕ}
local notation "F" => R.family.labels.level 4
local notation "S" => R.family.localSection 4
local notation "P" => R.family.path.rep N per m

def seed (m per:ℕ) (z:Stock B) (clock:ℝ) (k:ℕ):R.family.label 4 :=
  (R.family.factory 4 m per).terminal.symm (submitted R Q m per z clock k)

def charged (life:m ≤ N) (o:Site (R.family.side m per))
    (z:Stock B) (clock:ℝ) (k:ℕ):Coefficient F (R.family.side m per):=
  WilsonReportingGuardedSource.field W life o 4 (seed (R:=R) Q m per z clock k)

theorem density (simple:G.Simple) (age:R.family.ref 4 ≤ m) (life:m ≤ N)
    (z:Stock B) (clock:ℝ) (k:ℕ) (o:Site (R.family.side m per)) (U:Config G (R.family.side m per)):
    (charged W Q life o z clock k).density o S P U=
      (R.family.S.a m:ℂ)^4*((P).eval U:ℂ)*operand R Q z clock k _ o U := by
  let v:=seed (R:=R) Q m per z clock k
  have law:=WilsonReportingGuardedSource.purchased W life age o 4 v
  have ht:(P).p.threshold=R.family.path.levels.clock.threshold m:=
    congrArg BudgetPoint.threshold (R.makes.wilson.represents N per m life).vac
  have q:=WilsonReportingMeasuredWardSource.original R Q simple m per age z clock k o U
  change (((R.family.S.a m:ℂ)^4)⁻¹)*(S).places ((F).scaled (R.family.path.levels.clock.threshold m)⁻¹ v) o U=_ at q
  change (WilsonReportingGuardedSource.field W life o 4 v).density o S P U=_
  rw [law.2.2.2.2 U,ht,←q]
  field_simp [(R.family.S.a_pos m).ne']

theorem entered (age:R.family.ref 4 ≤ m) (life:m ≤ N) (z:Stock B) (clock:ℝ) (k:ℕ):
    let q:=charged W Q (per:=per) life 0 z clock k
    let x:=seed (R:=R) Q m per z clock k
    reads (C:=R.family) 4 N per m q ((F).coeffSize ((F).core x)) ∧
      page (C:=R.family) 4 per m q=((R.family.S.a m:ℂ)^4) • bank R Q m z clock k := by
  intro q x
  have raw:=WilsonReportingGuardedSource.purchased W life age (0:Site (R.family.side m per)) 4 x
  refine ⟨⟨raw.1,raw.2.1⟩,?_⟩
  have paid:=R.makes.calibrated 4 m per age
  calc
    page (C:=R.family) 4 per m q=page (C:=R.family) 4 per m ((R.family.factory 4 m per).entries m x):=by
      unfold Trace.Physical.GermGraph.page Germ.projection
      rw [show q.x=x from raw.2.2.1,show q.regular=0 from raw.2.2.2.1,
        show ((R.family.factory 4 m per).entries m x).x=x from paid.bare_coord x,
        show ((R.family.factory 4 m per).entries m x).regular=0 from paid.bare_germ x]
    _=x:=born R m per age x
    _=_:=frame R Q m per age z clock k

end YM.Integration.WilsonReportingMeasuredWardIntake
