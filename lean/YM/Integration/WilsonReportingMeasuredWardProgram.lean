import YM.Integration.WilsonReportingMeasuredWardInverse
import YM.Integration.WilsonReportingMeasuredWardFunding

/-! A single earlier Wilson source for the entire finite MS prescription at each order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingMeasuredWardProgram
open Finset Lattice Wilson RG Source Labels MS.Local.Physical MS.Theater MS.Land
open PhysicalNext.Repeat.Legato Trace.Physical Trace.Physical.GermGraph
open WilsonReportingPrescribedOldFreeArms WilsonReportingPrescribedOldWardTree
open WilsonReportingMeasuredWardFees WilsonReportingMeasuredWardSource WilsonReportingMeasuredWardSourceGerm
open WilsonReportingMeasuredWardIntake WilsonReportingMeasuredWardInverse
open private born from YM.Integration.WilsonReportingMeasuredWardSourceGerm
open scoped Classical BigOperators

variable {G:Gauge} {R:Run G} {B:Deck G} {T:Campaign R} (W:Campaign.Pillars R T) (Q:Prescription B)
local notation "I" => B.BIndex (4:ℤ) 2
local notation "F" => R.family.labels.level 4
local notation "S" => R.family.localSection 4

def table (m per:ℕ) (clock:ℝ) (v:ℕ→I→ℂ) (k:ℕ):R.family.label 4:=
  ∑i:Fin (k+1),seed (R:=R) Q m per (0,submit Q clock v i.val) clock (k-i.val)

def joined {m N per:ℕ} (life:m ≤ N) (o:Site (R.family.side m per)) (clock:ℝ) (v:ℕ→I→ℂ) (k:ℕ):=
  WilsonReportingGuardedSource.field W life o 4 (table (R:=R) Q m per clock v k)

theorem raw (m per:ℕ) (age:R.family.ref 4 ≤ m) (clock:ℝ) (v:ℕ→I→ℂ) (k:ℕ):
    table (R:=R) Q m per clock v k=((R.family.S.a m:ℂ)^4) •
      (intercept Q R clock v k • (F).e0+((R.family.path.levels.clock.threshold m^2:ℝ):ℂ) • coordinates R (0,v k)):=by
  unfold table
  simp only [seed,frame R Q m per age,←Finset.smul_sum]
  exact congrArg (fun y:R.family.label 4=>(R.family.S.a m:ℂ)^4 • y)
    (rolled Q R ((R.family.path.levels.clock.threshold m^2:ℝ):ℂ) clock v k)

theorem entered {m N per:ℕ} (age:R.family.ref 4 ≤ m) (life:m ≤ N) (clock:ℝ) (v:ℕ→I→ℂ) (k:ℕ):
    let q:=joined W Q (per:=per) life 0 clock v k
    let x:=table (R:=R) Q m per clock v k
    reads (C:=R.family) 4 N per m q ((F).coeffSize ((F).core x)) ∧
      Trace.Physical.GermGraph.page (C:=R.family) 4 per m q=x:=by
  intro q x
  have a:=WilsonReportingGuardedSource.purchased W life age (0:Site (R.family.side m per)) 4 x
  have issued:=R.makes.calibrated 4 m per age
  refine ⟨⟨a.1,a.2.1⟩,?_⟩
  calc
    _=Trace.Physical.GermGraph.page (C:=R.family) 4 per m ((R.family.factory 4 m per).entries m x):=by
      unfold Trace.Physical.GermGraph.page Germ.projection
      rw [show q.x=x from a.2.2.1,show q.regular=0 from a.2.2.2.1,
        show ((R.family.factory 4 m per).entries m x).x=x from issued.bare_coord x,
        show ((R.family.factory 4 m per).entries m x).regular=0 from issued.bare_germ x]
    _=x:=born R m per age x

theorem law {m N per:ℕ} (simple:G.Simple) (age:R.family.ref 4 ≤ m) (life:m ≤ N) (clock:ℝ)
    (v:ℕ→I→ℂ) (k:ℕ) (o:Site (R.family.side m per)) (U:Config G (R.family.side m per)):
    let P:=R.family.path.rep N per m
    (joined W Q life o clock v k).density o S P U=
      (R.family.S.a m:ℂ)^4*(P.eval U:ℂ)*(intercept Q R clock v k+stencil R (0,v k) _ o U):=by
  intro P
  let a (i:Fin (k+1)):=seed (R:=R) Q m per (0,submit Q clock v i.val) clock (k-i.val)
  let x:=table (R:=R) Q m per clock v k
  have expanded: (S).places ((F).scaled P.p.threshold⁻¹ x) o U=
      ∑i:Fin (k+1),(S).places ((F).scaled P.p.threshold⁻¹ (a i)) o U:=by
    change (S).evaluate ((F).scaled P.p.threshold⁻¹ (∑i:Fin (k+1),a i)) (expandAt o U)=
      ∑i:Fin (k+1),(S).evaluate ((F).scaled P.p.threshold⁻¹ (a i)) (expandAt o U)
    simp only [SectionData.evaluate,map_sum]
  have input:=WilsonReportingGuardedSource.purchased W life age o 4 x
  calc
    _ = (P.eval U:ℂ)*((S).places ((F).scaled P.p.threshold⁻¹ x) o U):=input.2.2.2.2 U
    _ = ∑i:Fin (k+1),(charged W Q life o (0,submit Q clock v i.val) clock (k-i.val)).density o S P U:=by
      rw [expanded,Finset.mul_sum]
      exact sum_congr rfl fun i _=>(WilsonReportingGuardedSource.purchased W life age o 4 (a i)).2.2.2.2 U |>.symm
    _ = _:=WilsonReportingMeasuredWardInverse.measured Q W simple age life clock v k o U

end YM.Integration.WilsonReportingMeasuredWardProgram
