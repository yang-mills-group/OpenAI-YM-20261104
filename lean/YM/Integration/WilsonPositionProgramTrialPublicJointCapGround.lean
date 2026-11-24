import YM.Integration.WilsonPositionProgramTrialPublicJointCapRegistered
import YM.Integration.WilsonPositionProgramTrialPublicJointFourGroundVote

/-! At thermal order zero the native Wick matrix fixes each nonunit row on both genuinely placed groups. The difference therefore gives only a measured scalar feed before its rooted correction. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointCapGround
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels XSpace
open WilsonSurveyedEquationFrameInlet (bank master loan price)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) (W : Initialize G) {h hi D k u e : ℕ}
local notation "L" => R.family.path.levels
local notation "O" => R.metals.O
local notation "CC" => Credit.leanC


open WilsonIndependentMatchedReportedProxy (sectionSeal)
open WilsonIndependentMatchedFreshWhole (projected)
open WilsonPositionProgramTrialReverseLens (received)
open WilsonPositionProgramTrialFittedLens (matrix)
open WilsonPositionProgramTrialPublicJointCapFiling (sectionAt)
open WilsonSurveyedEquationFrameStability (course)

open WilsonPositionProgramTrialPublicJointCapArrival (high own linear)


open PowerSeries Matrix WilsonCoeffUV.Bank.Carp

theorem angular (simple:G.Simple)(cap:h≤6)(fit:h<D)(le:h≤hi)(height:h≤k)
    (A:Levels G)(m N:ℕ)(c:Verse (R.family.labels.level h))(i:Alma (R.family.labels.level h))
    (active:sheet (R.family.labels.level h) i≠0):
    wickT A m N k (R.family.labels.level h) (high R W le fit c-own R W fit c).2 i=0:=by
  let F:=R.family.labels.level h
  have pos:=F.factors_pos (sheet F i) active
  have off:=WilsonMaxwellThermometerWardColors.arity simple F (sheet F i)
  have two:2≤valence F i:=by change 2≤(F.grades (sheet F i)).2;omega
  have read (I:Island F D)(sh:Shimmer I):wickT A m N k F (Shrine I c).2 i=coeff 0 (c i):=by
    rw [WickBase A I sh c height]
    change ∑j:Alma F,wickM A m N F I.2 i j * coeff 0 (c j)=_
    simp_rw [WilsonPhysicalSixWickRows.retained cap I sh A m N i two]
    simp [Matrix.one_apply,ite_mul]
  have sh:=WilsonPositionProgramTrialPublicJointCapFiling.issued R W le
  have sl:=WilsonOriginalPivotWardSurvey.issued R W h
  have hp:=freshly _ W.hol fit sh.1 sh.2.1
  have hq:=freshly _ W.hol fit sl.1 sl.2.1
  change wickT A m N k F (Shrine _ c-Shrine _ c).2 i=0
  have eq:=clocksW A (Shrine_on (plate (sectionAt R W le) fit) hp c height)
    (Shrine_on (plate (WilsonOriginalPivotWardSurvey.sectionAt R W h) fit) hq c height) (le_refl k) i m N
  exact eq.trans (sub_eq_zero.mpr ((read (plate (sectionAt R W le) fit) hp).trans
    (read (plate (WilsonOriginalPivotWardSurvey.sectionAt R W h) fit) hq).symm))

theorem written {H:Hol G}(J:SectionData (R.family.labels.level h))
    (simple:G.Simple)(cap:h≤6)(fit:h<D)(le:h≤hi)(rails:Rails h k u e)(E U V B cash:Credit):
    ∃ C:Credit,∀(X:CutsP H J fit rails E U B V),Weston X.L.L cash →
    ∀(c:Verse (R.family.labels.level h)),X.pt=high R W le fit c-own R W fit c →
    ∀i:Alma (R.family.labels.level h),sheet (R.family.labels.level h) i≠0 →
      ‖coeff 0 (X.tileP i)‖ ≤ C.buy X.Age*X.ρ*X.fuel:=by
  obtain ⟨C,paid⟩:=fan_jet H J fit rails E U V B cash
  refine ⟨C,?_⟩
  intro X west c source i active
  have sum:=paid X west i
  have fixed:=WilsonPhysicalSixWickRows.nonunit X.L.L cap simple (X.hc.trans X.hn)
    (X.ha.trans (Nat.le_add_right X.m X.i)) i active (fun a=>coeff 0 (X.tileP a))
  change (Wray X.ax X.tx J fit X.N X.ceilC*ᵥ fun a=>coeff 0 (X.tileP a)) i=coeff 0 (X.tileP i) at fixed
  rw [fixed,source,angular R W simple cap fit le rails.hk _ _ _ _ i active,sub_zero] at sum
  exact sum

end YM.Integration.WilsonPositionProgramTrialPublicJointCapGround
