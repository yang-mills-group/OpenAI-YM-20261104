import YM.Integration.WilsonRootedPhysicalShortLog
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Boulevard.Dawn
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Equip

/-! A local original physical catalogue with its truncation chosen before all cutoffs and periods. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedPhysicalLocalPeriod
open Function Filter Finset Set Lattice Wilson RG RG.Shoot Pressure
open Push Push.AbsoluteSums Push.AbsoluteSums.Animals Gas Ursell Trees Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes PhysicalNext PhysicalNext.Repeat Legato
open ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.Blaze Blaze.March Captain
open Opera Height Beam Song Geo Greenbelt Next.Scheduling Extra.Iteration UVNext
open PriceCompiler Org Input Supply Pressure.Testing Time Roost Match Refrain WilsonStartup
open RG01Estimate RG01Estimate.CensusStep WilsonLimitConstruction.FundedCensusVacuum
open WilsonVacuumPreResetCatalogue WilsonRootedPhysicalPathCover
open scoped Topology BigOperators Classical

variable {G : Gauge} (R : Run G)

/-- All numerical inputs are functions of the appointed history and the date alone. -/
def wallet (m : ℕ) :=
  let a:=R.alloy.B.a
  let p:=regularPoint (a.budget m)
  let k:=a.params m
  let σ:=2*k.width/3
  let s i:=anchoredFee (headline p) i
  let fee (i : ℕ) (A C : ℝ):=s (Song.octave i)*(|VerifiedReset.factor| *A*(turnFee p*(Geo.highFee G i p σ*p.threshold^i*C)))
  let j:=a.clock.J (m+1)
  let A:=2*a.clock.hatBeta (m+1)
  let b:=Pane.cloak R.rolls j
  let wage:=R.kit.expense j (a.clock.J m)
  turnFee p*((a.clock.hatBeta (m+1))^wage.wanting +
    (s Geo.lowCount*(|VerifiedReset.factor| *b*(turnFee p*p.threshold^2*(Geo.lowFee G p σ*lowerSize k.clip k.paths)))+
      (fee 3 A k.paths+(fee 4 A k.paths+fee 2 1 (a.clock.loopCap m)))))

lemma charged {N m : ℕ} (per : ℕ) (hm : m<N) : WilsonRootedPhysicalShortLog.tariff R N per m≤wallet R m:=by
  let a:=R.alloy.B.a
  let k:=a.params m
  let p:=regularPoint (a.budget m)
  let σ:=2*k.width/3
  let β:=(R.family.path.rep N per (m+1)).beta
  let A:=2*a.clock.hatBeta (m+1)
  let b:=Pane.cloak R.rolls (a.clock.J (m+1))
  have z:= (R.makes.wilson.represents N per (m+1) (by omega)).band
  have hβ : |β|≤A:=by
    have hpos : 0<a.clock.hatBeta (m+1):=WardBin.hot _ _
    have lower : a.clock.hatBeta (m+1)/2≤β:=z.1
    have hb : 0≤β:=by linarith only [hpos,lower]
    rw [abs_of_nonneg hb]
    exact z.2
  have hα : |R.alloy.B.kin.alpha N m|≤b:=Boulevard.coupling R.alloy N m hm
  have hs : 0<σ:=by dsimp [σ]; linarith only [k.width_pos]
  have hΛ : 0≤a.clock.loopCap m:=Cost.nonneg (R.alloy.B.support.cap N m hm.le).two
  have bill:=Meadow.rain G k.clip hs k.paths_pos.le p p ⟨rfl,rfl,rfl⟩ hβ hα le_rfl hΛ le_rfl
  exact mul_le_mul_of_nonneg_left (add_le_add_right bill _) (turnFee_pos p).le

/-- A spatial cutoff can be elected at this date before either regulator. -/
lemma buy (m : ℕ) {δ:ℝ} (hδ : 0<δ) : ∃D:ℕ,Real.exp (-(1:ℝ)*(D+1))*wallet R m≤δ:=by
  obtain ⟨D,hD⟩:=exists_nat_ge (wallet R m/δ)
  refine ⟨D,?_⟩
  have q : wallet R m≤δ*D:=by simpa only [mul_comm] using (div_le_iff₀ hδ).mp hD
  have e : (D:ℝ)≤Real.exp ((D:ℝ)+1):=by linarith only [Real.add_one_le_exp ((D:ℝ)+1)]
  rw [neg_one_mul,Real.exp_neg,mul_comm,←div_eq_mul_inv,div_le_iff₀ (Real.exp_pos _)]
  exact q.trans (mul_le_mul_of_nonneg_left e hδ.le)

/-- One pre-period radius, exact masked density at every rough field, and the authentic unmasked
polygon on its healthy root neighborhood. Both complementary physical sources keep the old hard bank. -/
theorem original (simple : G.Simple) (salary : WilsonOriginalHighSelection.Salary G R.kit) (r:ℕ)
    {η δ : ℝ} (eη : 0<η) (eδ : 0<δ) :
    ∀ᶠm:ℕ in atTop,∃D:ℕ,∀N per,∀hm:m<N,let S:=station R N per m hm
    let H:=S.guide
    let X:=ledger R.kit H
    let d:=vacuum R.kit H H S.identity
    let a:=R.alloy.B.a
    let B:=a.budget m
    let β:=(R.family.path.rep N per (m+1)).beta
    let w:=Time.forecastK a m R.kit.scout β
    ∀ᶠt:ℕ in atTop,let π:=WilsonRootedPhysicalHousing.spatial R S t D
    let g:=portion R S r π
    let K:=Abacus.revise d g
    let E:=Abacus.revise d (d.logRead-g)
    let C:=WilsonRootedPhysicalHousing.rack R S r D t
    Local X B K (Opera.earlyFee (p:=R.kit.expense) R.alloy.B N m β) w ∧
    Local X B E (((2*gStep β)^(r+1)+η)+δ) w ∧
    (∀W O,(R.family.path.rep N per m).eval W=earlyValue X (R.alloy.B.kin.path N m) (a.params m).clip B E β
      (Song.weighty H Chi.canonical O) (R.alloy.B.kin.alpha N m) W*Real.exp (-(∑x,C.maskedEntry B x W))) ∧
    ∀W x,Healthy B.threshold (neighbors (WilsonRootedPhysicalHousing.radius B D) x) W →
      C.maskedEntry B x W=C.polygon x W:=by
  filter_upwards [WilsonLimitConstruction.FundedCensusVacuum.paid R simple r,WilsonVacuumPreResetStation.actual R simple r]
    with m ticket actual
  obtain ⟨D,discount⟩:=buy R m eδ
  refine ⟨D,?_⟩
  intro N per hm S H X d a B β w
  have p:=WilsonRootedPhysicalShortLog.original R S salary hm (ticket N per hm) D eη
  have dose:=(actual N per hm).2.2.2.2.2.2
  filter_upwards [p] with t entry
  intro π g K E C
  obtain ⟨hk,he,_⟩:=entry
  have bill: Real.exp (-(1:ℝ)*(D+1))*WilsonRootedPhysicalShortLog.tariff R N per m ≤δ:=
    (mul_le_mul_of_nonneg_left (charged R per hm) (Real.exp_nonneg _)).trans discount
  have hi:=VacuumListing.relax B he (add_le_add_right bill _) le_rfl
  refine ⟨hk,hi,?_,fun W x clean=>C.chip_healthy B W x clean⟩
  intro W O
  have rows:d.logRead=E.logRead+K.logRead:=by change d.logRead=(d.logRead-g)+g;rw [sub_add_cancel]
  rw [dose O,VacuumListing.reassemble B hi hk rows rfl β (Song.weighty H Chi.canonical O) (R.alloy.B.kin.path N m)
    (a.params m).clip W]
  congr 2
  exact congrArg Neg.neg (C.routes B W d)

end YM.Integration.WilsonRootedPhysicalLocalPeriod
