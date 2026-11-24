import YM.Integration.WilsonReflectedMixedFundedSeat
import YM.Integration.WilsonReflectedMixedMountedCoupon
import YM.Integration.WilsonReflectedPublicCommonEstate
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedMixedSignedCampus
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


open WilsonReflectedFundedHearing WilsonReflectedOpticalArm WilsonReflectedPublicCommonDose
open WilsonReflectedPublicGuardedColumns
local notation "β" => R.family.path.levels.clock.hatBeta


open WilsonReflectedMixedFundedSeat WilsonReflectedMixedThermalArms
open WilsonMeasuredPublicEntranceGridDebit WilsonOriginalMicroscopicGuardedReporters
open WilsonReflectedPublicCommonEstate WilsonReflectedRestoredStation

theorem rotated {d N p f K:ℕ}(A:Arm R d N p f K)(c:ℝ)(cp:0≤c)(small:c≤1){bank:ℝ}
    (raw:((C₀).labels.level d).coeffSize ((((C₀).S.a K:ℂ)^d)⁻¹ • A.w)≤bank):
    ((C₀).labels.level d).coeffSize (((c:ℂ)*(((C₀).S.a K:ℂ)^d)⁻¹) • WilsonReflectedPublicGuardedMotion.coords R A) ≤
      orbitCost ((C₀).labels.level d)*bank:=by
  let Ω:=orbitCost ((C₀).labels.level d)
  let v:=(((C₀).S.a K:ℂ)^d)⁻¹
  have op:0≤Ω:=zero_le_one.trans (orbitCost_one_le _)
  have price:=patch_cost ((C₀).labels.level d) (A.s,A.b) A.w
  have base:0≤‖v‖*((C₀).labels.level d).coeffSize A.w:=mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun _ _=>norm_nonneg _)
  rw [Size.smul] at raw
  rw [Size.smul,norm_mul,Complex.norm_real,Real.norm_of_nonneg cp]
  calc
    _ ≤ (c*‖v‖)*(Ω*((C₀).labels.level d).coeffSize A.w):=
      mul_le_mul_of_nonneg_left price (mul_nonneg cp (norm_nonneg _))
    _ = Ω*(c*(‖v‖*((C₀).labels.level d).coeffSize A.w)):=by ring
    _ ≤ _:=mul_le_mul_of_nonneg_left ((mul_le_of_le_one_left base small).trans raw) op

/-- One fixed floor for the original census at f and the fitted rows at their
individual reporter dates.  The same A and original budget are used at K. -/
theorem original (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)(d e:I→ℕ):
    ∃floor:ℕ,∀(j:I→ℕ)(_start:∀i,floor≤j i) {N p f K target power:ℕ}(_late:floor≤f)(up:f<K)(live:K≤N)
    (Y:(i:I)→(C₀).label (d i))(M:I→ℝ)(_pos:∀i,0≤M i)(bank:ℝ)
    (_seats:∀i,Seat R (d i) (j i) target N p f K (e i) up.le live (Y i) (M i) (bank*(β K)^power))
    (V:(i:I)→Sight C₀ (d i) p)(u:(i:I)→Emblems C₀ (d i))(home:∀i,Opened C₀ (d i) f p)
    (_enrolled:∀i,Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) f N p (d i)
      (digits R N p 0) (V i) (u i))(_ref:∀i k,k≤d i→(C₀).ref k≤f)
    (turn:I→Motion)(root:I→Site ((C₀).side f p))(names:Census I)(t:ℕ),
    let y:=fun i=>offer R (Y i) (home i) (up.le.trans live)
    WilsonThermometerReflectedRoster.filed R d (fun _=>0) turn root (fun i=>reduce (y i)) V u names (up.le.trans live) t →
    ∃(before:∀i,j i≤f)(F:(i:I)→(C₀).label (d i) ≃ₗ[ℂ] (C₀).label (d i)),
    (∀i a,Arrived R (d i) (j i) K N p target ((before i).trans up.le) live (1/32) (F i) a) ∧
    ∀i,Ready (R:=R) (e i) (orbitCost ((C₀).labels.level (d i))*bank) power
      (rent R (d i) (M i)) (Y i) (j i) 1 (F i) (V i) (u i) (home i) up live (turn i) (root i):=by
  classical
  obtain ⟨floor,bought⟩:=eventually_atTop.mp ((WilsonReflectedMixedMountedCoupon.original R simple shop d e).and
    (Filter.eventually_all.mpr (fun i=>WilsonAddressedRestartedFiled.original R (d i) simple)))
  refine ⟨floor,?_⟩
  intro j start N p f K target power late up live Y M pos bank seats V u home enrolled ref turn root names t y filed
  choose before F issued capital atSite using seats
  choose A ay aw ab angle pin tickets using fun i=>atSite i (turn i).1 (turn i).2 (root i)
  have granted:=(bought f late).1 N p K up.le live A V u home enrolled ref (fun i=>rent R (d i) (M i))
    (fun i=>mul_nonneg (mul_nonneg (by norm_num) (pos i)) (zero_le_one.trans (le_max_left ..))) tickets names t
  simp only [angle,ab,pin,ay,Prod.mk.eta] at granted
  have earned:=granted filed
  refine ⟨before,F,issued,?_⟩
  intro i
  unfold Ready
  intro offer_i χ c θ wage Ω
  have ok:j i≤K:=(before i).trans up.le
  let w:=(F i).symm (fitted R (d i) (j i) N p (Y i))
  have calibrated:WilsonOriginalMicroscopicGuardedPage.full R (d i) N p (j i) (Y i)=
      fitted R (d i) (j i) N p (Y i):=WilsonOriginalMicroscopicGuardedPage.page_at R (d i) (ok.trans live) (Y i)
  obtain ⟨z,zvalid⟩:=(bought (j i) (start i)).2 i N p K ok live target (1/32) (F i)
    (((C₀).factory (d i) N p).terminal.symm (Y i)) (issued i _) K ok le_rfl 0
  let L:Arm R (d i) N p K K:=⟨Y i,w,(turn i).2,(turn i).1,((C₀).S.toDepth up.le p).embed (root i),
    _,z,zvalid⟩
  have aligned:Situated R up.le (A i) L:=⟨(ay i).symm,(aw i).symm,(ab i).symm,(angle i).symm,congrArg (fun t=>((C₀).S.toDepth up.le p).embed t) (pin i).symm⟩
  refine ⟨A i,ay i,(aw i).trans (congrArg (F i).symm calibrated.symm),ab i,angle i,pin i,⟨L,aligned⟩,?_⟩
  obtain ⟨Q,E,paid⟩:=earned i
  refine ⟨Q,E,?_,?_⟩
  · rw [WilsonReflectedPublicDoseField.marked_real R (N:=N) 0 (turn i) (root i) (V i) (u i) (reduce offer_i) (c*χ) f]
    exact paid
  · have one:1≤χ:=le_max_left ..
    have residual:=rotated R (A i) (bank:=bank*(β K)^power) c (WilsonReflectedPublicCommonDose.positive ..).le
      (WilsonReflectedPublicCommonDose.smaller χ (rent R (d i) (M i)) 1 one).1
      (by rw [aw i];exact capital i)
    exact residual.trans_eq (mul_assoc _ _ _).symm

end YM.Integration.WilsonReflectedMixedSignedCampus
end
