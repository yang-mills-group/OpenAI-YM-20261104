import YM.Integration.WilsonReflectedMixedSignedCampus
import YM.Integration.WilsonReflectedPublicDoseField
/-! The two-flat entrance on a previously specified master fit and its already issued arm at each physical site. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntrancePrescribedCampus
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

theorem original (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)(d e:I→ℕ):
    ∃floor:ℕ,∀(j:I→ℕ)(_start:∀i,floor≤j i) {N p f K target power:ℕ}(_late:floor≤f)(up:f<K)(live:K≤N)
    (Y:(i:I)→(C₀).label (d i))(M:I→ℝ)(_pos:∀i,0≤M i)(bank:ℝ)
    (before:∀a,j a≤f)(F:(a:I)→(C₀).label (d a) ≃ₗ[ℂ] (C₀).label (d a))
    (_filed:∀a x,Arrived R (d a) (j a) K N p target ((before a).trans up.le) live (1/32) (F a) x)
    (_capital:∀a,((C₀).labels.level (d a)).coeffSize ((((C₀).S.a K:ℂ)^(d a))⁻¹ •
      (F a).symm (fitted R (d a) (j a) N p (Y a)))≤bank*(β K)^power)
    (V:(i:I)→Sight C₀ (d i) p)(u:(i:I)→Emblems C₀ (d i))(home:∀i,Opened C₀ (d i) f p)
    (_enrolled:∀i,Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) f N p (d i)
      (digits R N p 0) (V i) (u i))(_ref:∀i k,k≤d i→(C₀).ref k≤f)
    (turn:I→Motion)(root:I→Site ((C₀).side f p))(A:∀a,Arm R (d a) N p f K)
    (_pose:∀a,(A a).Y=Y a ∧ (A a).w=(F a).symm (fitted R (d a) (j a) N p (Y a)) ∧
      (A a).b=(turn a).2 ∧ (A a).s=(turn a).1 ∧ (A a).o=root a)
    (_paid:∀a,Priced R (A a) (rent R (d a) (M a)*((β f)^(e a+1))⁻¹*((C₀).S.a f)^(d a)))
    (names:Census I)(t:ℕ),
    let y:=fun i=>offer R (Y i) (home i) (up.le.trans live)
    WilsonThermometerReflectedRoster.filed R d (fun _=>0) turn root (fun i=>reduce (y i)) V u names (up.le.trans live) t →
    let χ:=fun a=>charge (y a)
    let c:=fun a=>dose (χ a) (rent R (d a) (M a)) 1
    let θ:=fun a=>(c a*χ a:ℝ)
    let old:=fun a=>marked R (N:=N) 0 (turn a) (root a) (V a) (u a) (reduce (y a)) f
    let paid:=fun a=>marked R (N:=N) 0 (turn a) (root a) (V a) (u a) ((θ a:ℂ) • reduce (y a)) f
    let P:=(C₀).path.rep N p f
    ∃X E:∀a,Coefficient ((C₀).labels.level (d a)) ((C₀).side f p),
      (∀a,(A a).w=(F a).symm (WilsonOriginalMicroscopicGuardedPage.full R (d a) N p (j a) (Y a)) ∧
        ∃L:Arm R (d a) N p K K,Situated R up.le (A a) L) ∧
      (∀a,0<c a ∧ c a≤1 ∧ ‖(θ a:ℂ)‖≤1 ∧ (c a:ℂ)=(θ a:ℂ)/(χ a:ℂ)) ∧
      (∀a,let Ω:=orbitCost ((C₀).labels.level (d a))
        let w:=WilsonReflectedPublicMountedInvoice.wage R f
        WilsonReflectedPublicGuardedColumns.Joined R (A a) up.le live (c a:ℂ) (paid a) w (Ω*(1+w))
          ((2+Ω)*((β f)^(e a))⁻¹) (X a) (E a)) ∧
      (∀a W,(X a).exponentialEntry ((A a).o) ((C₀).localSection (d a)) P W=(θ a:ℂ)*(old a).2.1 W) ∧
      (∀a,((C₀).labels.level (d a)).coeffSize (((c a:ℂ)*(((C₀).S.a K:ℂ)^(d a))⁻¹) •
        WilsonReflectedPublicGuardedMotion.coords R (A a))≤(orbitCost ((C₀).labels.level (d a))*bank)*(β K)^power):=by
  classical
  obtain ⟨floor,bought⟩:=eventually_atTop.mp ((WilsonReflectedMixedMountedCoupon.original R simple shop d e).and
    (Filter.eventually_all.mpr (fun a=>WilsonAddressedRestartedFiled.original R (d a) simple)))
  refine ⟨floor,?_⟩
  intro j start N p f K target power late up live Y M pos bank before F issued capital V u home enrolled
    ref₀ turn root A pose ticket names t y filed χ c θ old paid P
  have ay(a):=(pose a).1
  have aw(a):=(pose a).2.1
  have ab(a):=(pose a).2.2.1
  have angle(a):=(pose a).2.2.2.1
  have pin(a):=(pose a).2.2.2.2
  have granted:=(bought f late).1 N p K up.le live A V u home enrolled ref₀ (fun a=>rent R (d a) (M a))
    (fun a=>mul_nonneg (mul_nonneg (by norm_num) (pos a)) (zero_le_one.trans (le_max_left ..))) ticket names t
  simp only [angle,ab,pin,ay,Prod.mk.eta] at granted
  choose X E rows using granted filed
  refine ⟨X,E,?_,?_,?_,?_,?_⟩
  · intro a
    have ok:j a≤K:=(before a).trans up.le
    have same:=WilsonOriginalMicroscopicGuardedPage.page_at (p:=p) R (d a) (ok.trans live) (Y a)
    obtain ⟨z,valid⟩:=(bought (j a) (start a)).2 a N p K ok live target (1/32) (F a)
      (((C₀).factory (d a) N p).terminal.symm (Y a)) (issued a _) K ok le_rfl 0
    let L:Arm R (d a) N p K K:=⟨Y a,(F a).symm (fitted R (d a) (j a) N p (Y a)),(turn a).2,(turn a).1,
      ((C₀).S.toDepth up.le p).embed (root a),_,z,valid⟩
    refine ⟨(aw a).trans (congrArg (F a).symm same.symm),L,?_,?_,?_,?_,?_⟩
    · exact (ay a).symm
    · exact (aw a).symm
    · exact (ab a).symm
    · exact (angle a).symm
    · exact congrArg (fun t=>((C₀).S.toDepth up.le p).embed t) (pin a).symm
  · intro a
    have large:(1:ℝ)≤χ a:=le_max_left _ _
    have beam:=WilsonReflectedPublicCommonDose.smaller (χ a) (rent R (d a) (M a)) 1 large
    refine ⟨WilsonReflectedPublicCommonDose.positive ..,beam.1,?_,?_⟩
    · rw [Complex.norm_real,Real.norm_of_nonneg beam.2.1];exact beam.2.2.1
    · rw [div_eq_mul_inv];exact (WilsonReflectedPublicCommonDose.composed (χ a) (rent R (d a) (M a)) 1 large).symm
  · intro a
    dsimp only [paid]
    rw [WilsonReflectedPublicDoseField.marked_real]
    exact rows a
  · intro a W
    rw [←(rows a).regular]
    rfl
  · intro a
    have amt:=WilsonReflectedMixedSignedCampus.rotated R (A a) (bank:=bank*(β K)^power) (c a)
      (WilsonReflectedPublicCommonDose.positive ..).le
      (WilsonReflectedPublicCommonDose.smaller (χ a) (rent R (d a) (M a)) 1 (le_max_left ..)).1
      (by rw [aw a];exact capital a)
    exact amt.trans_eq (mul_assoc _ _ _).symm

end YM.Integration.WilsonMeasuredPublicEntrancePrescribedCampus
end
