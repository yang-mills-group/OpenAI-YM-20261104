import YM.Integration.WilsonRootedPhysicalLocalPeriod

/-! The Taylor tariff and logarithmic cutoff are set on the physical calendar before all periods. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedPhysicalTaylorPeriod
open Function Filter Finset Set Lattice Wilson RG RG.Shoot Pressure
open Push Push.AbsoluteSums Push.AbsoluteSums.Animals Gas Ursell Trees Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes PhysicalNext PhysicalNext.Repeat Legato
open ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.Blaze Blaze.March Captain
open Opera Height Beam Song Geo Greenbelt Next.Scheduling Extra.Iteration UVNext
open PriceCompiler Org Input Supply Pressure.Testing Time Roost Match Refrain WilsonStartup
open RG01Estimate RG01Estimate.CensusStep WilsonLimitConstruction.FundedCensusVacuum
open WilsonVacuumPreResetCatalogue
open scoped Topology BigOperators Classical

variable {G : Gauge} (R : Run G)

def allowance (m r : ℕ) := (2*gStep (2*R.alloy.B.a.clock.hatBeta (m+1)))^(r+1)/2

/-- Larger cutoffs remain available for a simultaneously chosen independent local catalogue. -/
def cutoff (m r : ℕ) : ℕ :=
  ⌈Real.log (max 1 (WilsonRootedPhysicalLocalPeriod.wallet R m / allowance R m r))⌉₊

lemma budget (m r D : ℕ) (hD : cutoff R m r≤D) :
    Real.exp (-(1:ℝ)*(D+1))*WilsonRootedPhysicalLocalPeriod.wallet R m≤allowance R m r :=by
  let b:=WilsonRootedPhysicalLocalPeriod.wallet R m
  let a:=allowance R m r
  let q:=max 1 (b/a)
  have hz:=WardBin.hot R.alloy.B.a (m+1)
  have ha:0<a:=by
    dsimp [a,allowance,gStep]
    positivity
  have hq:0<q:=zero_lt_one.trans_le (le_max_left ..)
  have h:Real.log q≤(D:ℝ)+1:=by
    have c:=Nat.le_ceil (Real.log q)
    exact (c.trans (Nat.cast_le.mpr hD)).trans (by linarith)
  have bound : q≤Real.exp ((D:ℝ)+1):=calc
    q = Real.exp (Real.log q):=(Real.exp_log hq).symm
    _ ≤ _ :=Real.exp_le_exp.mpr h
  have v:b/a≤Real.exp ((D:ℝ)+1):=(show b/a≤q from le_max_right ..).trans bound
  rw [neg_one_mul,Real.exp_neg,mul_comm,←div_eq_mul_inv,div_le_iff₀ (Real.exp_pos _)]
  simpa only [mul_comm] using (div_le_iff₀ ha).mp v

lemma window (simple : G.Simple) (r : ℕ) {N m : ℕ} (per : ℕ) (hm : m<N) :
    let β:=(R.family.path.rep N per (m+1)).beta
    let β₀:=(R.family.path.rep N per m).beta
    0<allowance R m r ∧ allowance R m r+allowance R m r≤(2*gStep β)^(r+1) ∧
      gStep β≤2*gStep β₀ :=by
  intro β β₀
  let a:=R.alloy.B.a
  have z:=R.makes.wilson.represents N per (m+1) (by omega)
  have z₀:=R.makes.wilson.represents N per m (by omega)
  have hβ : a.clock.hatBeta (m+1)/2≤β ∧ β≤2*a.clock.hatBeta (m+1):=z.band
  have h₀ : a.clock.hatBeta m/2≤β₀ ∧ β₀≤2*a.clock.hatBeta m:=z₀.band
  have o:=WardBin.hot a m
  have t:=WardBin.hot a (m+1)
  have b:0<β:=by linarith only [t,hβ.1]
  have b₀:0<β₀:=by linarith only [o,h₀.1]
  have u : gStep (2*a.clock.hatBeta (m+1))≤gStep β:=inv_anti₀ (Real.sqrt_pos.mpr b) (Real.sqrt_le_sqrt hβ.2)
  have pos:0<gStep (2*a.clock.hatBeta (m+1)):=by unfold gStep;positivity
  have paid: (2*gStep (2*a.clock.hatBeta (m+1)))^(r+1)≤(2*gStep β)^(r+1):=by gcongr
  have monotone:=Push.Corrected.Last.band_le a simple (Nat.le_succ m)
  have pair:β₀≤4*β:=by linarith only [monotone,h₀.2,hβ.1]
  have cmp:Real.sqrt β₀≤2*Real.sqrt β:=by
    simpa only [Real.sqrt_mul (by norm_num : (0:ℝ)≤4),show Real.sqrt (4:ℝ)=2 by norm_num] using Real.sqrt_le_sqrt pair
  refine ⟨?_,?_,?_⟩
  · change 0<(2*gStep (2*a.clock.hatBeta (m+1)))^(r+1)/2
    positivity
  · change _/2+_/2≤_
    linarith only [paid]
  · change (Real.sqrt β)⁻¹ ≤2*(Real.sqrt β₀)⁻¹
    calc (Real.sqrt β)⁻¹ = 2*(2*Real.sqrt β)⁻¹ := by rw [mul_inv_rev];ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (inv_anti₀ (Real.sqrt_pos.mpr b₀) cmp) (by norm_num)

/-- The complete genuine signed physical log at its actual Taylor order. The chart cutoff and
both small errors are elected before either period. -/
theorem original (simple : G.Simple) (salary : WilsonOriginalHighSelection.Salary G R.kit) (r:ℕ) :
    ∀ᶠm:ℕ in atTop,∀D≥cutoff R m r,∀N per,∀hm:m<N,let S:=station R N per m hm
    let H:=S.guide
    let X:=ledger R.kit H
    let d:=vacuum R.kit H H S.identity
    let a:=R.alloy.B.a
    let B:=a.budget m
    let β:=(R.family.path.rep N per (m+1)).beta
    let β₀:=(R.family.path.rep N per m).beta
    let w:=Time.forecastK a m R.kit.scout β
    ∀ᶠt:ℕ in atTop,let g:=portion R S r (WilsonRootedPhysicalHousing.spatial R S t D)
    let K:=Abacus.revise d g
    let E:=Abacus.revise d (d.logRead-g)
    let C:=WilsonRootedPhysicalHousing.rack R S r D t
    Local X B K (Opera.earlyFee (p:=R.kit.expense) R.alloy.B N m β) w ∧
    Local X B E (2*(2*gStep β)^(r+1)) w ∧ 2*(2*gStep β)^(r+1)≤2*(4*gStep β₀)^(r+1) ∧
    (∀W O,(R.family.path.rep N per m).eval W=earlyValue X (R.alloy.B.kin.path N m) (a.params m).clip B E β
      (Song.weighty H Chi.canonical O) (R.alloy.B.kin.alpha N m) W*Real.exp (-(∑x,C.maskedEntry B x W))) ∧
    ∀W x,Healthy B.threshold (neighbors (WilsonRootedPhysicalHousing.radius B D) x) W →
      C.maskedEntry B x W=C.polygon x W:=by
  filter_upwards [WilsonLimitConstruction.FundedCensusVacuum.paid R simple r,WilsonVacuumPreResetStation.actual R simple r]
    with m ticket actual D hD N per hm S H X d a B β β₀ w
  obtain ⟨positive,paid,couplings⟩:=window R simple r per hm
  have finite:=WilsonRootedPhysicalShortLog.original R S salary hm (ticket N per hm) D positive
  have dose:=(actual N per hm).2.2.2.2.2.2
  filter_upwards [finite] with t entry
  intro g K E C
  obtain ⟨hk,he,_⟩:=entry
  have bill:Real.exp (-(1:ℝ)*(D+1))*WilsonRootedPhysicalShortLog.tariff R N per m≤allowance R m r:=
    (mul_le_mul_of_nonneg_left (WilsonRootedPhysicalLocalPeriod.charged R per hm) (Real.exp_nonneg _)).trans (budget R m r D hD)
  have sum: (2*gStep β)^(r+1)+allowance R m r+Real.exp (-(1:ℝ)*(D+1))*WilsonRootedPhysicalShortLog.tariff R N per m≤
      2*(2*gStep β)^(r+1):=by linarith only [bill,paid]
  have hi:=VacuumListing.relax B he sum le_rfl
  refine ⟨hk,hi,?_,?_,fun W x clean=>C.chip_healthy B W x clean⟩
  · have gb:0≤gStep β:=by unfold gStep; positivity
    have factor : 2*gStep β≤4*gStep β₀:=by linarith only [couplings]
    gcongr
  · intro W O
    have rows:d.logRead=E.logRead+K.logRead:=by change d.logRead=(d.logRead-g)+g;rw [sub_add_cancel]
    rw [dose O,VacuumListing.reassemble B hi hk rows rfl β (Song.weighty H Chi.canonical O) (R.alloy.B.kin.path N m)
      (a.params m).clip W]
    congr 2
    exact congrArg Neg.neg (C.routes B W d)

end YM.Integration.WilsonRootedPhysicalTaylorPeriod
