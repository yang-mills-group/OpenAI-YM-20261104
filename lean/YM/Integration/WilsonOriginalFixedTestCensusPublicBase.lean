import YM.Integration.WilsonOriginalCensusDatedSchools
import YM.Integration.WilsonOriginalFixedTestCensusPairedTickets

/-! The preannounced finite public test budgets pay both true reporting dates. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFixedTestCensusPublicBase
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology

open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Embroider
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Flooring
open Work.F08
open scoped BigOperators Classical


open FundedMarkedPathSelection
open PhysicalNext.Repeat.Legato WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Embroider.Canvas
open ComparisonDensity.Address WilsonCoeffUV.Shard WilsonCoeffUV.Winding OriginalIssuedMarkedRows
open ActualRunAdmissionScales OriginalBareMarkedInvoice Filter Function
open WilsonOlderFreshConnectedRobe WilsonCoeffUV.Bank.Ticket
open scoped Topology

open WilsonOlderFreshConnectedRobe WilsonOlderFreshGraphSlate WilsonOlderFreshConnectedRoll
open WilsonOlderFreshConnectedPin WilsonOlderFreshConnectedAppointment FundedMarkedCoverRows
open WilsonCoeffUV.Bank.Ticket

open WilsonOlderFreshConnectedBirth WilsonCoeffUV.Blue WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Carp
open WilsonOlderFreshConnectedBinding


open QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary Stationary
open WilsonOriginalPrimerReceipts WilsonNeutralTwoPrintPathJet
open Primitives.TwoWave AllOrder.Haiku AllOrder.Ink Response PertExtension.Series

open WilsonNeutralTwoPrintPathRoll WilsonOlderFreshConnectedAssembly
open Further.PhysicalPeriodLimitF933 Macrame Shingle AllOrder.Ker FVA1Physical FVA1Physical.TwoReset


open WilsonCoeffUV.Winding WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.Mosaic.Near
open WilsonNeutralTwoPrintPathRead

open WilsonNeutralTwoPrintPathFixed (parcel)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonReceivedFixedDigitCanonical (fixed)
open OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds
open WilsonNeutralTwoPrintPathQuoted (bill)

open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet Multi
open WilsonNeutralTwoPrintPathCensus (slates)
open WilsonNeutralTwoPrintPathDatedPolynomial (row sheet entry)
open WilsonReceivedCoverGrade (Same)
open FundedMarkedPathSelection (output)

open WilsonOriginalCensusDatedMaterial (Material words mounts)
open WilsonCapturedRootedAngularSlots WilsonCapturedPrimaryWindingMaterialRead WilsonNeutralTwoPrintPeg
open WilsonNeutralTwoPrintPathPolynomial RegulatorIR.Diagram

open WilsonOriginalCensusFaceSites (binder port pin frill root)
open WilsonOriginalCensusDatedSheets (sideValue)
open WilsonNeutralTwoPrintPathCalendar (spent)
open WilsonReceivedCompactVerseEntrance (submit)
open WilsonOriginalCensusFaceSheet (Addressed)
open WilsonReceivedDepositedOrbitalPrint (front)
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Express
open WilsonOriginalCensusFaceSites (root)

open WilsonOriginalCensusFaceSchools (Account)
variable {G:Gauge}{n:ℕ}(R:Run G)(simple:G.Simple)(B:ℝ)
local notation "χ" j:max => R.family.path.levels.clock.hatBeta (j)
local notation "rate" N:max per:max m:max δ:max =>
  (Real.sqrt (R.family.path.β N per (m+1)))^(δ:ℝ)*B^n
/-- The same base can be posted before any period or cutoff is chosen. -/
def base (cap:Fin n → ℝ)(d:Fin n → ℕ)(H:ℝ)(v:Fin n):ℝ:=max 1 (cap v * H^(d v) * B^n * H)

include simple in
theorem opening (cap:Fin n → ℝ) : ∀ᶠ m:ℕ in atTop,∀j,m ≤ j →
    2 ≤ χ (j+1) ∧ ∀v,cap v*B^n ≤ χ (j+1):=by
  let A:=R.family.path.levels
  let price:=∑v:Fin n,max 0 (cap v*B^n)
  have rise:Tendsto A.clock.hatBeta atTop atTop:=tendsto_atTop_add_const_left _ _
    (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  filter_upwards [rise.eventually_ge_atTop (max 2 price)] with m late
  intro j after
  have later:=WilsonStartup.Timing.hat_mono A (Gauge.slopeConstant_pos simple).le (after.trans (Nat.le_succ j))
  refine ⟨((le_max_left ..).trans late).trans later,fun v=>?_⟩
  have part:max 0 (cap v*B^n) ≤ price:=Finset.single_le_sum (f:=fun v=>max 0 (cap v*B^n))
    (fun _ _=>le_max_left ..) (Finset.mem_univ v)
  exact (((le_max_right ..).trans part).trans ((le_max_right ..).trans late)).trans later

include simple in
theorem actual_rate {m j N per:ℕ}{δ:ℝ}(after:m ≤ j)(live:m+1 ≤ N)
    (warm:2 ≤ χ (j+1))(p:0 ≤ δ)(small:δ ≤ 1)(one:1 ≤ B):
    rate N per m δ ≤ B^n * χ (j+1):=by
  let x:=χ (j+1)
  have base1:1 ≤ x:=by linarith only [warm]
  have x0:0 ≤ x:=zero_le_one.trans base1
  have rise:=WilsonStartup.Timing.hat_mono R.family.path.levels (Gauge.slopeConstant_pos simple).le
    (Nat.succ_le_succ after)
  have high:R.family.path.β N per (m+1) ≤ 2*χ (m+1):=(R.makes.wilson.represents N per (m+1) live).band.2
  have bounded:Real.sqrt (R.family.path.β N per (m+1)) ≤ x:=by
    apply Real.sqrt_le_iff.mpr
    refine ⟨x0,?_⟩
    rw [pow_two]
    exact (high.trans (mul_le_mul_of_nonneg_left rise (by norm_num))).trans (mul_le_mul_of_nonneg_right warm x0)
  have onePower:x^δ ≤ x:=by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le base1 small
  calc
    _ ≤ x*B^n:=mul_le_mul_of_nonneg_right ((Real.rpow_le_rpow (Real.sqrt_nonneg _) bounded p).trans onePower)
      (pow_nonneg (zero_le_one.trans one) _)
    _ = _:=mul_comm ..

include simple in
theorem published {m j N per:ℕ}{δ:ℝ}(after:m ≤ j)(live:m+1 ≤ N)(one:1 ≤ B)
    (warm:2 ≤ χ (j+1))(p:0 ≤ δ)(small:δ ≤ 1)(cap:Fin n → ℝ)(d:Fin n → ℕ)
    (stage:∀v,cap v*B^n ≤ χ (j+1)){D:Fin n → ℕ}(t:Case D)(test:∀v,‖t v‖ ≤ cap v*(χ (j+1))^(d v)):
    ∀v,0 < base B cap d (χ (j+1)) v ∧
      ‖t v‖ * (rate N per m δ) ≤ base B cap d (χ (j+1)) v ∧
      base B cap d (χ (j+1)) v ≤ (χ (j+1))^(d v+2):=by
  let x:=χ (j+1)
  have x1:1 ≤ x:=by linarith only [warm]
  have x0:0 ≤ x:=zero_le_one.trans x1
  have b0:0 ≤ B:=zero_le_one.trans one
  have r0:0 ≤ (rate N per m δ):=mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (pow_nonneg b0 _)
  have r1:=actual_rate (n:=n) (per:=per) R simple B after live warm p small one
  intro v
  refine ⟨zero_lt_one.trans_le (le_max_left ..),?_,max_le (one_le_pow₀ x1) ?_⟩
  · refine (mul_le_mul (test v) r1 r0 ((norm_nonneg _).trans (test v))).trans ?_
    exact (le_of_eq (by ring)).trans (le_max_right ..)
  · calc
      _ = (cap v*B^n)*(x^d v*x):=by ring
      _ ≤ x*(x^d v*x):=mul_le_mul_of_nonneg_right (stage v) (mul_nonneg (pow_nonneg x0 _) x0)
      _ = _:=by rw [pow_add,pow_two];ring

include simple in
/-- Fixed public test labels and all thresholds precede the original cutoff and period. -/
theorem fixed {D:Fin n → ℕ}(t:Case D)(one:1 ≤ B) :
    ∀ᶠ m:ℕ in atTop,∀j,m ≤ j → ∀N per:ℕ,m+1 ≤ N → ∀δ:ℝ,0 ≤ δ → δ ≤ 1 →
    ∀v,0 < base B (fun z=>‖t z‖) (fun _=>0) (χ (j+1)) v ∧
      ‖t v‖*(rate N per m δ) ≤ base B (fun z=>‖t z‖) (fun _=>0) (χ (j+1)) v ∧
      base B (fun z=>‖t z‖) (fun _=>0) (χ (j+1)) v ≤ (χ (j+1))^2:=by
  filter_upwards [opening R simple B (fun v=>‖t v‖)] with m late
  intro j after N per live δ p small v
  obtain ⟨warm,stage⟩:=late j after
  exact published (per:=per) R simple B after live one warm p small (fun v=>‖t v‖) (fun _=>0) stage t
    (fun v=>by simp) v

theorem norm_eq {D D':Fin n → ℕ}(t:Case D)(u:Case D')(kind:D'=D)(same:HEq u t)(v:Fin n):
    ‖u v‖=‖t v‖:=by subst D';rw [eq_of_heq same]

include simple in
theorem material {m j z N per q:ℕ}{δ σ:ℝ}{k D:Fin n → ℕ}{V:Realm G (q+1) Credit.leanC}
    {side:Side}{y:Fin n → Cover}(M:Material R N z q k σ (binder side y))(t:Case D)
    (owned:Account V (rate N per m δ) δ side y M t)(u:Case M.tests)(same:HEq u t)
    (after:m ≤ j)(live:m+1 ≤ N)(one:1 ≤ B)(warm:2 ≤ χ (j+1))(p:0 ≤ δ)(small:δ ≤ 1)
    (cap:Fin n → ℝ)(d:Fin n → ℕ)(stage:∀v,cap v*B^n ≤ χ (j+1))(test:∀v,‖t v‖ ≤ cap v*(χ (j+1))^(d v)):
    ∀v,0 < base B cap d (χ (j+1)) v ∧
      ‖u v‖*M.amplitude ≤ base B cap d (χ (j+1)) v ∧
      base B cap d (χ (j+1)) v ≤ (χ (j+1))^(d v+2):=by
  intro v
  rw [norm_eq t u owned.2.1 same v,owned.2.2.1]
  exact published R simple B after live one warm p small cap d stage t test v

end YM.Integration.WilsonOriginalFixedTestCensusPublicBase
end

