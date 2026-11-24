import YM.Integration.WilsonOriginalTwoFlatPublicOuter
import YM.Integration.WilsonOriginalTwoFlatPublicFare
import YM.Integration.WilsonOriginalTwoFlatPublicGeometry
import YM.Integration.WilsonReflectedPublicStationPrice
import YM.Integration.WilsonThermometerUnitFilingFourPoolBill

/-! Numerical source prices for the actual Vane vectors and the positioned
homogeneous pooled vectors at their declared public field scale. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatPublicNamedFare
open Lattice Wilson RG Source Extraction Maxwell Maxwell.Free RG05Readout
open PhysicalNext.Repeat.Legato FVA2 FVA2.Register MS MS.Land
open Function Filter Set Table Spec Climb GapsContact GapsContact.Seams OPE Trace.Pilot
open Next.Rank Next.Rank.Station MergeProof.East Next.UVStress
open Trace.Terrace Trace.Pilot
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare
open scoped Topology Classical

open WilsonInvariantActionPosition WilsonReflectedOriginalPrefixTariff
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) {l:Ultrafilter (ℕ×ℕ)} {z:Trace.Terrace.Arch R.family}
    {H:(Bel R.family.book).Hierarchy}
local notation "P" => R.family.path.levels
local notation "a" => R.family.S.a
local notation "β" => (P).clock.hatBeta

open Function Filter Set Table Spec Climb Maxwell Maxwell.Free RG05Readout
open Lattice Wilson RG Source Extraction OPE Trace.Pilot PhysMS Frame
open GapsContact GapsContact.Seams PhysicalNext.Repeat.Legato
open FVA2 FVA2.Register MS MS.Land
open WilsonPositionHomogeneousFrame
open WilsonThermometerUnitFilingFourPoolShell WilsonThermometerUnitFilingFourPoolClock
open scoped Classical Topology BigOperators
open GapsContact GapsContact.Seams
open Function Filter Set MeasureTheory Analysis Table Extraction Lattice RG Wilson
open Labels Source Push Extra.Histories Bid Spec Ascent Power Stamps
open Trace Trace.Verse Trace.Terrace Trace.Pilot Trace.Over MergeProof.East Further.CorrectedLift
open Next.Rank.Price Next.Rank Next.Rank.East Next.Rank.Station Ward Climb OPE OPE.Levy
open scoped Topology InnerProductSpace BigOperators ContDiff NNReal Matrix.Norms.Frobenius Classical
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonOriginalTwoFlatPublicFare (charge)
variable (J:ℝ→tower S)(Z:WilsonPrescription G)
local notation "C" => R.family

def chosen {d:ℕ}(r:ℝ)(U:Spin.change S d)(weak:Bool)(y:(Spin.comparator R.family.book).Field d)(x:RG17.Free R.family d):S.Field d:=
  if weak then U y else WilsonPositionHomogeneousFrame.homogeneous F J Z r d x

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(lead:Leading F J)
    (paid:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d)(d T:ℕ)(y:(Spin.comparator R.family.book).Field d)(x:RG17.Free C d):
    ∃K:ℝ,∃e:ℕ,1  ≤  K ∧ ∀ᶠ r in trail,∀{D k:ℕ}
    {stock:Bank F l D (WilsonThermometerUnitFilingFourPoolShell.radius z T r)
      (dock (WilsonThermometerUnitFilingFourPoolShell.radius z T r)^T)}
    {cap:d ≤ D}{W:Vane R.family k}{fits:D ≤ k}{U:Spin.change S d}
    (A:Pair F stock cap W fits U r),W.checked f H k → W.wheel.r=r →
    ∀j cashPower:ℕ, max stock.j W.k  ≤  j → r  ≤  (β j)^cashPower*a j →
    ∀b:Bool,charge F A j b (chosen F J Z r U b y x)
       ≤  K*(β j)^((2*T+3+cashPower)*(d+1)+e):=by
  obtain ⟨C₁,p₁,K₁,weakBill⟩:=WilsonReflectedPublicStationPrice.original C simple d
  obtain ⟨early,weakAt⟩:=eventually_atTop.mp weakBill
  obtain ⟨C₂,K₂,pooled⟩:=WilsonThermometerUnitFilingFourPoolBill.original F J Z simple bliss lead paid T 0 d x
  let t:=WilsonThermometerUnitFilingFourPoolBill.exponent T 0 d
  let e:=max p₁ (2*t)
  let A₀:=max 1 (max C₂ (C₁*‖Further.CorrectedLift.ladder C d y‖))
  have a0:1  ≤  A₀:=le_max_left ..
  refine ⟨2*A₀,e,by linarith,?_⟩
  have positive:=(wilson_link F simple bliss.budgets bliss.keen bliss.lies).positive
  filter_upwards [pooled,WilsonOriginalTwoFlatPublicOuter.original F simple bliss t,positive,
    (ge_mem_nhds (R.family.S.a_pos early)).filter_mono nhdsWithin_le_nhds,
    WilsonReflectedPublicStationSpan.original F simple bliss T] with r income gauge gp tiny ratios
  intro D k stock cap W fits U A checked live j h late cash b
  let m:=max stock.j W.k
  have dated:W.k ≤ m:=le_max_right ..
  have wr:a W.k ≤ r:=(WilsonReflectedPublicBulbBerth.mesh R W checked).trans live.le
  have mr:a m ≤ r:=((C).S.strictAnti.antitone dated).trans wr
  have wj:=dated.trans late
  have needed:early ≤ W.k:=by
    by_contra! h;exact (not_le_of_gt ((C).S.strictAnti h)) (wr.trans tiny)
  have more:=WilsonStartup.Timing.hat_mono (P) (Gauge.slopeConstant_pos simple).le
  have beta:1  ≤  β j:=((P).fits.delayed j).le
  have beta0:0  ≤  β j:=zero_le_one.trans beta
  have feeBound:fee F A b (chosen F J Z r U b y x)  ≤  A₀*(β j)^e:=by
    cases b with
    | false =>
      have turn:(wilson z r)⁻¹^t ≤ (β j)^(2*t):=by
        have weight:=gauge.2.2 j (((C).S.strictAnti.antitone late).trans mr)
        exact (mul_le_mul_iff_of_pos_left gauge.1).mp (by simpa only [outer,mul_comm ((β j)^(2*t)) r] using weight)
      have earned:dock (WilsonThermometerUnitFilingFourPoolShell.radius z T r)^T*
        Ascent.cost F d (WilsonThermometerUnitFilingFourPoolShell.radius z T r)
          (WilsonPositionHomogeneousFrame.homogeneous F J Z r d x)*(wilson z r)^t  ≤  C₂:=by
        simpa only [outer,pow_zero,mul_one] using income
      have head:(fee F A false (chosen F J Z r U false y x)) ≤ C₂*((wilson z r)⁻¹^t):=by
        rw [inv_pow,←div_eq_mul_inv]
        exact (le_div_iff₀ (pow_pos gp _)).mpr earned
      exact head.trans (mul_le_mul ((le_max_left C₂ _).trans (le_max_right 1 _))
        (turn.trans (pow_le_pow_right₀ beta (le_max_right ..))) (pow_nonneg (inv_nonneg.mpr gp.le) _) (zero_le_one.trans a0))
    | true =>
      have physical:preExpense C d W.k W.b  ≤  C₁*(β j)^p₁:=(weakAt _ needed _ checked.high.2).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans ((P).fits.delayed W.k).le) (more wj) _) (zero_le_one.trans K₁))
      calc
        _ = preExpense C d W.k W.b*‖Further.CorrectedLift.ladder C d y‖:=by simp [WilsonReflectedPublicStationFare.fee,chosen]
        _  ≤  C₁*(β j)^p₁*‖Further.CorrectedLift.ladder C d y‖:=mul_le_mul_of_nonneg_right physical (norm_nonneg _)
        _ = (C₁*‖Further.CorrectedLift.ladder C d y‖)*(β j)^p₁:=by ring
        _  ≤  _:=mul_le_mul ((le_max_right C₂ _).trans (le_max_right 1 _)) (pow_le_pow_right₀ beta (le_max_left ..)) (pow_nonneg beta0 _) (zero_le_one.trans a0)
  have rel:a (station F A b)/a j ≤ (β j)^(2*T+3+h):=by
    have h₁:=(ratios A checked live b).trans (pow_le_pow_left₀ (zero_le_one.trans ((P).fits.delayed m).le) (more late) _)
    have h₂: a m/a j ≤ (β j)^h:=(div_le_iff₀ ((C).S.a_pos _)).mpr (mr.trans cash)
    calc
      _ = (a (station F A b)/a m)*(a m/a j):=by field_simp [ne_of_gt ((C).S.a_pos m)]
      _  ≤  (β j)^(2*T+3)*(β j)^h:=mul_le_mul h₁ h₂ (div_nonneg ((C).S.a_pos _).le ((C).S.a_pos _).le) (pow_nonneg beta0 _)
      _ = _ :=(pow_add ..).symm
  refine max_le ?_ ?_
  · exact (le_mul_of_one_le_right (show 0 ≤ 2*A₀ by positivity) (one_le_pow₀ beta)).trans' (by linarith)
  · have slope:2*(a (station F A b)/a j)^(d+1)  ≤  2*((β j)^(2*T+3+h))^(d+1):=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (div_nonneg ((C).S.a_pos _).le ((C).S.a_pos _).le) rel _) zero_le_two
    calc
      _  ≤  (2*(a (station F A b)/a j)^(d+1))*(A₀*(β j)^e):=
        mul_le_mul_of_nonneg_left feeBound (mul_nonneg zero_le_two (pow_nonneg (div_nonneg ((C).S.a_pos _).le ((C).S.a_pos _).le) _))
      _  ≤  _ := (mul_le_mul_of_nonneg_right slope (mul_nonneg (zero_le_one.trans a0) (pow_nonneg beta0 _))).trans_eq (by
        rw [pow_add (β j) ((2*T+3+h)*(d+1)) e,pow_mul (β j) (2*T+3+h) (d+1)];ring)

end YM.Integration.WilsonOriginalTwoFlatPublicNamedFare
end
