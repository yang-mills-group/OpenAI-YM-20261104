import YM.Integration.WilsonAddressedPublicPrintingDate
import YM.Integration.WilsonAddressedPublicFiledFee
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedPublicSourceWage
open Function Filter Set MeasureTheory Finset Table Spec Climb Maxwell Maxwell.Free RG05Readout
open Lattice Wilson RG Source Extraction OPE Trace.Pilot PhysMS Frame Cells
open GapsContact GapsContact.Seams GapsContact.Stamps PhysicalNext.Repeat.Legato
open FVA2 FVA2.Register MS MS.Land Trace.Terrace MergeProof.East
open WilsonPositionHomogeneousFrame WilsonThermometerUnitFilingFourSquare
open WilsonThermometerUnitFilingFourPoolShell WilsonThermometerUnitFilingFourPoolClock
open WilsonMeasuredPublicSlots WilsonMeasuredPublicClearance 
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F:Final R.family f S) {l:Ultrafilter (ℕ×ℕ)}
    {z:Trace.Terrace.Arch R.family} {H:(Bel R.family.book).Hierarchy}


open RG05Readout.Address RG05Readout.Planes WilsonLimitConstruction Next.Rank RG05Readout
local notation "A₀" => R.family.path.levels
local notation "a_" => R.family.S.a
local notation "H_" => R.family.path.levels.clock.hatBeta


open WilsonInvariantActionPosition WilsonMeasuredPublicClearance
open WilsonThermometerUnitFilingFourPoolClock
local notation "depth_" T:max => deep T
local notation "shell" => WilsonThermometerUnitFilingFourPoolShell.radius

theorem cap {g H K χ A:ℝ}{e:ℕ}(gp:0<g)(Hp:0 ≤ H)(Kp:0 ≤ K)(one:1 ≤ χ)
    (h:g⁻¹ ≤ H)(paid:A*g^e ≤ K):A/χ ≤ K*H^e:=by
  have funds:A ≤ K*g⁻¹^e:=by
    rw [inv_pow,←div_eq_mul_inv]
    exact (le_div_iff₀ (pow_pos gp _)).mpr paid
  exact (div_le_iff₀ (zero_lt_one.trans_le one)).mpr
    ((funds.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_pos.mpr gp).le h _) Kp)).trans
      (le_mul_of_one_le_right (mul_nonneg Kp (pow_nonneg Hp _)) one))

/-- Each already published physical income can be restored in units of this
    reporting date on the true coupling. The exponent is the one paid for
    that input before the internal accuracy. -/
theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)(bliss:Bliss F l z H)
    (v u:ℕ)(vp:0<v):∀ᶠ r:ℝ in trail,
    let m:=WilsonMeasuredWindow.stop A₀ simple v r
    let f:=berth R u m
    ∀ {A K χ:ℝ}{e:ℕ},0 ≤ K → 1 ≤ χ → A*(wilson z r)^e  ≤  K →
      A/χ  ≤  K*(H_ f)^e:=by
  filter_upwards [WilsonAddressedPublicWilsonClock.original F simple slow bliss v vp] with r owned
  dsimp only
  intro A K χ e kp cp paid
  let m:=WilsonMeasuredWindow.stop A₀ simple v r
  let f:=berth R u m
  exact cap owned.1 (zero_lt_one.trans (R.family.path.levels.fits.delayed f)).le kp cp
    (owned.2.2.2.trans (WilsonReflectedOpticalStock.monotone R simple (arrival R u m).1.le)) paid

/-- Restore the true salary before spending the remaining purchase on the
    receiving physical stores or on a crossing residual. -/
theorem debit {H A χ K Y:ℝ}{e E q:ℕ}(clock:1 ≤ H)(kp:0 ≤ K)(before:e ≤ E)
    (original:A/χ ≤ K*H^e)(heard:Y ≤ 8*(A/χ)*(H^(q+E))⁻¹):
    Y  ≤  8*K*(H^q)⁻¹:=by
  have hp:=zero_lt_one.trans_le clock
  have given:(A/χ) ≤ K*H^E:=original.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ clock before) kp)
  refine heard.trans ?_
  calc
    _  ≤  8*(K*H^E)*(H^(q+E))⁻¹:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left given (by norm_num))
      (inv_nonneg.mpr (pow_nonneg hp.le _))
    _ = _:=by rw [pow_add];field_simp [hp.ne']

end YM.Integration.WilsonAddressedPublicSourceWage
end
