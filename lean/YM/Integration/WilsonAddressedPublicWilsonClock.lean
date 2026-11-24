import YM.Integration.WilsonAddressedPublicGuardedRoster
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedPublicWilsonClock
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

/-- Comparison on the actual measured reporting stop and the original
    positive physical coupling, before either limit over tori. -/
theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)(bliss:Bliss F l z H)
    (v:ℕ)(vp:0<v):∀ᶠ r:ℝ in trail,
    let m:=WilsonMeasuredWindow.stop A₀ simple v r
    0<wilson z r ∧ wilson z r ≤ 1 ∧ a_ m ≤ r ∧ (wilson z r)⁻¹  ≤  H_ m:=by
  have dates:=WilsonMeasuredWindow.stop_tendsto A₀ simple v vp
  have link:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  let c:=G.slopeConstant⁻¹/2
  have slope:=Gauge.slopeConstant_pos simple
  have cp:0<c:=half_pos (inv_pos.mpr slope)
  have ct:c<G.slopeConstant⁻¹:=half_lt_self (inv_pos.mpr slope)
  filter_upwards [dates.eventually ((Station.hat_rate A₀ simple).eventually_ge_atTop 2),
    Ioc_mem_nhdsGT (R.family.S.a_pos 0),link.positive,(link.conforms simple).eventually (ge_mem_nhds zero_lt_one),
    link.running.eventually (le_mem_nhds ct)] with r big real gp gu run
  let m:=WilsonMeasuredWindow.stop A₀ simple v r
  have price:= (WilsonFundedMeasuredWindow.all_radii R slow simple vp).2 r real.1 real.2
  have bp:=zero_lt_one.trans (R.family.path.levels.fits.delayed m)
  have mb:1 ≤ RG16.Lambda A₀ m:=by unfold RG16.Lambda;linarith [Real.log_nonneg (R.family.path.levels.fits.delayed m).le]
  have near: a_ m ≤ r:=(one_le_div (R.family.S.a_pos m)).mp ((one_le_pow₀ mb).trans price.1)
  refine ⟨gp,gu,near,?_⟩
  let g:=wilson z r
  have logRate:LogV r ≤ R.family.S.scale m:=Real.log_le_log (inv_pos.mpr real.1) (inv_anti₀ (R.family.S.a_pos m) near)
  have aligned:G.slopeConstant*LogV r ≤ H_ m:=by
    have c0:=mul_le_mul_of_nonneg_left logRate slope.le
    change _  ≤  (A₀).clock.bar+G.slopeConstant*R.family.S.scale m
    linarith only [(A₀).clock.bar_pos,c0]
  have base:(2*G.slopeConstant)*c=1:=by unfold c;field_simp [slope.ne']
  have stable:1 ≤ (2*H_ m)*g^2:=calc
    1 = (2*G.slopeConstant)*c:=base.symm
    _  ≤  (2*G.slopeConstant)*(LogV r*g^2):=mul_le_mul_of_nonneg_left run (by positivity)
    _ = 2*(G.slopeConstant*LogV r)*g^2:=by ring
    _  ≤  (2*H_ m)*g^2:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left aligned (by norm_num)) (sq_nonneg _)
  have compare:g⁻¹^2 ≤ 2*H_ m:=by
    rw [inv_pow,←one_div]
    exact (div_le_iff₀ (pow_pos gp _)).mpr stable
  have enough:2*H_ m ≤ (H_ m)^2:=by nlinarith only [mul_nonneg bp.le (sub_nonneg.mpr big)]
  exact (sq_le_sq₀ (inv_nonneg.mpr gp.le) bp.le).mp (compare.trans enough)

end YM.Integration.WilsonAddressedPublicWilsonClock
end
