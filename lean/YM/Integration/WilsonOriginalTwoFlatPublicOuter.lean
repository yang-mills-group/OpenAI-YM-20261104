import YM.Integration.WilsonReflectedPublicStationSpan
import YM.Integration.WilsonReflectedOpticalWidth

/-! At the actual common optical berth the entire finite separated physical
shape fits a reflection chamber and clears the native interaction radius. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatPublicOuter
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

open WilsonThermometerUnitFilingFourPoolClock (outer longer)

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(h:ℕ):
    ∀ᶠ r in trail,0<r ∧ r  ≤  outer z h r ∧ ∀j,a j ≤ r → outer z h r  ≤  (β j)^(2*h)*r:=by
  have link:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  let slope:=G.slopeConstant
  have sp:0<slope:=Gauge.slopeConstant_pos simple
  obtain ⟨m,after⟩:=eventually_atTop.mp ((hat_rate (P) simple).eventually_ge_atTop 2)
  have half:slope⁻¹/2<slope⁻¹:=half_lt_self (inv_pos.mpr sp)
  filter_upwards [self_mem_nhdsWithin,link.positive,(link.conforms simple).eventually (ge_mem_nhds zero_lt_one),
    link.running.eventually (le_mem_nhds half),
    (ge_mem_nhds (R.family.S.a_pos m)).filter_mono nhdsWithin_le_nhds] with r rp gp gu wage fine
  change 0<r at rp
  change slope⁻¹/2  ≤  LogV r*(wilson z r)^2 at wage
  have one:1 ≤ (wilson z r)⁻¹:=by simpa using inv_anti₀ gp gu
  refine ⟨rp,le_mul_of_one_le_right rp.le (one_le_pow₀ one),?_⟩
  intro j mesh
  have mj:m ≤ j:=by
    by_contra! earlier
    exact (not_le_of_gt (R.family.S.strictAnti earlier)) (mesh.trans fine)
  have H:=after j mj
  have lg:LogV r  ≤  R.family.S.scale j:=Real.log_le_log (inv_pos.mpr rp) (inv_anti₀ (R.family.S.a_pos j) mesh)
  have cash:slope*R.family.S.scale j  ≤  β j:=le_add_of_nonneg_left (P).clock.bar_pos.le
  have base:slope*(slope⁻¹/2)  ≤  β j*(wilson z r)^2:=by
    calc
      _  ≤  slope*(LogV r*(wilson z r)^2):=mul_le_mul_of_nonneg_left wage sp.le
      _ ≤ _:=by
        rw [←mul_assoc]
        exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left lg sp.le).trans cash) (sq_nonneg _)
  have run:1  ≤  2*β j*(wilson z r)^2:=by
    have fixed:slope*(slope⁻¹/2)=1/2:=by field_simp [sp.ne']
    rw [fixed] at base
    linarith only [base]
  have square:2*β j  ≤  (β j)^2:=by nlinarith only [mul_nonneg (sub_nonneg.mpr H) (show 0 ≤ β j by linarith)]
  have g2:(wilson z r)^2  ≤  wilson z r:=by nlinarith only [mul_nonneg gp.le (sub_nonneg.mpr gu)]
  have rate:(wilson z r)⁻¹ ≤ (β j)^2:=by
    rw [←one_div]
    apply (div_le_iff₀ gp).2
    exact run.trans (mul_le_mul square g2 (sq_nonneg _) (sq_nonneg _))
  change r*((wilson z r)⁻¹)^h  ≤  _
  rw [pow_mul]
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr gp.le) rate h) rp.le).trans_eq (mul_comm ..)

end YM.Integration.WilsonOriginalTwoFlatPublicOuter
end
