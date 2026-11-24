import YM.Integration.WilsonThermometerUnitFilingFourPoolRent
import YM.Integration.WilsonThermometerUnitFilingFourPoolClock

/-! One fixed power of the measured coupling buys the original factory and reflected
tests at the smaller mesh, for a near or outer physical diploma. -/
set_option autoImplicit false
set_option maxHeartbeats 340000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingFourPoolBill
open Function Filter Set Table Spec Climb Maxwell Maxwell.Free RG05Readout
open Lattice Wilson RG Source Extraction OPE Trace.Pilot PhysMS Frame
open GapsContact GapsContact.Seams PhysicalNext.Repeat.Legato
open FVA2 FVA2.Register MS MS.Land
open WilsonPositionHomogeneousFrame
open WilsonThermometerUnitFilingFourPoolShell WilsonThermometerUnitFilingFourPoolClock
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
  (F : Final R.family f S) (J : ℝ→tower S) (Z : WilsonPrescription G)
  {l : Ultrafilter (ℕ×ℕ)} {z : Trace.Terrace.Arch R.family}
  {H : (Bel R.family.book).Hierarchy}

def exponent (T A d : ℕ) := 2*T+(2*T+4+A)*(d+1)

theorem original (simple : G.Simple) (bliss : Bliss F l z H) (lead : Leading F J)
    (paid : ∀ d : ℕ, ∀ᶠ r in trail, Frame.obedient F H (J r) d)
    (T A d : ℕ) (v : RG17.Free R.family d) :
    ∃ B : ℝ, 0≤B ∧ ∀ᶠ r in trail,
      let s := radius z T r
      let u := outer z A r
      (dock s^T * Ascent.cost F d s (homogeneous F J Z u d v)) *
        (wilson z r)^(exponent T A d) ≤ B := by
  let k := 2*T+4
  let g := wilson z
  let u := outer z A
  let a := fun r=> g r^(k+A)
  have link := wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have dates : ∀ᶠ r in trail, a r * u r = radius z T r := by
    filter_upwards [link.positive] with r hp
    change (g r)^(k+A) * (r*(g r)⁻¹^A) = r*(g r)^k
    have gn : g r≠0 := hp.ne'
    rw [pow_add,inv_pow]
    field_simp
  have young : Tendsto (fun r=>a r*u r) trail trail :=
    (smaller F simple bliss T).congr' (dates.mono fun _ h=>h.symm)
  have old := longer F simple bliss A
  have member : ∀ᶠ r in trail, a r∈Set.Ioc (0:ℝ) 1 := by
    filter_upwards [link.positive,(link.conforms simple).eventually (ge_mem_nhds zero_lt_one)] with r hp hg
    exact ⟨pow_pos hp _,pow_le_one₀ hp.le hg⟩
  obtain ⟨W,wp,rent⟩ := WilsonThermometerUnitFilingFourPoolRent.converted F J Z simple lead paid d v old young member
  obtain ⟨C,cp,clock⟩ := WilsonThermometerUnitFilingFourPoolClock.invoice F simple bliss T
  refine ⟨C*W,mul_nonneg (zero_le_one.trans cp) wp,?_⟩
  filter_upwards [dates,member,rent 1 zero_lt_one,clock,link.positive] with r hs ha price bill hp
  rw [hs] at price
  have cancel : (a r)^(-(d:ℝ)-1) * (g r)^((k+A)*(d+1))=1 := by
    rw [show -(d:ℝ)-1= -((d+1:ℕ):ℝ) by push_cast; ring,Real.rpow_neg ha.1.le,Real.rpow_natCast,pow_mul]
    exact inv_mul_cancel₀ (pow_pos ha.1 _).ne'
  let s := radius z T r
  let dw := dock s^T
  let y := homogeneous F J Z (u r) d v
  have due : Ascent.cost F d s y * (g r)^((k+A)*(d+1)) ≤ W := by
    calc _ ≤ W*(a r)^(-(d:ℝ)-1) * (g r)^((k+A)*(d+1)) :=
              mul_le_mul_of_nonneg_right price (pow_nonneg hp.le _)
         _ = W := by rw [mul_assoc,cancel,mul_one]
  have d0 : 0≤dw*(g r)^(2*T) := mul_nonneg (pow_nonneg bill.1.le _) (pow_nonneg hp.le _)
  have c0 : 0≤Ascent.cost F d s y*(g r)^((k+A)*(d+1)) :=
    mul_nonneg (Ascent.cost_pos ..) (pow_nonneg hp.le _)
  change dw * Ascent.cost F d s y * (g r)^(2*T+(k+A)*(d+1)) ≤ C*W
  calc _ = (dw*(g r)^(2*T))*(Ascent.cost F d s y*(g r)^((k+A)*(d+1))) := by rw [pow_add]; ring
       _ ≤ _ := mul_le_mul bill.2 due c0 (zero_le_one.trans cp)

end YM.Integration.WilsonThermometerUnitFilingFourPoolBill
