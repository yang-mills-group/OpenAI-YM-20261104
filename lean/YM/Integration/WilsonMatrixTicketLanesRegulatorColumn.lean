import YM.Integration.WilsonMatrixTicketLanesReportedCoupon
import YM.Integration.WilsonMatrixTicketLanesReportedAdmission

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesRegulatorColumn
open Filter Real FVA2 FVA2.CityHistory Lattice RG Wilson Tree Precision RG17 RG12 Extraction Spec
open RGComparison.Core16 RGComparison.Core16.Spool PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonMatrixTicketLanesReportedPivot WilsonMatrixTicketLanesReportedOneBlock
open WilsonMatrixTicketLanesReportedPrepaid
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) {f : Extraction.Order} {S : Table R.family.book}
  (F : Spec.Final R.family f S) (L : RG17.Layout F)

/-- The literal head of the upper operator's registered entry at the intervening
date, in engineering-normalized coordinates. -/
def entry (d k N p : ℕ) (x : R.family.label d) : R.family.label d :=
  (↑(R.family.S.a k^d):ℂ)⁻¹ •
    ((R.family.factory d N p).entries k ((R.family.factory d N p).terminal.symm x)).x

/-- Reindex just the fixed-date coordinates in the bare one-block calculation.
The original chart, observation and cutoff filter are kept pointwise. -/
def dated (k : ℕ) : RG17.Layout F :=
  { L with level := fun _=>k, shift := fun _ _=>LinearEquiv.refl ℂ _ }

theorem attached (d k N p : ℕ) (age : R.family.ref d ≤ k) (future : k ≤ N) (x : R.family.label d) :
    RG17.atRef (dated R F L k) d 0 (N,p) (entry R d k N p x) = x := by
  let A := RG12.charts R.family F.room.cutoff d k (N,p)
  let X := (R.family.factory d N p).entries k ((R.family.factory d N p).terminal.symm x)
  have row : A x = X.x := by
    unfold A
    rw [RG12.charts,dif_pos ⟨age,future⟩]
    rfl
  apply A.injective
  change A ((↑(R.family.S.a k^d):ℂ) • A.symm ((↑(R.family.S.a k^d):ℂ)⁻¹ • X.x)) = A x
  rw [map_smul,LinearEquiv.apply_symm_apply,smul_smul,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (pow_ne_zero d (R.family.S.a_pos k).ne')),one_smul,row]

include L in
theorem cost (d k N p : ℕ) (age : R.family.ref d ≤ k) (future : k ≤ N) (x : R.family.label d) :
    mass R.family d (entry R d k N p x) =
      (R.family.S.a k^d)⁻¹ * Next.UVStress.quota R.family d k N p x := by
  have bill := WilsonMatrixTicketLanesReportedAdmission.quota R F (dated R F L k) d 0
    (entry R d k N p x) age N p future
  rw [attached R F L d k N p age future] at bill
  change Next.UVStress.quota R.family d k N p x = R.family.S.a k^d*mass R.family d (entry R d k N p x) at bill
  rw [bill,←mul_assoc,inv_mul_cancel₀ (pow_ne_zero d (R.family.S.a_pos k).ne'),one_mul]

include L in
/-- The whole printed nonlinear field at the authentic later date for the original
upper label, pointwise on every group configuration before all integrations. -/
theorem physical (d k N p : ℕ) (age : R.family.ref d ≤ k) (future : k ≤ N) (x : R.family.label d)
    (o : Site (R.family.side k p)) (U : Config G (R.family.side k p)) :
    R.family.O k p (center R k N p x) o U = ∑j,
      (R.family.labels.level d).scaled (R.family.path.levels.clock.threshold k)⁻¹ (entry R d k N p x) j *
        Light (WilsonCoherentTerminalFrame.lamp R d j) (R.family.side k p) o U := by
  have row := WilsonMatrixTicketLanesReportedPlating.measured R F (dated R F L k) d 0
    (entry R d k N p x) N p age future o U
  rw [attached R F L d k N p age future] at row
  exact row

end YM.Integration.WilsonMatrixTicketLanesRegulatorColumn
