import YM.Integration.WilsonOriginalObservedRoseGroundMenu
import YM.Integration.WilsonMaxwellThermometerKineticUpper

/-! The original kinetic bound pays a preselected independent ground before both original cutoffs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseKineticGround

open Filter Set Function Metric Lattice Wilson RG Source Extraction Table Spec Climb Trace.Pilot PhysMS
open OPE PhysicalNext PhysicalNext.Repeat FVA2.Register Pert.Asymptotics
open PhysicalNext.Repeat.Legato Maxwell XSpace XSpace.Cirrus XSpace.Normalize XSpace.Rose
open WilsonMaxwellThermometerCommonTangent (Equivariant)
open WilsonMaxwellThermometerFiniteTangent (credit cost roster)
open WilsonMaxwellThermometerOriginal (lower)
open scoped Topology Classical

variable {G:Gauge} (R:Run G) (simple:G.Simple) {B:ℕ} (hB:0<B)
    (pace:WilsonWindowReportingPace.Slow R.kit) (Z:WilsonPrescription G) {fine index:ℝ→ℕ}
    (schedule:WilsonOriginalPositionFineScheme.enrolled (R:=R) (hG:=simple) (B:=B) Z fine index)
local notation "Visit" => ℝ×(ℕ×ℕ)
local notation "g" => WilsonMaxwellThermometerKineticFineRose.axis (R:=R) fine
local notation "unit" => WilsonMaxwellThermometerKineticLog.unit G
variable {I:Type} [Fintype I] (basis:Module.Basis I ℂ (Sec G 6))

include hB pace schedule in
/-- The ground mesh depends on the prescribed cap and length.  All admissible input
triples and physical periods then use this one independent board. -/
theorem original (cap:ℝ→ℝ) (offered:ℝ→Set Mesh) (openings:∀r,offered r∈Front) :
    ∃m:ℝ→Mesh, (∀r,m r∈offered r) ∧
      ∀ᶠ r in trail,∀ N per, fine r≤N → ∀(u:Sec G 6)(P Q:Module.End ℂ (Sec G 4)),
        Equivariant P → Equivariant Q → cost basis (roster u (P (lower G)) (Q (lower G))) ≤ cap r →
        ‖credit Z.scheme Z.criterion (m r) u (P (lower G)) (Q (lower G)) / (g (r,N,per):ℂ)‖ ≤ 2*r := by
  obtain ⟨m,sold⟩:=WilsonOriginalObservedRoseGroundMenu.original Z.scheme Z.criterion basis simple cap
    (fun r=>r*unit r) offered openings
  refine ⟨m,fun r=>(sold r).1,?_⟩
  have kinetic:=WilsonMaxwellThermometerKineticUpper.original R simple hB pace Z schedule (show (0:ℝ)<1/2 by norm_num)
  filter_upwards [kinetic,self_mem_nhdsWithin (s:=Set.Ioi (0:ℝ))] with r prices rp
  intro N per ready u P Q p q cash
  have hp:0<r:=rp
  have pos:0<g (r,N,per):= inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson ready))
  have price:=abs_lt.mp (prices N per ready)
  change -(1/2:ℝ)<g (r,N,per)/unit r-1 ∧ g (r,N,per)/unit r-1<1/2 at price
  have ratio:0<g (r,N,per)/unit r:=by linarith [price.1]
  have hu:0<unit r:=(div_pos_iff.mp ratio).resolve_right (fun h=>pos.not_gt h.1) |>.2
  have bound:unit r ≤ 2*g (r,N,per) := by
    have low:(1/2:ℝ) < g (r,N,per)/unit r:=by linarith [price.1]
    linarith [(lt_div_iff₀ hu).mp low]
  have paid:=(sold r).2 (mul_pos hp hu) u P Q p q cash
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos pos]
  apply (div_le_iff₀ pos).mpr
  exact paid.trans ((mul_le_mul_of_nonneg_left bound hp.le).trans_eq (by ring))

end YM.Integration.WilsonOriginalObservedRoseKineticGround
