import YM.Integration.WilsonReflectedPhysicalCounterterm
import YM.Integration.IntrinsicProductLinearity
import YM.OPE.Cards.Literal

/-! Rescaling the same finite physical numerator rescales its actual
fixed-date field under the native intrinsic filing. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryScaledCounter
open Filter Lattice Wilson RG Source Labels Extra.Histories PhysicalNext.Repeat.Legato
open MergeProof Accent Trace.Physical.GermGraph Trace.Physical Cells RG16 RG16.Literal
open OPE.Cards
open scoped BigOperators Classical
variable {G : Gauge} (R : Run G) {N p u J h : ℕ}

def difference (door : Opened R.family h u p) (live : u ≤ N) (Y : Cut R.family N p) :=
  Y - R.family.O N p (WilsonMacroscopicRichChildRegistration.returned R.family R.makes door live Y) 0

theorem original (door : Opened R.family h u p) (live : u ≤ N) (Y : Cut R.family N p)
    (cont : Continuous Y) (booked : Booked R.family N p h Y u live) (c : ℂ) {fee : ℝ}
    (paid : PaidAt R.family.S N p J (R.family.beta N p) fee (difference R door live Y)) :
    Booked R.family N p h (c • Y) u live ∧
      PaidAt R.family.S N p J (R.family.beta N p) (‖c‖ * fee) (difference R door live (c • Y)) := by
  have bank := IntrinsicProductLinearity.booked_sum R.family N p h u R.makes door live
    (fun _ : Unit => c) (fun _ => Y) (fun _ => cont) (fun _ => booked)
  simp only [Finset.univ_unique, Finset.sum_singleton] at bank
  have filed : difference R door live (c • Y) = c • difference R door live Y := by
    unfold difference WilsonMacroscopicRichChildRegistration.returned
    rw [bank.2, map_smul, (R.family.linearO N p h 0).map_smul, smul_sub]
  refine ⟨bank.1, ?_⟩
  rw [filed]
  exact ⟨paid.live, paid.ticket.scale _, (Next.UVStress.root_smul ..).le.trans
    (mul_le_mul_of_nonneg_left paid.mark (norm_nonneg c))⟩

end YM.Integration.WilsonCapturedPrimaryScaledCounter
