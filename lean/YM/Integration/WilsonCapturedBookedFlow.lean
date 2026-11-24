import YM.Integration.WilsonCapturedReturnedCrossing
import YM.RG16.Unmasked.Report

/-! The normalized credit of the very same original cutoff function
has exact physical evolution, with zero genuine foreground. The
extension past N is never read in the physical return. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedBookedFlow
open Function Filter Lattice RG Wilson Labels Source PhysicalNext.Repeat.Legato
open Trace.Physical Trace.Physical.GermGraph Work.G08 RG16 RG16.Literal
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) (d N p : ℕ)

def field (Y : Cut R.family N p) : Er R.family p :=
  fun i => if h : i ≤ N then credit R.family N p d Y i h else 0

theorem onCut (Y : Cut R.family N p) {i : ℕ} (stop : i ≤ N) :
    field R d N p Y i = credit R.family N p d Y i stop := by
  simp only [field,dif_pos stop]

private theorem noForce (i : ℕ) (op : Opened R.family d i p) (stop : i ≤ N) :
    Foreground R.family d N p i 0 0 := by
  let q := (R.family.factory d N p).entries i 0
  let matrix := fitting d N p i R.makes op stop
  have cost0 : (R.family.labels.level d).coeffSize (matrix 0) = 0 := by
    rw [matrix.map_zero]
    exact Finset.sum_eq_zero fun _ _ => (norm_zero : ‖(0 : ℂ)‖ = 0)
  have physical := graph_cost d N p i R.makes op stop 0
  change reads (C:=R.family) d N p i q (2*stock R.family i*(R.family.labels.level d).coeffSize (matrix 0)) at physical
  rw [cost0,mul_zero] at physical
  have head := (size_gap d N p i R.makes op stop 0).2
  change (R.family.labels.level d).coeffSize q.x ≤ 2*(R.family.labels.level d).coeffSize (matrix 0) at head
  rw [cost0,mul_zero] at head
  exact ⟨0,q,le_rfl,physical,head,zero_cal d N p i R.makes op.post stop,by simp⟩

/-- All actual cutoff/forest history on any interval of admitted
physical scales contributes *zero* extra source once the complete
same cutoff Y is held. No independent trajectory assumption. -/
theorem retained (Y : Cut R.family N p) (continuous : Continuous Y) {u b : ℕ}
    (stop : b ≤ N) (admitted : ∀ j ≥ u, Opened R.family d j p) :
    ∀ i ≥ u, i<b → Foreground R.family d N p i ((0 : Er R.family p) i) 0 ∧
      field R d N p Y i = transition (C:=R.family) d N p i (field R d N p Y (i+1)) +
        (0 : Er R.family p) i := by
  intro i ui ib
  have iN : i<N := ib.trans_le stop
  refine ⟨noForce R d N p i (admitted i ui) iN.le,?_⟩
  rw [onCut R d N p Y iN.le,onCut R d N p Y iN]
  exact (credit_step R.family N p d Y continuous iN).trans (add_zero _).symm

end YM.Integration.WilsonCapturedBookedFlow
end
