import YM.Integration.WilsonCenteredPositiveFiling

/-! The actual panel and its all-child-residue cutoff source for the original
ordinary OPE. The finite physical program and its booked cutoff use the same
field on every microscopic configuration. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredPhysicalPanel
open Function Set MeasureTheory Table Spec Extraction Lattice Trace Wilson Source PhysicalNext.Repeat.Legato
open RG Labels Finset Trace.Physical.GermGraph RG16 RG16.Literal RG12 Cells Push.GridApprox
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) {n : ℕ} (caps : Fin n → ℕ) (z : UVIndex)
abbrev Sites (n : ℕ) := Fin n → Site (R.family.side z.1 z.2)
variable (w : ∀j,R.family.label (caps j)) (weight : Sites R z n → ℂ)

def cylinder : Cut R.family z.1 z.2 :=
  WilsonCenteredProductBooking.source R (N:=z.1) (per:=z.2) (fun (_ : Sites R z n)=>caps)
    (fun _ => w) id (fun _=>univ) weight univ

theorem value : R.family.omega z.1 z.2 (cylinder R caps z w weight)=
    ∑u : Sites R z n,weight u*R.family.ensemble (N:=z.1) (p:=z.2) caps u w :=by
  let f (u:Sites R z n) (U:Config G (R.family.side z.1 z.2)) := ∏j,R.family.O z.1 z.2 (w j) (u j) U
  change (∫ U,∑u,weight u*f u U ∂law G (R.family.side z.1 z.2) (R.family.beta z.1 z.2))=_
  rw [integral_finsetSum]
  · apply sum_congr rfl
    intro u _
    rw [integral_const_mul]
    rfl
  · intro u _
    have h : Continuous (fun U=>weight u*f u U) := continuous_const.mul
      (continuous_finsetProd _ fun j _=>R.family.continuousO z.1 z.2 _ _ _)
    exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The canonical original book for this very panel at any positive output
horizon and every admitted reporting date. -/
theorem booked (simple : G.Simple) (out u : ℕ) (input : ∀j,R.t (caps j) ≤ z.1) (start : R.t out ≤ u) (stop : u ≤ z.1)
    (funded : WilsonCenteredCaptureClock.first R simple ≤ z.1)
    (opened : Opened R.family out u z.2) :
    Booked R.family z.1 z.2 out (cylinder R caps z w weight) u stop :=by
  obtain ⟨_,_,_,all⟩:=WilsonCenteredPositiveFiling.booked R simple
    (fun (_:Sites R z n)=>caps) (fun _=>w) id (fun _=>univ) weight univ out u (fun _ _=>input) start stop funded
  exact (all u le_rfl stop opened).1

end YM.Integration.WilsonCenteredPhysicalPanel
