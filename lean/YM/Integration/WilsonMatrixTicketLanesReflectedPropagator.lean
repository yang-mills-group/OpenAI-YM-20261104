import YM.Integration.WilsonMatrixTicketLanesReflectedInner
import YM.Integration.WilsonMatrixTicketLanesReflectedWindow
import YM.Integration.WilsonMatrixTicketLanesMirrorClock

/-! The two finite-period inverse-Hessian estimates used by the registered reflected Gaussian. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReflectedPropagator
open Filter Lattice Gauge RG Tree Wilson FVA2 RGComparison.Core16 RGComparison.Core16.Descent
open RGComparison.Core16.Lumen RGComparison.Core16.Lumen.Planet RGComparison.Core16.Forge
open RGComparison.Core16.Parcel RGComparison.Core16.Parcel.Oven RGComparison.Core16.Spool RGComparison.Core16.Silk
open PhysicalNext.Repeat.Legato WilsonMatrixTicketLanesReflectedInner WilsonMatrixTicketLanesReportedPrepaid
open WilsonMatrixTicketLanesReflectedWindow Contacts.Lyre Contacts.Lyre.Align
open scoped Topology Classical
variable {G : Gauge} {c f : Side} (S : StepData c f)

theorem axis_reflected (even : Even f.val) (j : Wire G (Forestry S).Free) :
    axis S (Forestry S) j ∘ₗ (Both.lights G S even).t = -axis S (Forestry S) (Align.via S j.1,j.2) := by
  ext x; rfl

variable (R : Run G) (b : ℕ)
local notation "stepAt" p => R.family.path.levels.clock.op b p
local notation "forestAt" p => Forestry (stepAt p)

theorem sideEven (j p : ℕ) : Even (R.family.side j p).val :=
  (WilsonMatrixTicketLanesMirrorClock.segment R.family.path p j (WilsonMatrixTicketLanesMirrorClock.central R.family.path p) 0).even

def Entries : Prop := ∃ γ : ℝ,0<γ ∧ ∃ C : ℝ,0≤C ∧ ∀ p,∃ large : Bid.Larger (G:=G) (stepAt p),
  ∀ (T : Tree.Forest (stepAt p).ratio) (tag : (stepAt p).Choices) (i j : Wire G T.Free),
    |(law (stepAt p) T large tag ()).wick (axis (stepAt p) T i) (axis (stepAt p) T j)|≤
      C / Real.exp (γ*(Lattice.separation (Hut.pad T i.1) (Hut.pad T j.1):ℝ))

theorem original (paid : Paid G R.kit) : ∀ᶠ b : ℕ in atTop,Entries R b := by
  filter_upwards [WilsonMatrixTicketLanesReflectedWires.original R paid,WilsonMatrixTicketLanesMirrorClock.purchased R.family.path] with b booked allowed
  obtain ⟨P,X,offer,fees⟩:=booked
  obtain ⟨C,hC,fee⟩:=fees 0 1 1
  refine ⟨shade X,shade_pos,C,hC,?_⟩;intro p
  let S:=R.family.path.levels.clock.op b p
  have large : Bid.Larger (G:=G) S:=allowed p 1 0 (by decide)
  refine ⟨large,?_⟩;intro T tag i j
  have pin : ∀ k,‖(0:Directions G (R.family.side b p)) k‖≤X.Q := by simp [offer.good.thick.1.le]
  have price:= (fee p T 0 pin [i] [j] (le_refl 1) (le_refl 1)).2 0 (le_refl 0) (Lattice.separation (Hut.pad T i.1) (Hut.pad T j.1))
  rw [←WilsonMatrixTicketLanesReflectedInner.covariance S T X offer large tag () i j]
  apply price;intro x hx y hy;simp only [List.mem_singleton] at hx hy;rw [hx,hy]

def Mirror : Prop := ∃ γ : ℝ,0<γ ∧ ∃ C : ℝ,0≤C ∧ ∀ p,∃ large : Bid.Larger (G:=G) (stepAt p),
  ∀ a : Site (R.family.side (b+1) p),∃ q : Site (R.family.side b p),∀ (tag : (stepAt p).Choices)
    (i j : Wire G (forestAt p).Free) (h : ℕ),8*(h+h+1)≤(R.family.side (b+1) p).val→
    let center:=a+(stepAt p).ratio.embed q
    pdist (Hut.pad (forestAt p) i.1-center)≤h→pdist (Hut.pad (forestAt p) j.1-center)≤h→
    |(law (stepAt p) (forestAt p) large tag ()).wick (axis (stepAt p) (forestAt p) i)
      (axis (stepAt p) (forestAt p) j ∘ₗ (Both.lights G (stepAt p) (sideEven R (b+1) p)).t)|≤
      C / Real.exp (γ*(((R.family.side (b+1) p).val/8:ℕ):ℝ))

theorem reflected (paid : Paid G R.kit) : ∀ᶠ b : ℕ in atTop,Mirror R b := by
  filter_upwards [WilsonMatrixTicketLanesReflectedWindow.original R paid,WilsonMatrixTicketLanesMirrorClock.purchased R.family.path] with b booked allowed
  obtain ⟨P,X,offer,fees⟩:=booked
  obtain ⟨C,hC,fee⟩:=fees 0 1 1
  refine ⟨shade X,shade_pos,C,hC,?_⟩;intro p
  let S:=R.family.path.levels.clock.op b p
  have large : Bid.Larger (G:=G) S:=allowed p 1 0 (by decide)
  refine ⟨large,?_⟩;intro a
  obtain ⟨q,hq⟩:=fee p a
  refine ⟨q,?_⟩;intro tag i j h clearance center hi hj
  have pin : ∀ k,‖(0:Directions G (R.family.side b p)) k‖≤X.Q := by simp [offer.good.thick.1.le]
  have bound:= (hq 0 pin [i] [j] (le_refl 1) (le_refl 1) h clearance (by simpa [WilsonMatrixTicketLanesReflectedWindow.inside] using hi) (by simpa [WilsonMatrixTicketLanesReflectedWindow.inside] using hj)).2 0 (le_refl 0)
  rw [axis_reflected];change |-((law S (Forestry S) large tag ()).wick (axis S (Forestry S) i) (axis S (Forestry S) (Align.via S j.1,j.2)))|≤_
  rw [abs_neg,←WilsonMatrixTicketLanesReflectedInner.covariance S (Forestry S) X offer large tag () i (Align.via S j.1,j.2)]
  exact bound

end YM.Integration.WilsonMatrixTicketLanesReflectedPropagator
