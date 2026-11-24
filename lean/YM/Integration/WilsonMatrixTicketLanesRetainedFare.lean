import YM.Integration.WilsonMatrixTicketLanesRegulatorReturn
import YM.Integration.WilsonMatrixTicketLanesRetainedBid
import YM.Integration.WilsonMatrixTicketLanesReportedTransport
import YM.Integration.WilsonReportingMeasuredAdmission

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesRetainedFare
open Filter Real FVA2 FVA2.CityHistory Lattice RG Wilson Tree Precision RG17 RG12 Extraction Spec
open OPE Table SharpGram.Lenses Pier.Lair OPE.Orbits Climb Ward PhysMS Trace.Pilot SharpGram
open RGComparison.Core16 RGComparison.Core16.Spool PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonMatrixTicketLanesReportedOneBlock WilsonMatrixTicketLanesReportedPrepaid
open WilsonMatrixTicketLanesRegulatorCoupon
open WilsonMatrixTicketLanesDescentWords WilsonCoherentJointReturn PertExtension
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) {f : Extraction.Order} {S : Table R.family.book}
  (F : Spec.Final R.family f S) (L : RG17.Layout F)

/-- Numerical expansion with the genuine retained finite-torus signed Wick term displayed. -/
def reading {n m b N p : ℕ} (d : Fin n→ℕ) (s : ℕ) (elected : m=b+1)
    (large : Bid.Larger (G:=G) (step R p elected)) (T : Forest (step R p elected).ratio)
    (u : Pins G (R.family.side b p)) (o : Fin n→Site (R.family.side m p))
    (tag : (step R p elected).Choices) (v : (Descent.nil (top:=R.family.side m p)).Tags)
    (j : ∀ i,(R.family.labels.level (d i)).Index) : ℂ :=
  let A:=WilsonMatrixTicketLanesRetainedBid.value R d j (step R p elected) T o large tag v u
  (∑ z∈Finset.range s,regulatorRun R.family N p m^(z+1) •
    WilsonCoherentJointReturn.series (lamps R d j) (step R p elected) T R.metals.O u o large tag v (z+1))+
    ⟨A false,A true⟩

theorem identified {n m b N p : ℕ} (d : Fin n→ℕ) (s : ℕ) (elected : m=b+1)
    (large : Bid.Larger (G:=G) (step R p elected)) (T : Forest (step R p elected).ratio)
    (u : Pins G (R.family.side b p)) (o : Fin n→Site (R.family.side m p))
    (tag : (step R p elected).Choices) (v : (Descent.nil (top:=R.family.side m p)).Tags) :
    WilsonMatrixTicketLanesReportedCoupon.value R (N:=N) d s elected large T u o tag v=
       reading R (N:=N) d s elected large T u o tag v := by
  funext j
  unfold WilsonMatrixTicketLanesReportedCoupon.value reading
  change (∑i∈Finset.range (s+1),regulatorRun R.family N p m^i •
    WilsonCoherentJointReturn.series (lamps R d j) (step R p elected) T R.metals.O u o large tag v i)=_
  rw [Finset.sum_range_succ',pow_zero,one_smul,WilsonMatrixTicketLanesRetainedBid.series]

variable (E : Services R.family f S)
variable (J : ℝ → PhysMS.tower S) (lead : PhysMS.Leading F J)
  {K : (Bel R.family.book).Hierarchy}
  (aligned : ∀ d : ℕ,∀ᶠ r in trail,AlignO F.sector F.room.kernel.spin K d (J r d))
  {U : Filter (ℕ×ℕ)} (B : Mantle F U) (pegs : Pegs B L)
  (near : ∀ᶠ r in trail,R.family.S.a (L.level r)≤r ∧
    r≤R.family.S.a (L.level r)*R.family.path.levels.clock.hatBeta (L.level r)^2)

include lead aligned E pegs near in
/-- The genuinely retained original Wilson response sees the complete signed deposited stencil
on its actual finite-torus Gaussian, with its true retained-color means and all higher deposited orders. -/
theorem original (simple : G.Simple) (paid : Paid G R.kit) {n : ℕ} (d : Fin n→ℕ) :
    ∃ e : Fin n→ℕ,∀ (H q cap : ℕ) (ε : ℝ),0<ε → ∀ᶠ r in trail,
      ∀ x : ∀i,RG17.Free R.family (d i),∃ w : ∀i,R.family.label (d i),
        (∀i,master L (d i) r (w i)=J r (d i) (x i) ∧
          mass R.family (d i) (L.shift (d i) r (w i)) ≤
            R.family.path.levels.clock.hatBeta (L.level r)^(e i)*‖x i‖) ∧
        ∀ (b k : ℕ) (stage : k=b+1),L.level r≤k →
          R.family.S.a (L.level r)/R.family.S.a k ≤ R.family.path.levels.clock.hatBeta k^H →
          ∀ (N p : ℕ),k≤N →
          ∀ (large : Bid.Larger (G:=G) (step R p stage)) (T : Forest (step R p stage).ratio)
            (u : Pins G (R.family.side b p)) (o : Fin n → Site (R.family.side k p))
            (tag : (step R p stage).Choices) (v : (Descent.nil (top:=R.family.side k p)).Tags),
            (∀j,‖u j‖≤(cap:ℝ)+1) →
            let top := fun i=>atRef L (d i) r (N,p) (w i)
            ‖fresh R d N p top stage u o - WilsonMatrixTicketLanesRegulatorCoupon.forecast R (k:=k) d N p top
              (reading R (N:=N) d
                (q+2*((∑i,(e i+H*(d i+1)))+1)) stage large T u o tag v)‖ ≤
              ε*regulatorRun R.family N p k^q*∏i,‖x i‖ := by
  simpa only [←identified] using WilsonMatrixTicketLanesRegulatorReturn.original R F L E J lead aligned B pegs near simple paid d

end YM.Integration.WilsonMatrixTicketLanesRetainedFare
