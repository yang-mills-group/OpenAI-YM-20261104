import YM.Integration.WilsonMatrixTicketLanesReportedAccuracy
import YM.Integration.WilsonMatrixTicketLanesReportedCoupon
import YM.Integration.WilsonReportingMeasuredAdmission

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReportedReturn
open Function Filter Set Real FVA2 FVA2.CityHistory Lattice RG Wilson Tree Precision RG17 RG12 Extraction Spec
open OPE Table SharpGram.Lenses Pier.Lair OPE.Orbits Climb Ward PhysMS Trace.Pilot SharpGram
open RGComparison.Core16 RGComparison.Core16.Spool PertExtension.Series.Tested PhysicalNext.Repeat.Legato
open WilsonMatrixTicketLanesReportedOneBlock WilsonMatrixTicketLanesReportedPrepaid
open WilsonMatrixTicketLanesReportedSettlement Pert.Asymptotics
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) {f : Extraction.Order} {S : Table R.family.book}
  (F : Spec.Final R.family f S) (L : RG17.Layout F)
local notation "β" => R.family.path.levels.clock.hatBeta

/-- A single true finite posterior and the independently issued Taylor polynomials
of all its original marked words, with their own unaltered signed weights. -/
def Compared (r : ℝ) {n : ℕ} (d : Fin n → ℕ) (w : ∀i,R.family.label (d i))
    (x : ∀i,RG17.Free R.family (d i)) (s q cap : ℕ) (ε : ℝ) : Prop :=
  ∀ (b : ℕ) (elected : L.level r=b+1) (N p : ℕ),L.level r ≤ N →
    ∀ (large : Bid.Larger (G:=G) (step R p elected)) (T : Forest (step R p elected).ratio)
      (u : Pins G (R.family.side b p)) (o : Fin n → Site (R.family.side (L.level r) p))
      (tag : (step R p elected).Choices) (v : (Descent.nil (top:=R.family.side (L.level r) p)).Tags),
      (∀ k,‖u k‖ ≤ (cap:ℝ)+1) →
      ‖fresh R F L r d w b N p elected u o -
        priced R F L r d w N p (WilsonMatrixTicketLanesReportedCoupon.value R (N:=N) d s elected large T u o tag v)‖ ≤
        ε * regulatorRun R.family N p (L.level r)^q * ∏ i,‖x i‖

private theorem total {n : ℕ} (d : Fin n → ℕ) (e : Fin n → ℕ) (r : ℝ)
    (w : ∀i,R.family.label (d i)) (x : ∀i,RG17.Free R.family (d i))
    (charged : ∀i,mass R.family (d i) (L.shift (d i) r (w i)) ≤ β (L.level r)^(e i)*‖x i‖) :
    ∏ i, (2:ℝ)^(d i)*mass R.family (d i) (L.shift (d i) r (w i)) ≤
      ((∏ i,(2:ℝ)^(d i))*β (L.level r)^(∑ i,e i)) * ∏ i,‖x i‖ := by
  calc
    _ ≤ ∏ i,(2:ℝ)^(d i)*(β (L.level r)^(e i)*‖x i‖) := by
      exact Finset.prod_le_prod
        (fun _ _ => mul_nonneg (by positivity) (mass_nonneg ..))
        (fun i _ => mul_le_mul_of_nonneg_left (charged i) (by positivity))
    _ = _ := by simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, mul_assoc]

variable (J : ℝ → PhysMS.tower S) (lead : PhysMS.Leading F J)
  {K : (Bel R.family.book).Hierarchy}
  (aligned : ∀ d : ℕ, ∀ᶠ r in trail, AlignO F.sector F.room.kernel.spin K d (J r d))
  {U : Filter (ℕ×ℕ)} (B : Mantle F U) (E : Services R.family f S) (pegs : Pegs B L)
  (near : ∀ᶠ r in trail, R.family.S.a (L.level r) ≤ r ∧ r ≤ R.family.S.a (L.level r)*R.family.path.levels.clock.hatBeta (L.level r)^2)

include lead aligned E pegs near in
/-- Quantitative comparison on the measured physical fields. The exponents precede
every order and radius. The filed fields are chosen before all future cutoffs,
periods, forests and positions and realize the very same measured frame. -/
theorem original (simple : G.Simple) (paid : Paid G R.kit) {n : ℕ} (d : Fin n → ℕ) :
    ∃ e : Fin n → ℕ,∀ q cap (ε : ℝ),0 < ε → ∀ᶠ r in trail,
      ∀ x : ∀i,RG17.Free R.family (d i),∃ w : ∀i,R.family.label (d i),
        (∀i,master L (d i) r (w i) = J r (d i) (x i) ∧
          mass R.family (d i) (L.shift (d i) r (w i)) ≤ β (L.level r)^(e i)*‖x i‖) ∧
        Compared R F L r d w x (q+2*((∑ i,e i)+1)) q cap ε := by
  choose e receipts using fun i=>WilsonReportingMeasuredTender.entry B E
    (WilsonReportingMeasuredAdmission.present F J lead aligned) pegs near (d i)
  refine ⟨e,?_⟩
  intro q cap ε positive
  let A := ∏i,(2:ℝ)^(d i)
  let h := ∑i,e i
  have grows := pegs.level.growing
  have previous : Tendsto (fun r=> L.level r-1) trail atTop := tendsto_atTop.2 (fun b =>
    (grows.eventually_ge_atTop (b+1)).mono fun r arriving=>by omega)
  have allAges := eventually_all.mpr (fun i=>grows.eventually_ge_atTop (R.family.ref (d i)))
  have pricedRows := previous.eventually (WilsonMatrixTicketLanesReportedCoupon.original R simple paid d (q+2*(h+1)) cap)
  have paidRates := grows.eventually (WilsonMatrixTicketLanesReportedAccuracy.coupon R simple q h A ε
    (Finset.prod_nonneg fun _ _=>by positivity) positive)
  filter_upwards [eventually_all.mpr receipts,allAges,pricedRows,paidRates] with r available ages rows costs
  intro x
  choose w dollars fields using fun i=>available i (x i)
  refine ⟨w,fun i=>⟨fields i,dollars i⟩,?_⟩
  intro b elected N p future large T u o tag v inside
  have pred : L.level r-1=b := by omega
  rw [pred] at rows
  let g := regulatorRun R.family N p (L.level r)
  let fee := g^(q+2*(h+1)+1)*(2+Real.log (β b))
  have feePos : 0 ≤ fee := mul_nonneg (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)
    (add_nonneg zero_le_two (Real.log_nonneg (R.family.path.levels.fits.delayed b).le))
  have dec := costs b N p (by omega) future
  calc
    _ ≤ (∏ i,(2:ℝ)^(d i)*mass R.family (d i) (L.shift (d i) r (w i)))*fee :=
      rows F L r elected w ages N p future large T u o tag v inside
    _ ≤ (A*β (L.level r)^h * (∏ i,‖x i‖))*fee :=
      mul_le_mul_of_nonneg_right (total R F L d e r w x dollars) feePos
    _ = (A*β (L.level r)^h*fee)*(∏i,‖x i‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right dec (Finset.prod_nonneg fun _ _=>norm_nonneg _)

end YM.Integration.WilsonMatrixTicketLanesReportedReturn
