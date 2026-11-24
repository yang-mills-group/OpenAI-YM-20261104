import YM.Integration.WilsonMatrixTicketLanesRegulatorCoupon
import YM.Integration.WilsonMatrixTicketLanesReportedTransport
import YM.Integration.WilsonReportingMeasuredAdmission

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesRegulatorReturn
open Filter Real FVA2 FVA2.CityHistory Lattice RG Wilson Tree Precision RG17 RG12 Extraction Spec
open OPE Table SharpGram.Lenses Pier.Lair OPE.Orbits Climb Ward PhysMS Trace.Pilot SharpGram
open RGComparison.Core16 RGComparison.Core16.Spool PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonMatrixTicketLanesReportedOneBlock WilsonMatrixTicketLanesReportedPrepaid
open WilsonMatrixTicketLanesRegulatorCoupon
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) {f : Extraction.Order} {S : Table R.family.book}
  (F : Spec.Final R.family f S) (L : RG17.Layout F)

variable (E : Services R.family f S)
include E in
/-- The genuine fixed-date deposit also pays the charge of its own unchanged
upper label at a finer intermediate date, with one explicit rate adjustment. -/
theorem charge (simple : G.Simple) (d h H : ℕ) (r : ℝ) (w : R.family.label d) (amount : ℝ)
    (nonneg : 0≤amount) (recd : mass R.family d (L.shift d r w) ≤
      R.family.path.levels.clock.hatBeta (L.level r)^h*amount)
    (k N p : ℕ) (age : R.family.ref d≤L.level r) (after : L.level r≤k) (future : k≤N)
    (room : R.family.S.a (L.level r)/R.family.S.a k ≤ R.family.path.levels.clock.hatBeta k^H) :
    (R.family.S.a k^d)⁻¹*Next.UVStress.quota R.family d k N p (atRef L d r (N,p) w) ≤
      R.family.path.levels.clock.hatBeta k^(h+H*(d+1))*amount := by
  let B := R.family.path.levels.clock.hatBeta
  have bp (i) : 0≤B i := zero_le_one.trans (R.family.path.levels.fits.delayed i).le
  have mono : B (L.level r)≤B k :=
    WilsonStartup.Timing.hat_mono R.family.path.levels (Gauge.slopeConstant_pos simple).le after
  have cash := WilsonMatrixTicketLanesReportedTransport.later R F L E d r w k N p age after future
  rw [div_eq_mul_inv,mul_comm] at cash
  calc
    _ ≤ _ := cash
    _ ≤ (B k^H)^(d+1)*(B k^h*amount) :=
      mul_le_mul (pow_le_pow_left₀ (div_nonneg (R.family.S.a_pos _).le (R.family.S.a_pos _).le) room _)
        (recd.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (bp _) mono _) nonneg))
        (mass_nonneg ..) (pow_nonneg (pow_nonneg (bp _) _) _)
    _ = _ := by rw [←pow_mul,pow_add]; ring

variable (J : ℝ → PhysMS.tower S) (lead : PhysMS.Leading F J)
  {K : (Bel R.family.book).Hierarchy}
  (aligned : ∀ d : ℕ,∀ᶠ r in trail,AlignO F.sector F.room.kernel.spin K d (J r d))
  {U : Filter (ℕ×ℕ)} (B : Mantle F U) (pegs : Pegs B L)
  (near : ∀ᶠ r in trail,R.family.S.a (L.level r)≤r ∧
    r≤R.family.S.a (L.level r)*R.family.path.levels.clock.hatBeta (L.level r)^2)

include lead aligned E pegs near in
/-- The same measured upper fields work at every sufficiently fine reporting date
in the physically permitted range. The original filed Maxwell vectors and their
upper operators are chosen before every such date, period, and cutoff. -/
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
              (WilsonMatrixTicketLanesReportedCoupon.value R (N:=N) d
                (q+2*((∑i,(e i+H*(d i+1)))+1)) stage large T u o tag v)‖ ≤
              ε*regulatorRun R.family N p k^q*∏i,‖x i‖ := by
  choose e dates using fun i=>WilsonReportingMeasuredTender.entry B E
    (WilsonReportingMeasuredAdmission.present F J lead aligned) pegs near (d i)
  refine ⟨e,?_⟩
  intro H q cap ε positive
  let rate i := e i+H*(d i+1)
  obtain ⟨b₀,blocks⟩ := eventually_atTop.1 (billed R F L simple paid d rate q cap ε positive)
  have grows := pegs.level.growing
  have ages := eventually_all.mpr fun i=>grows.eventually_ge_atTop (R.family.ref (d i))
  filter_upwards [eventually_all.mpr dates,ages,grows.eventually_ge_atTop (b₀+1)] with r received ready late
  intro x
  choose w accounts fields using fun i=>received i (x i)
  refine ⟨w,fun i=>⟨fields i,accounts i⟩,?_⟩
  intro b k stage after room N p future large T u o tag v inside
  exact blocks b (by omega) k N p stage future (fun i=>(ready i).trans after) _ (fun i=>‖x i‖)
    (fun i=>charge R F L E simple (d i) (e i) H r (w i) ‖x i‖ (norm_nonneg _) (accounts i)
      k N p (ready i) after future room) (fun i=>norm_nonneg _) large T u o tag v inside

end YM.Integration.WilsonMatrixTicketLanesRegulatorReturn
