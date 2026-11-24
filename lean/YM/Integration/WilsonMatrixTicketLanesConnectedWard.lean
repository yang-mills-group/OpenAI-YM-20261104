import YM.Integration.WilsonMatrixTicketLanesConnectedSigned
import YM.Integration.WilsonMatrixTicketLanesReportedAdmission
import YM.Integration.WilsonGaussianProbeMatrix

/-! The two *already selected* nonzero Ward row fields pay the entire fresh connected physical block. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesConnectedWard
open Filter Function Set Finset MeasureTheory Lattice Wilson RG Tree Precision RG17 Source Marker Extraction Extraction.Order Spec
open Table Climb Maxwell Maxwell.Free Trace.Pilot Trace.Over Spin PhysMS OPE OPE.Therm Next.UVStress Next.Rank.Price
open PhysicalNext.Repeat.Legato SharpGram.Lenses FVA2 FVA2.Register Pert.Asymptotics
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMatrixTicketLanesSmearedRows
open WilsonInvariantActionPairProbe WilsonInvariantActionSpectatorPrices WilsonInvariantActionCalibratedColumn
open Trace.Sundial WilsonLimitConstruction WilsonMatrixOriginalEarlierPanel
open WilsonInvariantActionPairCovariance
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book} (F:Final R.family f S)
  (J:ℝ→tower S) (Z:WilsonPrescription G) {H:(Bel R.family.book).Hierarchy} (L:Layout F)
  {U:Filter (ℕ×ℕ)}
local notation "β" => R.family.path.levels.clock.hatBeta

theorem on_row (simple:G.Simple) (connected:WilsonMatrixTicketLanesConnectedBudget.Paid G R.kit)
    (pace:WilsonWindowReportingPace.Slow R.kit) (lead:Leading F J) (obey:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d)
    (chosen:U ≤ L.lens) {B:ℕ} (wide:17 ≤ B) (level:L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B)
    {δ g:ℝ→ℝ} (coupling:Coupling G g) (D:Profiles R 4) (j:D.probes.index) (v₀:(standard R.family.labels).Ref 4)
    (hs:D.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 v₀) (e:ℕ)
    (deposit:ℝ→RG17.Free R.family 4→R.family.label 4) (χ:ℂ→L[ℝ]ℝ) (σ:ℝ)
    (record:Row (H:=H) (U:=U) F J Z L δ g D j v₀ hs e deposit χ σ):
    let φ:=WilsonInvariantActionCalibratedColumn.packet v₀ hs (test D j)
    let v:=(Bel R.family.book).project 4 v₀
    let a:=fun r=>deposit r (stepField R.family)
    let b:=fun r=>deposit r (freeInput F J Z 4 r v)
    WilsonMatrixTicketLanesConnectedSigned.Negligible R F L U 4 4 g a b φ := by
  let α:=stepField R.family
  let v:=(Bel R.family.book).project 4 v₀
  let E:=‖v‖+1
  have Ep:0 ≤ E:=by dsimp only [E];positivity
  have bounded:∀ᶠr in trail,‖freeInput F J Z 4 r v‖ ≤ E:=
    (WilsonOriginalCompensatedAnchor.field F J Z lead obey simple 4 v).norm.eventually (ge_mem_nhds (by dsimp only [E];linarith))
  have grows:Tendsto L.level trail atTop:=by rw [level];exact WilsonMeasuredWindow.stop_tendsto _ simple B (by omega)
  obtain ⟨_,_,_,_,_,_,_,market,_⟩:=record
  have billing:∀ᶠr in trail,∀w:RG17.Free R.family 4,
      RG12.mass R.family 4 (L.shift 4 r (deposit r w)) ≤ β (L.level r)^e*‖w‖:=by
    filter_upwards [market,grows.eventually_ge_atTop (R.family.ref 4)] with r sold mature
    intro w
    have receipt:=(sold w).2 (L.level r) 0 le_rfl
    rw [WilsonMatrixTicketLanesReportedAdmission.quota R F L 4 r (deposit r w) mature _ _ le_rfl] at receipt
    exact (mul_le_mul_iff_right₀ (pow_pos (R.family.S.a_pos _) 4)).mp receipt
  apply WilsonMatrixTicketLanesConnectedSigned.purchased R F L simple connected pace wide level chosen 4 4 g coupling _ _ _ e e ‖α‖ E (norm_nonneg _) Ep
  · filter_upwards [billing] with r paid
    exact (paid α).trans_eq (mul_comm ..)
  · filter_upwards [billing,bounded] with r paid bound
    have beta:0 ≤ β (L.level r):=(zero_lt_one.trans (R.family.path.levels.fits.delayed _)).le
    exact (paid (freeInput F J Z 4 r v)).trans ((mul_le_mul_of_nonneg_left bound (pow_nonneg beta _)).trans_eq (mul_comm ..))

end YM.Integration.WilsonMatrixTicketLanesConnectedWard
