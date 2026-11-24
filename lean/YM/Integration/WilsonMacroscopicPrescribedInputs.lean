import YM.Integration.WilsonReportPrescribedFrame
import YM.RG17.Balance
import YM.PhysMS.Foundation.Estimates

/-! The spatial price for the true moving position fields at fixed external
points. The graded input charges cancel their engineering dimensions before
one spends a small positive spatial margin on the running coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicPrescribedInputs
open Function Filter Finset Set MeasureTheory Extraction Table
open Next.Rank OPE OPE.Orbits RG12 RG17 SharpGram Climb PhysMS
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
  {T : Campaign R} (hG : G.Simple) (W : Campaign.Pillars R T)
  {b : ℝ} (source : FundedOriginalProperties.{u} hG b W)
  (pace : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (hB : 0 < B)
  (F : Spec.Final R.family f S) (fac : OPE.Facilities R.family f S)
  (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
  (J : ℝ → PhysMS.tower S) (leading : PhysMS.Leading F J) {K : (Bel R.family.book).Hierarchy}
  (paid : ∀ d : ℕ, ∀ᶠ r in Trace.Pilot.trail, PhysMS.Frame.obedient F K (J r) d)
  {I : Type} [Fintype I] (d : I → ℕ) (vs : (i : I) → RG17.Free R.family (d i))
include hG W source pace hB fac leading paid

omit [Fintype I] in

/-- This is the manuscript's engineering bound for the *prescribed* position
fields in the same reader. Each grade is charged at its own physical weight. -/
theorem grades : RG17.GradePrice Q d (fun r i => J r (d i) (vs i)) (fun _=>0) := by
  obtain ⟨u, mantle, L, _, pegs, _, _, buys, _⟩ :=
    WilsonReportPrescribedFrame.selected hG W source pace hB F fac J leading paid
  intro i j
  rw [add_zero]
  by_cases hj : j ≤ d i
  · exact (buys (d i)).test F (d i) fac.toServices (Pier.Lair.tender F L J)
      Q (vs i) pegs.level ⟨j,Nat.lt_succ_iff.mpr hj⟩
  · apply RateLE.congr (F:=fun _ : ℝ => (0 : S.Field j)) (RateLE.zero RG17.home OPE.run _)
    exact Eventually.of_forall fun r=>(Q.kills_lower j (d i) (Nat.lt_of_not_ge hj) _).symm

/-- Through **the requested horizon itself**, with arbitrary fixed macroscopic
spectators, every positive fraction of a spatial power pays all coupling
orders. The bound carries no sum of the input engineering weights. -/
theorem original {E : Type} [Fintype E] {e : E → ℕ} (w : Labels S e)
    {M η δ : ℝ} (hM : 0 ≤ M) (hη : 0 < η) (hδ : 0 < δ)
    {g : ℝ → ℝ} (hg : Trace.Pilot.Coupling G g) (H q : ℕ)
    {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) : ∀ᶠ r in Trace.Pilot.trail,
    ∀ (x : I → E4) (o : E4) (y : E → E4), WithinRoom r M η x o → ClearOf o y δ →
      ∀ t : Viewers F, ‖formula F Q x o (fun i=>J r (d i) (vs i)) y w H t‖ ≤
        ε*g r^q*r^((H : ℝ)+1-σ) := by
  have charged := grades hG W source pace hB F fac Q J leading paid d vs
  have tail := RG17.formulaCharged Q fac.toServices hM hη w H charged hδ (half_pos hσ)
  have tariff := PhysMS.subpower_payment hg hG 1 (σ/2) (half_pos hσ) ε hε q
  filter_upwards [tail, tariff, RG17.positiveLength] with r hr price pos
  intro x o y fits clear t
  have bound := hr x o y fits clear t
  simp only [Finset.sum_const_zero, sub_zero] at bound
  rw [one_mul] at price
  refine bound.trans ?_
  rw [show (H:ℝ)+1-σ/2=σ/2+((H:ℝ)+1-σ) by ring, Real.rpow_add pos]
  exact mul_le_mul_of_nonneg_right price (Real.rpow_nonneg pos.le _)

end YM.Integration.WilsonMacroscopicPrescribedInputs
