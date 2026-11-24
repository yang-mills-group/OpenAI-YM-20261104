import YM.Integration.WilsonMaxwellThermometerFirstPosition
import YM.Integration.WilsonPositionThermometerSevenFaceRate

/-! The sole signed physical comparison left by the first two formal position
coefficients, on one original three-field cutoff and its own reporting currency. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerFirstInvoice
open Function Filter Set Metric Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS Climb Maxwell XSpace XSpace.Normalize
open WilsonPositionThermometerCapStation WilsonPositionCapTransport
open scoped Topology

variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → tower S) {V : Store G}
    {Y : Ultrafilter (ℕ × ℕ)} {H : (Bel R.family.book).Hierarchy}
    {arch : Trace.Terrace.Arch R.family} (A : ℝ → Group R.family 6)
    (K : Rose.Pick V) (W : Initialize G) (simple : G.Simple) (B : ℕ)
local notation "P" => WilsonPositionPrescribedFrame.positioned F J V
local notation "out" => WilsonPositionGradedThermometerHearing.offer F J V K A
local notation "c" => Rose.c_T K
local notation "first" => WilsonMaxwellThermometerFirstPosition.coefficient F J A K W simple B

/-- The wound negative first coefficient after removing the true physical regulators
at fixed reporting radius. -/
def deposited (Y : Ultrafilter (ℕ × ℕ)) (r : ℝ) : ℝ :=
  limUnder (Y : Filter _) (fun z => (first r z).re)

theorem removed (hB : 0<B) (prior : (Y : Filter _)≤f.fuse)
    (book : Book (f:=f) (l:=Y) (H:=H) A J) (lead : Leading F J) :
    (∀ᶠ r in trail, Tendsto (fun z => (first r z).re) (Y : Filter _)
      (𝓝 (deposited F J A K W simple B Y r))) ∧
    Tendsto (deposited F J A K W simple B Y) trail (𝓝 c) := by
  have evaluated := WilsonMaxwellThermometerFirstPosition.original F J A K W simple B hB prior book lead
  have ordered := Complex.continuous_re.continuousAt.tendsto.comp evaluated
  have bounded := eventually_curry_iff.mp (Metric.tendsto_nhds.mp ordered 1 zero_lt_one)
  have fibre : ∀ᶠ r in trail, Tendsto (fun z => (first r z).re) (Y : Filter _)
      (𝓝 (deposited F J A K W simple B Y r)) := by
    filter_upwards [bounded] with r close
    apply tendsto_nhds_limUnder
    obtain ⟨b,_,limit⟩ := (isCompact_closedBall c 1).ultrafilter_le_nhds (Y.map (fun z => (first r z).re))
      (le_principal_iff.mpr (close.mono fun _ h => h.le))
    exact ⟨b,limit⟩
  refine ⟨fibre,Metric.tendsto_nhds.mpr fun ε hε => ?_⟩
  filter_upwards [fibre,eventually_curry_iff.mp (Metric.tendsto_nhds.mp ordered _ (half_pos hε))] with r limit tight
  exact (le_of_tendsto (limit.dist (tendsto_const_nhds (x:=c))) (tight.mono fun _ h => h.le)).trans_lt (half_lt_self hε)

/-- Signed physical comparison with the separately evaluated finite first
coefficient on the identical corrected three-field vector. -/
def invoice (Y : Ultrafilter (ℕ × ℕ)) (C η : ℝ) : Prop :=
  WilsonPositionThermometerSevenFaceRate.charged (R:=R) simple (B:=B) Y C η out
    (fun r z => (first r z).re)

theorem original (pace : WilsonWindowReportingPace.Slow R.kit) (hB : 0<B)
    (bliss : Bliss F Y arch H) (book : Book (f:=f) (l:=Y) (H:=H) A J)
    (lead : Leading F J) {C η : ℝ} (slack : η<1) (paid : invoice F J A K W simple B Y C η) :
    Coupling G (WilsonPositionThermometerReading.reading F P K) := by
  have issued := removed F J A K W simple B hB bliss.lies book lead
  exact (WilsonPositionThermometerSevenFaceRate.compared F P K simple Y bliss.lies arch.β bliss.keen.mintS
    pace hB bliss slack out (WilsonPositionGradedThermometerHearing.signed F J V lead K A book simple bliss.lies)
    _ _ issued.1 issued.2 paid).2

end YM.Integration.WilsonMaxwellThermometerFirstInvoice
end
