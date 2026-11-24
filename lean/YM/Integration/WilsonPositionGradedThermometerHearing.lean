import YM.Integration.WilsonPositionCorrectedCap
import YM.Integration.WilsonPositionThermometerGradedReading
import YM.Integration.WilsonPositionPrescribedNested

/-! The cutoffs of the common position frame converge against the original
thermometer test at the three source horizons on its elected ultrafilter. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionGradedThermometerHearing
open Function Filter Set Table Spec Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open Lattice Wilson RG PhysicalNext.Repeat.Legato RG17 PhysMS PhysMS.Frame Maxwell XSpace
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonPositionThermometerGradedSource
open scoped Topology Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → tower S) (V : Normalize.Store G) (lead : Leading F J)
local notation "P" => WilsonPositionPrescribedFrame.positioned F J V
local notation "E" => (Maxwell.Free.scheme R.family.labels)
local notation "D" => F.sector.derivatives

include lead in
theorem raised {d e : ℕ} (h : d ≤ e) : ∀ᶠ r in trail, ∀ x, P r e ((E).rise h x) = (D).rise h (P r d x) := by
  have src := Maxwell.Free.scheme_filters R.family.labels
  have own := F.phase.transport.injection
  have ax := F.room.kernel.laws.toSymmetric
  have sym := (Maxwell.Free.hierarchy R.family.labels).laws.toSymmetric
  have future := WilsonPositionPrescribedNested.transported F J lead V P
    (fun d r h v=>congrArg (J r d) (WilsonPositionPrescribedFrame.leg F J V h v))
  induction h with
  | refl => exact Eventually.of_forall fun r x=>by rw [(E).arrival sym src,(D).arrival ax own]
  | step h ih =>
    filter_upwards [ih,future _] with r before next x
    rw [← (E).transit sym src h (Nat.le_succ _) x,next,before,(D).transit ax own]

include lead in
theorem measured : ∀ᶠ r in trail, ∀ x∈conf 3, ∀ s : Rose.Badge, WilsonPositionThermometerReading.sample F P r x s =
    PhysMS.measured F none (P r) (d:=fun i => (grade i).val) (source R.family s) r x := by
  have ready := eventually_all.mpr (fun i : Fin 3 => raised F J V lead (Nat.le_of_lt_succ (grade i).isLt))
  filter_upwards [ready,RG17.positiveLength] with r applies hr x hx s
  change S.classMoment S _ (r • x) (fun i=>P r 6 (WilsonPositionThermometerReading.leg R.family s i))=_
  simp_rw [←promoted,applies]
  exact AllOrder.Leading.moment_inclusion F.room.kernel.laws.toSymmetric F.phase.transport.injection
    (fun i=>Nat.le_of_lt_succ (grade i).isLt) (Work.A05.smul_conf hr hx)
    (fun i=>P r (grade i) (source R.family s i))

variable {Y : Ultrafilter (ℕ × ℕ)} {H : (Bel R.family.book).Hierarchy}

def offer (K : Rose.Pick V) (A : ℝ → Group R.family 6) (r : ℝ) (z : ℕ × ℕ) :=
  (Rose.test K).applyTo (WilsonPositionThermometerGradedReading.full r (WilsonPositionCorrectedCap.adjusted F J V A r) z)

include lead in
theorem signed (K : Rose.Pick V) (A : ℝ → Group R.family 6) (book : Book (f:=f) (l:=Y) (H:=H) A J)
    (simple : G.Simple) (prior : (Y : Filter _) ≤ f.fuse) :
    ∀ᶠ r in trail, Tendsto (offer F J V K A r) (Y : Filter _) (𝓝 (WilsonPositionThermometerReading.tested F P K r)) := by
  filter_upwards [WilsonPositionCorrectedCap.original F J V A book lead 0,measured F J V lead,RG17.positiveLength] with r filed lands hr
  exact WilsonPositionThermometerGradedReading.signed F P r _ simple prior filed.2.2.2.1
    (fun s i=>( (filed.2.2.2.2.1 (grade i)).2.2 _).symm) lands K hr

end YM.Integration.WilsonPositionGradedThermometerHearing
