import YM.FVA2.Register.Pressroom
import YM.FVA2.Parity.Clock
/-!
# Expose the parity result next to the comparison

See `YM/FVA2/Main.lean`, `Teller/Where` and `Parity/Clock` about the
actual data used.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Register
open Function Set Filter Finset MeasureTheory Metric Lattice Wilson
open YM.FVA2
open MS MS.Plane MS.Koszul MS.Book MS.Book.Convolve Program MS.Native MS.Theater MS.Menus MS.Local.Physical MS.Land
open MS.Orbit MS.Fleet MS.Tide MS.Swirl MS.Swirl.Near MS.Rake Press XPos Change Slice
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking BlockGauge BlockGauge.Fabric OpenSlots.Quadratic
open PertExtension PertExtension.Series PertExtension.Series.Tested PertExtension.Orb Facade Hearth RGComparison.Core16
open Arrival Arrival.Episodic XSpace Normalize Parity
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}
namespace WilsonPrescription
variable (N:WilsonPrescription G)
variable (M:Land.Prescription (Press.portDeck G)) (h:G.Simple)
variable (T: Land.MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "║"=> N.scheme
local notation "ω'"=> N.criterion
structure Served (M:Prescription ( Press.portDeck G )) : Prop extends Posted N T M where
    input : Parity.Screen.Right M
    whole (ν:ℝ): Parity.Clock.Presence N.scheme N.criterion T ν
lemma illuminate (he: Posted N T M)(h:G.Simple): Served N T (Parity.Screen.brush M):= by
    let X:=Parity.Screen.brush M; obtain ⟨ ht,hw,hu,hv ⟩:= Parity.Screen.eternal N.scheme T M h he.born.Taylor he.born.still he.born.base;
    refine ⟨ ⟨ Speed.beats_all N.scheme _ X T h ( Scale.System.promotes _ _ T X h ?_ ), he.journey, he.supplies, fun u L d i v y=>?_⟩, hw,fun t=> Parity.Clock.measured t N.scheme _ T X h ht hu hv ⟩
    exact ⟨ Reg.lifts N.scheme N.criterion T h X ⟨ ht,hu,hv⟩, fun n E J p W _ u d P x s=> Arrival.Episodic.platform _ _ _ _ _ _ _ _ _, he.toQuoted.toContract.toMission.stock, he.herald ⟩
    exact Rescaled.on_clock _ _ _ _ _ _ _ _ _
include h
theorem serves (dial:Bool): ∃ M:Prescription ( Press.portDeck G ), M.team=( Continuum.Continuation.proofStart h (Reg.supplies N.scheme T) dial ).team ∧ Served N T M:= by
    obtain ⟨M,hp,he⟩:= N.end_to_continuum h T dial; exact ⟨Parity.Screen.brush M,hp,illuminate N M T he h⟩
-- For the numerical cubic beta coefficient and running clock, see `Lambda.AtLast` and `Generator.Drive.clocks_run`.
end WilsonPrescription
end YM.FVA2.Register
