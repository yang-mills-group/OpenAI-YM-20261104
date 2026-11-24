import YM.Integration.WilsonMaxwellThermometerPublicRoom
import YM.Integration.WilsonMaxwellThermometerVotedCurrency

/-! The original all-radii book pays the public operator norm before the two
cutoff choices, on precisely the three filed signed source arms. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerPublicCollege
open Function Set Filter Finset RG Lattice Labels Source Extraction Table OPE OPE.Orbits Climb
open Trace Trace.Pilot Next.UVStress Cells PhysicalNext.Repeat.Legato Next.Rank Next.Rank.Atlas
open MergeProof.East PhysMS PhysMS.Frame XSpace XSpace.Cirrus XSpace.Rose XSpace.Structure1 XSpace.Normalize
open WilsonPositionCapTransport WilsonPositionThermometerCapStation WilsonMaxwellThermometerPublicStation
open WilsonMaxwellThermometerPublicUniform WilsonMaxwellThermometerPublicRoom
open WilsonMaxwellThermometerPublicEvenSlope WilsonMaxwellThermometerChargedHeads
open WilsonSeparatedOriginalThermometerDetectorMesh
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) (W:Initialize G){V:Normalize.Store G}(K:Rose.Pick V)
variable {f:Extraction.Order}{Y:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{S:Table R.family.book}
variable (A:ℝ→Group R.family 6)(J:ℝ→tower S)
local notation "station" => fun r=>(A r).station.k

theorem funding (simple:G.Simple)(book:Book (f:=f) (l:=Y) (H:=H) A J):
    Tendsto (aperture R station) trail (𝓝 0) ∧ Spacious R station:=
  real R simple A (tendsto_atTop.mpr fun j=>(book j).mono fun _ h=>h.1)
    ((book 0).mono fun _ h=>⟨h.2.2.1,h.2.1.high⟩)

theorem paid (simple:G.Simple)(book:Book (f:=f) (l:=Y) (H:=H) A J)
    {I:Fin 3→Type}[∀i,Fintype (I i)](fields:∀i,I i→Sec G 6):
    ∃C:ℝ,0≤C ∧ ∀ᶠ r in trail,∀N per,(A r).station.k≤N→∀a:∀i,I i,
      ‖report R W K station r (N,per) (fun i=>fields i (a i))‖≤C:=
  WilsonMaxwellThermometerPublicUniform.basis R W K station fields (funding R A J simple book).1 (funding R A J simple book).2

theorem voted (simple:G.Simple)(book:Book (f:=f) (l:=Y) (H:=H) A J):
    ∀ᶠ r in trail,∀per:ℕ,V.Meets W
      (chart R ((A r).station.k) per (aperture R station r) (granted R station r)) 6:=by
  have ready:∀ᶠ m in Front,V.Meets W m 6:=(V.nested_solution W 6 Cirrus.frontier).2.mono fun _ h=>h.1
  exact boards R station (funding R A J simple book).1 (funding R A J simple book).2 ready

end YM.Integration.WilsonMaxwellThermometerPublicCollege
end
