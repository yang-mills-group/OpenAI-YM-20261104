import YM.Integration.WilsonMaxwellThermometerSolvedSlope
import YM.Integration.WilsonOriginalNullReleasedGalopFit
/-! First coefficient of the complete public detected response of the actual
released Wilson columns. The finite displacements in Solved refer to the
original tilted physical projection at the very same N and period. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerReleasedSlope
open Function Filter Finset Spec Extraction Table RG Lattice OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open Wilson PhysicalNext.Repeat.Legato RG17 PhysMS PhysMS.Frame
open Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Cirrus XSpace.Photo
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonMaxwellThermometerPublicStation WilsonMaxwellThermometerSignedWallet
open WilsonOriginalNullReleasedMaximalLimit
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G)(W:Initialize G){V:Normalize.Store G}(K:Rose.Pick V)
variable {f:Extraction.Order}{Y:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{S:Table R.family.book}
variable (F:Final R.family f S)(J:ℝ→tower S)(A:ℝ→Group R.family 6)
local notation "Z" => WilsonPositionCorrectedCap.adjusted F J V A
local notation "k" => fun r=>(Z r).station.k
local notation "cut"=>trail.curry (Y:Filter (ℕ×ℕ))

theorem original (simple:G.Simple)(shop:WilsonReportingAbsoluteInletSimultaneous.StationInvoice R)
    (book:Book (f:=f) (l:=Y) (H:=H) A J)(lead:Leading F J)(q:ℕ)(prior:(Y:Filter _)≤f.fuse)
    (v:ℝ×(ℕ×ℕ)→∀i,Axes R i)
    (paid:∀ᶠ w in cut,∀i,Solved R (Z w.1) q w.2.1 w.2.2 univ i (v w i)):
    Tendsto (fun w:ℝ×(ℕ×ℕ)=>report R W K k w.1 w.2 (deposited R (k w.1) w.1 w.2.2 (v w)))
      cut (𝓝 ((Rose.c_T K:ℝ):ℂ)):=by
  exact WilsonMaxwellThermometerSolvedSlope.original R W K Z (WilsonPositionPrescribedFrame.positioned F J V)
    simple (WilsonPositionCorrectedCap.original F J V A book lead) prior v
    (WilsonOriginalNullReleasedGalopFit.original R simple shop F J V A book lead q prior v paid)

end YM.Integration.WilsonMaxwellThermometerReleasedSlope
end
