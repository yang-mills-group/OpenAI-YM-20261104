import YM.Integration.WilsonMaxwellThermometerPublicReturn
import YM.Integration.WilsonMaxwellThermometerPublicLower
import YM.Integration.WilsonPositionThermometerSevenFaceRate

/-! Restoring the signed grade-four projection of the genuine public field
costs little-o of the reporter's own coupling. Either one coupling price
on the lower triangles, or one on the true public calibration survey,
suffices together with convergence of the other factor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerPublicHearing
open Filter Lattice Wilson RG Maxwell Maxwell.Free RG17 XSpace XSpace.Normalize
open Table Spec Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress PhysMS PhysMS.Frame
open PhysicalNext.Repeat.Legato WilsonPositionThermometerCapStation WilsonMaxwellThermometerPublicPocket
open scoped Topology Classical BigOperators
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book}
  (F:Final R.family f S) (J:ℝ→PhysMS.tower S) (V:Store G) (K:Rose.Pick V) (A:ℝ→Group R.family 6)
  (Y:Ultrafilter (ℕ×ℕ)) (simple:G.Simple) (B:ℕ)
  {I:Type} [Fintype I] (D:RG17.Free R.family 6 →L[ℂ] (I→ℂ)) (e:I→RG17.Free R.family 4)
local notation "L" => trail.curry (Y:Filter (ℕ×ℕ))
local notation "g" => WilsonPositionThermometerSevenFaceRate.temperature (R:=R) simple (B:=B)
local notation "v" => coordinates R F J V D
local notation "s" => WilsonMaxwellThermometerPublicPocket.measured R F J V K A


/-- The returned public grade-four pocket is o(g) on the original seven physical
faces once the native finite grade-six calibration survey has its signed price. -/
theorem original {H:(Bel R.family.book).Hierarchy} (prior:(Y:Filter _)≤f.fuse)
    (book:WilsonPositionCapTransport.Book (f:=f) (l:=Y) (H:=H) A J)
    (lead:Leading F J) (C:ℝ) (positive:0<C)
    (paid:∀ᶠw:ℝ×(ℕ×ℕ) in L,WilsonPositionOriginalCalibrationSensitivity.price F J V 6 w.1 ≤ C*|g w.1 w.2|):
    ∀ε>0,∀ᶠw:ℝ×(ℕ×ℕ) in L,
      ‖WilsonMaxwellThermometerPublicReturn.bill R F J V K A D e w.1 w.2‖≤ε*|g w.1 w.2|:=
  WilsonMaxwellThermometerPublicReturn.survey R F J V K A Y simple B D e lead C positive paid
    (fun i=>WilsonMaxwellThermometerPublicLower.original R F J V K A simple prior book lead (e i))

end YM.Integration.WilsonMaxwellThermometerPublicHearing
