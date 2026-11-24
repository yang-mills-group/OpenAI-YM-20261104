import YM.SignedWilsonExpansion.Public.Prediction
import YM.SignedWilsonExpansion.Grid.Rise
namespace YM.Answer.ContinuumLimit.Vision
/-! Every off-axis call independent receipt. E field orientation WickFace.lens left right 1,2. Off diagonals destroyed by reflection. Complex removable clock second order. Raw free connected normalization corners occupation. -/
set_option autoImplicit false
noncomputable section
open Integration Integration.Election Extraction Climb Lattice Wilson RG Function Filter Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Table Spec
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Register Scale
open SignedWilsonExpansion SignedWilsonExpansion.Kane SignedWilsonExpansion.StageG Camera SignedWilsonExpansion.Kane.Tilted Next.UVStress
open MS MS.High MS.Land MS.Native MS.Tide MS.Fleet MS.Book
open PhysMS PhysMS.Frame Next.UVStress Order
open Belfry Belle OPE OPE.Orbits MeasureTheory Asymptotics FullVolume
open Carbon Frames Museum
open SignedWilsonExpansion.Overlap Chart Expert Marque
open scoped Classical Topology ContDiff BigOperators
universe u
variable {G:Gauge} {Z:WilsonPrescription G}{H:G.Simple}{ε:ℝ}{e:Axis}{O:OrderS G}{E:Construction.{u} H ε e O}{f:Extraction.Order}
variable (V:Vision E f){dial:Bool}(Q: Perspective H Z dial)(x:Scale.Stage 3)(φ: Test 3)(ν:ℝ)(a:Bool) (ϕ:RealTest 3)(hz: Golden G x ϕ)
local notation "Θ" => Real.log 2
local notation "K" => (four Z)
local notation "I" => Marque.ticket
local notation "p" => ( Rose.coerce ϕ )
/-- All points, even those in off-axis test beyond-center.
    Purely Maxwell choice test. Chart.priceR uses only Free House normalization at separated.
    On the independent coefficient: use with Prediction.compared (all smoothed, in its character and continuum settings). -/
structure FreeCorner (Q: Perspective H Z dial): Prop where
    quoted (φ:Test 3) : ProbeB.quote K φ 2=fund G φ
    place (x:Scale.Stage 3): ProbeB.receipt K 2 x.val=(Θ) • ( (priceR G x):ℂ )
    free (x:Scale.Stage 3): ProbeB.criterion K 0 x.val=( ( Fintype.card G.ColorIndex*8*I x 0 1 3 3* I x 0 2 3 3* I x 1 2 3 3:ℝ ):ℂ)
    supports (x:Scale.Stage 3) (ϕ:RealTest 3) : Golden G x ϕ ↔ ProbeB.Admire K x ϕ
lemma quotedExplicitly : FreeCorner Q:= ⟨fun φ=> priced Z Q.matching φ 0,fun x=> foiled Z Q.matching x 0,fun x=> corner Z Q.matching x 0,fun x φ=> appreciated Z Q.matching x φ 0⟩
include hz Q in
lemma funded_axial : (fund G ( Rose.coerce ϕ )).im=0 ∧ 0<( fund G p ).re:= by
    have ht:= Q.matching; let q':= ProbeB.quote K p 2; obtain ⟨h₁,h₂⟩:= Carbon.plank Z ht 0 x ϕ ( ( quotedExplicitly Q ).supports x ϕ |>.1 hz ); rw [ ← ( quotedExplicitly Q ).quoted ]; refine ⟨ ?_,h₂⟩; change star q'=q' at h₁; change q'.im=0; have he : -(q'.im)= q'.im:=congr_arg Complex.im h₁; linarith
end
end YM.Answer.ContinuumLimit.Vision
