import YM.SignedWilsonExpansion.Public.Archive
import YM.Integration.WilsonPositionThermometerGradedSource
set_option autoImplicit false
set_option maxHeartbeats 480000
noncomputable section
namespace YM.Answer.ContinuumLimit
open Lattice RG MeasureTheory Function Filter Wilson Integration Integration.Election Climb Extraction Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato FullVolume Spec Table Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1
open MS MS.High MS.Native MS.Land MS.Fleet PhysMS PhysMS.Frame Next.UVStress Order Spin OPE OPE.Orbits
open FVA2 FVA2.Register FVA2.Scale.Level FVA2.Scale SignedWilsonExpansion SignedWilsonExpansion.Belle SignedWilsonExpansion.Belle.Path SignedWilsonExpansion.Museum SignedWilsonExpansion.Kane SignedWilsonExpansion.Kane.Tilted SignedWilsonExpansion.Camera
open Asymptotics WilsonPositionHomogeneousComparison
open scoped ContDiff Topology Classical BigOperators
universe u
namespace Vision
variable {G:Gauge}{H:G.Simple}{e:Axis}{ε:ℝ}{O:OrderS G}{E:Construction.{u} H ε e O}{f:Extraction.Order}
variable {Z:WilsonPrescription G}{dial:Bool} (V:Vision E f)(Q:Perspective H Z dial)
local notation "ℂ*"=> V.pupil.last -- only bare
local notation "Ξp" => E.paths
local notation "τ₀"=> V.T Z

open WilsonPositionThermometerGradedSource
abbrev roseShape : Caps 3:= fun i=> (( WilsonPositionThermometerGradedSource.grade i ):ℕ)
abbrev roseLenses (G:Gauge): ( i:Fin 3 )→ Sec G ( roseShape i ) := WilsonPositionThermometerGradedSource.base G
-- This picks *cap*-unit, apply maskPrice/maskWord accordingly
variable (s:Rose.Badge)(r:ℝ)
local notation "t" => ( Rose.test Z.criterion )
local notation "L"=> roseLenses G
abbrev measuredAtHold := summit E.paths.family ( Rose.test Z.criterion ) r Buffet.cumul (fun m=>MaskWord Z V false r roseShape L m )
local notation "M₀"=> ( measuredAtHold (Z:=Z) V )
local notation "Ω"=> ( FOrder V )
include Q
lemma maskTargets : ∀ᶠ r in trail,∀ x∈conf 3,∀ m:Rose.Badge, Life Z V false r roseShape ( coversB roseShape m L ) x none= WilsonPositionThermometerReading.sample V.pupil.last ( V.Pre Z ) r x m:= ( WilsonPositionThermometerGradedSource.measured V.pupil.last ( V.Pre Z ) ( V.certificate Q ).leading ).mono fun i hi x hx m=> ( hi x hx m ).symm
lemma heldClock : ∀ᶠ k in trail, ( FOrder V ).limits (fun p=>Museum.Prism E.paths.family.S ( tsupport ( Rose.test Z.criterion ) ) p k ) ( measuredAtHold (Z:=Z) V k ) ( Vision.Signal V Z k ) :=by
     filter_upwards [ RG17.positiveLength, maskTargets V Q ] with i hi hx; have hh: Continuous (Buffet.cumul : ( _→ℂ )→ℂ) := by unfold Buffet.cumul; fun_prop; -- ambiguity
     have ht:= ( V.realizations Q ).profileLimit false roseShape L i hi t Buffet.cumul hh; convert ht using 1; unfold Signal WilsonPositionThermometerReading.tested; apply Test.apply_eq; intro x hu; exact congrArg Buffet.cumul ( funext ( fun j=> ( hx x hu j ).symm ) )
end Vision
end YM.Answer.ContinuumLimit
