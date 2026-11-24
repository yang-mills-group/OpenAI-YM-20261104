import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.FundedViewerFramePrices
import YM.SignedWilsonExpansion.Public.Compass
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
noncomputable section

namespace YM.Answer.ContinuumLimit
open Lattice RG MeasureTheory Function Filter Wilson Integration Integration.Election Climb Extraction Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato FullVolume Spec Table Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1
open MS MS.High MS.Native MS.Land MS.Fleet MS.Tide MS.Book PhysMS PhysMS.Frame Next.UVStress Order Spin OPE OPE.Orbits
open FVA2 FVA2.Register FVA2.Scale.Level FVA2.Scale SignedWilsonExpansion SignedWilsonExpansion.Belle SignedWilsonExpansion.Belle.Path SignedWilsonExpansion.Museum SignedWilsonExpansion.Kane SignedWilsonExpansion.Kane.Tilted SignedWilsonExpansion.Camera
open Asymptotics WilsonPositionHomogeneousComparison
open PowerSeries XSpace.Cirrus Future
open Integration Integration.Election Extraction Climb Lattice Wilson RG Function Filter Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Table Spec
open PhysMS PhysMS.Frame Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Register Scale OPE OPE.Orbits
open SignedWilsonExpansion SignedWilsonExpansion.Kane SignedWilsonExpansion.StageG Camera SignedWilsonExpansion.Kane.Tilted Next.UVStress XSpace.Cirrus
open MS MS.High MS.Land MS.Native MS.Tide MS.Fleet MS.Book PowerSeries Asymptotics
open Belfry Belle Dancer Belfry.ScaleFits Belfry.Classroom Scale Level GroupS
open scoped BigOperators Classical ContDiff Topology
universe u
variable {G:Gauge}{H:G.Simple}{ε:ℝ}{e:Axis}{O:OrderS G}{E:Construction.{u} H ε e O}
variable {ξ:Extraction.Order} {V:Vision E ξ} {Z:WilsonPrescription G}{dial:Bool} {Q:Perspective H Z dial}

namespace PublishedFrameTransfers
open YM.Integration.WilsonViewerElectedHierarchy YM.Integration.WilsonMacroscopicRichTwoDatePivot
theorem viewerPrice (V : Vision E ξ) (Z : WilsonPrescription G) {lamp}
    (Q : Perspective H Z lamp) {n : ℕ} {d : Caps n} (v : MaxwellSlots E.paths.family d)
    (j k : ℕ) (K : Set (Points n)) (compact : IsCompact K) (separated : K ⊆ conf n)
    {δ : ℝ} (positive : 0 < δ) : ∀ᶠ r in trail, ∀ x∈K, ∀ p p' : Viewers V.pupil.last,
      ‖iteratedFDeriv ℝ j (measured V.pupil.last p (V.Post Z r) v r) x -
        iteratedFDeriv ℝ j (measured V.pupil.last p' (V.Post Z r) v r) x‖ ≤ δ*(V.T Z r)^k :=
  fundedViewerPrice (simple := H) V.pupil.bliss V.pupil.VFrame.2 V.pupil.VFrame.1
    V.pupil.foundation Z v j k K compact separated (V.T Z) (V.certificate Q).calendar.clock positive

theorem viewerZero (V : Vision E ξ) (Z : WilsonPrescription G) {lamp}
    (Q : Perspective H Z lamp) {n : ℕ} {d : Caps n} (v : MaxwellSlots E.paths.family d)
    (j : ℕ) (K : Set (Points n)) (compact : IsCompact K) (separated : K ⊆ conf n)
    (δ : ℝ) (positive : 0 < δ) : ∀ᶠ r in trail, ∀ x∈K, ∀ p : Viewers V.pupil.last,
      ‖iteratedFDeriv ℝ j (measured V.pupil.last p (V.Post Z r) v r) x -
        iteratedFDeriv ℝ j (WickGoal v) x‖ < δ :=
  fundedViewerZero (simple := H) V.pupil.bliss V.pupil.VFrame.2 V.pupil.VFrame.1
    V.pupil.foundation Z v j K compact separated δ positive (V.T Z) (V.certificate Q).calendar.clock

theorem preOfPost (V : Vision E ξ) (Z : WilsonPrescription G) (k : ℕ)
    (u : ℝ → V.pupil.S.Field k) (v : RG17.Free E.paths.family k)
    (post : Tendsto (fun r : ℝ => (V.Post Z r k).symm (u r)) trail (𝓝 v)) :
    Tendsto (fun r : ℝ => (V.pupil.J r k).symm (u r)) trail (𝓝 v) := by
  have columns (w : RG17.Free E.paths.family k) :=
    WilsonMacroscopicRichTwoDatePivot.field V.pupil.last V.pupil.J Z V.pupil.VFrame.2 V.pupil.VFrame.1 H k w
  have transported := Dash.arcing (Dash.fit_plane (fun r : ℝ =>
    (WilsonMacroscopicRichTwoDatePivot.active V.pupil.last V.pupil.J Z r k).toLinearMap)
    LinearMap.id columns) post
  apply transported.congr
  intro r
  change (V.pupil.J r k).symm (V.Post Z r k ((V.Post Z r k).symm (u r))) = _
  rw [LinearEquiv.apply_symm_apply]

theorem preStress (V : Vision E ξ) (Z : WilsonPrescription G) (i j : Axis)
    (post : Tendsto (fun r : ℝ => (V.Post Z r 4).symm (r^4 • V.pupil.last.sector.energy i j))
      trail (𝓝 (Pert.freeStress E.paths.family.labels i j))) :
    Tendsto (fun r : ℝ => (V.pupil.J r 4).symm (r^4 • V.pupil.last.sector.energy i j))
      trail (𝓝 (Pert.freeStress E.paths.family.labels i j)) :=
  preOfPost V Z 4 (fun r : ℝ => r^4 • V.pupil.last.sector.energy i j)
    (Pert.freeStress E.paths.family.labels i j) post

end PublishedFrameTransfers
end YM.Answer.ContinuumLimit
end
