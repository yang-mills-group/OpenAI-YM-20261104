import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.PhysicalSignedStressPullback
import YM.SignedWilsonExpansion.Public.Compass
set_option maxHeartbeats 950000
set_option maxRecDepth 8192
set_option quotPrecheck false
set_option autoImplicit false
noncomputable section
namespace YM.Answer.ContinuumLimit
open Integration Integration.Election Extraction Climb Lattice Wilson RG Function Filter Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Table Spec
open PhysMS PhysMS.Frame Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Register Scale OPE OPE.Orbits
open SignedWilsonExpansion SignedWilsonExpansion.Kane SignedWilsonExpansion.StageG Camera SignedWilsonExpansion.Kane.Tilted Next.UVStress XSpace.Cirrus
open MS MS.High MS.Land MS.Native MS.Tide MS.Fleet MS.Book PowerSeries Asymptotics
open Belfry Belle Dancer Belfry.ScaleFits Belfry.Classroom Scale Level GroupS
open scoped Classical Topology
universe u
variable {G:Gauge}{H:G.Simple}{ε:ℝ}{e:Axis}{O:OrderS G}{E:Construction.{u} H ε e O}
variable {ξ:Extraction.Order} {V:Vision E ξ} {Z:WilsonPrescription G}{dial:Bool} {Q:Perspective H Z dial}

namespace PublishedStressCoordinates
open Trace.Over TraceExtension StressFlux Spin Maxwell.Free
theorem publishedAxes (V : Vision E ξ) (Z : WilsonPrescription G) {lamp}
    (Q : Perspective H Z lamp) (k : ℕ) : ∀ᶠ r : ℝ in trail,
    (∀ u : (Bel E.paths.family.book).Field k, V.Post Z r k ((Bel E.paths.family.book).conj V.pupil.H.spin k u)
      = V.pupil.S.conj V.pupil.last.room.kernel.spin k (V.Post Z r k u)) ∧
    (∀ (s : Signed) (u : (Bel E.paths.family.book).Field k),
      V.Post Z r k ((Bel E.paths.family.book).mirror V.pupil.H.spin k s u)
        = V.pupil.S.mirror V.pupil.last.room.kernel.spin k s (V.Post Z r k u)) := by
  let b := Maxwell.Free.fields E.paths.family.labels k
  have bar (u : (Bel E.paths.family.book).Field k) :
      b ((Bel E.paths.family.book).conj V.pupil.H.spin k u) = reel k (b u) :=
    Subtype.ext (Maxwell.Free.address_star E.paths.family.labels u)
  have axis (s : Signed) (u : (Bel E.paths.family.book).Field k) :
      b ((Bel E.paths.family.book).mirror V.pupil.H.spin k s u) = ori s.ortho k (b u) :=
    Subtype.ext (Maxwell.Free.address_motion E.paths.family.labels s u)
  filter_upwards [((V.certificate Q).spin k).2] with r orient
  have value (u : (Bel E.paths.family.book).Field k) : walk (V.Post Z) r k (b u) = V.Post Z r k u := by
    change V.Post Z r k (b.symm (b u)) = _
    rw [LinearEquiv.symm_apply_apply]
  constructor
  · intro u
    rw [←value,bar,orient.2.1,value]
  · intro s u
    rw [←value,axis,orient.2.2,value]

theorem filedTensor (V : Vision E ξ) (Z : WilsonPrescription G) {lamp}
    (Q : Perspective H Z lamp) : ∀ᶠ r : ℝ in trail,
    RawTensor V.pupil.H.spin (fun i j : Axis => (V.Post Z r 4).symm
      (r^4 • V.pupil.last.sector.energy i j)) := by
  filter_upwards [publishedAxes V Z Q 4] with r incidence
  exact Trace.Pilot.restaffedSignedEnergyPullback (H := V.pupil.H) V.pupil.last r (V.Post Z r 4) incidence.2

end PublishedStressCoordinates
end YM.Answer.ContinuumLimit
end
