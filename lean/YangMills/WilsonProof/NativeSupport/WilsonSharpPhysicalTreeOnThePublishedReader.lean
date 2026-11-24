import YangMills.WilsonProof.NativeSupport.WilsonSharpPhysicalTreeGeometryCoefficient
import YangMills.WilsonProof.NativeSupport.WilsonSharpPhysicalTreeGeometrySpectators
import YangMills.WilsonProof.NativeSupport.WilsonSharpPhysicalTreeGeometryElection
import YangMills.WilsonProof.NativeSupport.WilsonSharpPhysicalTreeGeometryRecursive
import YM.Integration.WilsonSharpPhysicalTreeDetectorPublishedDaughter

set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonSharpPhysicalTreeOnThePublishedReader
open Filter Spec Extraction Table OPE OPE.Log OPE.Orbits OPE.Orbits.Reader
open WilsonSharpPhysicalTreeGeometry WilsonGraphPaperPublication
open scoped Classical Topology

/-- The two public bounds use one Final, reader, Foundation, and original matrix ticket. -/
theorem on_tested_ticket {g : YangMills.GaugeGroup} {C : Family g.core} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (fac : Facilities C f S) (foundation : Foundation F Q) {l : Filter (ℕ × ℕ)} [l.NeBot]
    (lo : l ≤ f.fuse) (ticket : MatrixTicket (C := C) S F.sector.derivatives l)
    (tested : WilsonSharpPhysicalTreeDetectorApplication.AllTrees F Q) :
    YangMills.Hierarchy.SeparatedNestedPowerLog (YangMills.hierarchy F Q) := by
  refine ⟨coefficient_expansion F Q fac foundation lo ticket, ?_⟩
  intro t a J _ b h o M η c hM hη hc K _ clear
  exact spectator_remainder_from F Q tested t a b h o M η c hM hη hc K clear

theorem on_ticket {g : YangMills.GaugeGroup} {C : Family g.core} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (fac : Facilities C f S) (foundation : Foundation F Q) {l : Filter (ℕ × ℕ)} [l.NeBot]
    (lo : l ≤ f.fuse) (ticket : MatrixTicket (C := C) S F.sector.derivatives l) :
    YangMills.Hierarchy.SeparatedNestedPowerLog (YangMills.hierarchy F Q) :=
  on_tested_ticket F Q fac foundation lo ticket
    (WilsonSharpPhysicalTreeDetectorApplication.same_reader F Q fac.toServices (tickets_suffice F fac lo ticket Q.spans))

/-- The literal hierarchy of the published daughter has sharp arbitrary finite tree
 coefficients and full through-h spectator remainders. -/
theorem original (g : YangMills.GaugeGroup) (hg : g.IsSimple) (p : ℕ → ℕ) (hp : StrictMono p) :
    YangMills.Hierarchy.SeparatedNestedPowerLog ((((issued.{u}).runs g hg).refine p hp).hierarchy) := by
  let ξ := YM.Answer.ContinuumLimit.ElectedPublication.order p hp
  let V := publicPick.{u} g hg ξ
  obtain ⟨hierarchy,on_order,ticket,tested⟩ := WilsonSharpPhysicalTreeDetectorSelectedPupilClient.original.{u} g hg p hp
  have physical : YangMills.Hierarchy.SeparatedNestedPowerLog ((((issued.{u}).runs g hg).refine p hp).hierarchy) := by
    rw [hierarchy]
    exact on_tested_ticket V.pupil.last V.pupil.P V.pupil.pillar V.pupil.foundation on_order ticket tested
  exact ⟨physical.expansion, WilsonSharpPhysicalTreeDetectorPublishedDaughter.original.{u} g hg p hp⟩

end YM.Integration.WilsonSharpPhysicalTreeOnThePublishedReader
