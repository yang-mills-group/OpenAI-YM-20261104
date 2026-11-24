import YM.Integration.WilsonPositionProgramFilmSingleton

/-! Integration of the actual chronological incoming field on each later enrolled page. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionProgramFilmGroundLaw
open MeasureTheory Function Filter Finset Lattice Wilson Exterior Precision Tree Marker Multi
open Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Adjacent Comparison.RG02.Symmetry
open Comparison.RG02.Valence YM.Next.SectorChange WilsonThermometerPositionFilmCubicGeometry
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Binding RegulatorIR.Geometry
open PertExtension.Series PertExtension.Series.Tested Booth Pipeline Period.Field RG
open scoped Classical Topology BigOperators
variable {G:Gauge} {I:Type} [DecidableEq I] [Fintype I] {X:Type} {j:X→ℕ} {n:Page j→Side}
  {Q:KernelChoices} {Γ:RG.History G} {E:Circuit j n} (K:Bulk.Chain Γ) (P:SeriesT E Q Γ)
  (S:Census I) (u:I) {m:ℕ} (B:X→Boot.Scout (G:=G) m) (L:Page j→Binding.Scale) (per r:ℕ) (T:See.Times L r)
  (Z:See.Agenda P S per) (law:See.Setup K P S u B (p:=per) L r T Z) (k:Flap j)

local notation "tree" => Halo.bios (P.stepData E Γ per k)
local notation "draw" => directive (P.stepData E Γ per k)
local notation "op" => P.readyKin E Γ K per k
local notation "intake" => See.before P k (Z k.prev)


include law in
theorem original (x:fieldDir G (Γ.S.side (P.vol k.next) per) 1):
    (QuadraticLocal.Earn.Air.discharge (Z k.next) 0 x).part (S.fire u)=
      ∫ z,(QuadraticLocal.Earn.Air.discharge intake 0
        (direction tree (Bulk.translated op tree x z).2)).part (S.fire u)
        ∂(Gaussian.cloud ((op).covariance tree draw)):=by
  have good:Bulk.Well intake:=See.poster
    (fun j (W:Bulk.Colors S G (Γ.S.side j per))=>Bulk.Well W) (Z k.prev) (P.links k) (law.allows k.prev).1
  exact (WilsonPositionProgramFilmGroundReturn.original K P S u B L per r T Z law k x).trans
    (WilsonPositionProgramFilmSingleton.original op tree draw intake u x good.suppose_mark)

end YM.Integration.WilsonPositionProgramFilmGroundLaw
end
