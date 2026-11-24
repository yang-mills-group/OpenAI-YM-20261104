import YM.Integration.WilsonPositionProgramFilmGround
import YM.Integration.WilsonPositionProgramFoldedGround
import YM.Integration.WilsonPositionProgramRelativeClock
import YM.FVAAlt2.Pipeline.Film

/-! An original submitted chronological row recovered from its actual received scalar chart. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionProgramFilmGroundReturn
open Function Filter Finset Lattice Wilson Exterior Precision Tree Marker Multi
open Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Adjacent Comparison.RG02.Symmetry
open Comparison.RG02.Valence
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
    (Order.observe S 0 (Order.logMarked (Bulk.Fk op tree draw intake x 0)) 0).part (S.fire u):=by
  calc
    _=See.noseC S u (T.cloth k.next) (Z k.next) 0 x:=(WilsonPositionProgramFilmGround.reading
        (Z k.next) u (T.cloth k.next) x ((law.allows k.next).1.suppose_mark _)).symm
    _=Orbit.words op tree draw intake r (S.fire u) 0 x:=((law.walks k).mark_w 0 (Nat.zero_le _) x).trans
      (WilsonThermometerOriginalClockSlope.zeroth _ (T.cloth k.prev) r x)
    _=_:=by
      change (Order.observe S r (Order.logMarked (Bulk.Fk op tree draw intake x r)) 0).part (S.fire u)=_
      rw [WilsonOriginalReceivedGradeRestriction.original op tree draw intake x (Nat.zero_le r) 0 (Nat.zero_le 0)]

end YM.Integration.WilsonPositionProgramFilmGroundReturn
end
