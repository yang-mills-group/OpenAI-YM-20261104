import YM.RG05Readout.Petra.Arch
import YM.Integration.WilsonSeparatedOriginalSlabOriginRoom
import YM.Integration.WilsonSeparatedOriginalSlabBladeModule

/-! Insert a genuinely independent unit at the reporting origin without translating any of the proposed fields or the old gauge configuration. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabRootedAlcove
open MeasureTheory Finset Lattice Wilson Labels RG Source Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage
open Ribbons WilsonReportHarvestSlabLabels WilsonSeparatedOriginalSlabBladeModule RG05Readout.Petra
open scoped Classical BigOperators
variable {G:Gauge}{C:Family G}{D:Address.Rail C}{n N per:ℕ}
set_option quotPrecheck false
local notation "Y"=>C.path.rep N per n

theorem original (made:C.Makes)(tiers:Cater C D){o:Fin 3 → Site (C.side n per)}{rows:Fin 3 → Three G (C.side n per)}
    {F:Config G (C.side n per)→Poly (Stock.census (Fin 3))}{r t:ℝ}{shell:ℕ}
    (hn:0<n)(nN:n≤N)(degree:3≤C.path.levels.clock.J n)(rp:0<r)(furls:Furls C.path.levels n t)
    (reach:∀i,coverNumber (C.path.levels.budget n).B ({0,o i}:Support (C.side n per))≤ shell)(sp:1≤ shell)
    (estate:Alcove Y rows F o (fun _=>r) t (Bandage.renal C.path.levels n) (1/2)):
    0<Root.boon C 3 n shell r ∧ Filed Y 0 (fun U=>(F U).part WilsonReportHarvestSlabLabels.entire)
      (4/Root.boon C 3 n shell r):=by
  have occ:Occupancy (Root.roots (0:Site (C.side n per)) o) (apron C.path.levels n):=by
    intro z
    exact (Finset.card_le_univ _).trans (by simpa using WilsonSeparatedOriginalSlabOriginRoom.aperture C n degree)
  obtain ⟨positive,x,good,blade,fld⟩:=Root.rope (0:Site (C.side n per)) made tiers nN hn furls rp occ reach sp estate
  refine ⟨by simpa using positive,x,good,fld,?_⟩
  simpa only [Fintype.card_fin,one_div,div_eq_mul_inv,one_mul] using blade

end YM.Integration.WilsonSeparatedOriginalSlabRootedAlcove
