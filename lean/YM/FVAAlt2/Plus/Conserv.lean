import YM.FVAAlt2.Plus.Dial
/-! These are precisely the two endpoints, for NONHOMOGENEOUS top stencils:
`YM.MS.Tide.removePl` and `YM.MS.Dial.LPT_to_MSPl`. No change to scheme
or to trust/comparison/error/continuum definitions. For original dictionary
they certify back to BOTH original endpoints.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2
open MS MS.Land MS.Tide MS.Dial MS.Menus MS.Book MS.Latch MS.Vane MS.Fleet Lattice MS.Rake MS.Orbit MS.Vista
open Function Filter Topology
variable {I W:Type}{G:Gauge}{B:MS.Local.Physical.Deck G}{M:Booked B}(S:MS_Data G M)
variable (V:LitBook B)(Q:Land.Prescription B)(p:W→Label B)[LinearOrder W]
set_option linter.unusedSectionVars false
lemma recoversH: TaylorOKPl S (extendMenu V) Q ↔ TaylorOK S V Q:= ⟨fun h=>⟨h.bulk,h.mark⟩,fun h=>⟨h.bulk,h.mark⟩⟩
lemma recoversT (P:Geo I) (x:Faces I) (L:I→Side) (c:Berth (W:=W) (I:=I)) (u:ℝ)(b:Bool)(l:Filter I)(Z:Terrify W I)(Y:Rake.Dance G I W): scalePhysicsPl P M S u Q (extendMenu V) p c x L b l Z Y ↔ scalePhysics P M S u Q V p c x L b l Z Y:= ⟨fun h=>⟨h.native,h.empty,h.scheme,h.huge,h.compares⟩, fun h=>⟨h.native,h.empty,h.scheme,h.huge,h.compares⟩⟩
lemma recoversD (T:Trial I W)(l:Filter I)(v:ℝ)(b:Bool)(X: Terrify W I): coherentPl M S (extendMenu V) p T v b Q l X ↔ coherent M S V p T v b Q l X:= ⟨fun h=>⟨h.init,h.cost,h.ready,h.bouquet⟩, fun h=>⟨h.init,h.cost,h.ready,h.bouquet⟩⟩
end YM.FVAAlt2

