import YM.Integration.WilsonPositionProgramRelativeClock
import YM.FVAAlt2.Pipeline.Film

/-! An original submitted chronological row recovered from its actual received scalar chart. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionProgramDatedRelativeSource
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
  (C:UnitCost)

local notation "tree" => Halo.bios (P.stepData E Γ per k)
local notation "draw" => directive (P.stepData E Γ per k)
local notation "op" => P.readyKin E Γ K per k
local notation "intake" => See.before P k (Z k.prev)
local notation "rel" => WilsonPositionProgramRelativeClock.relative C (T.cloth k.prev)
local notation "card" => P.records E Γ per k.next

include law in
theorem occupied (t:ℕ)(ht:t≤r)(x:fieldDir G (Γ.S.side (P.vol k.next) per) 1):
    See.noseC S u (T.cloth k.next) (Z k.next) t x=
    born (born (Orbit.words op tree draw intake r (S.fire u)) C 0 r) rel 0 r t x := by
  let axis:=Orbit.words op tree draw intake r (S.fire u)
  let tally:=∑ v∈(S.fire u).val, costAll (intake).power v
  let g:ℕ→ℤ:=fun i=>(i:ℤ)+2+tally
  have enough:Charge r g axis:=by
    intro i _
    exact mark_read op tree draw intake (r:=r) _ (S.fire u) i (every _ _)
  have grow:Monotone g:=by
    intro x y h
    change (x:ℤ)+2+tally ≤ (y:ℤ)+2+tally
    omega
  exact ((law.walks k).mark_w t ht x).trans (congrFun
    (WilsonPositionProgramRelativeClock.restored r axis g enough grow C (T.cloth k.prev) t ht).symm x)

include law in
theorem quiet (t:ℕ)(ht:t≤r)(x:fieldDir G (Γ.S.side (P.vol k.next) per) 1):
    See.visible S (card).clip (card).path (T.cloth k.next) (Z k.next) t x=
    born (born (Orbit.ground op tree draw intake r) C 0 r) rel 0 r t x-
    born (born (Orbit.ground op tree draw intake r) C 0 r) rel 0 r t 0 := by
  let axis:=Orbit.ground op tree draw intake r
  have eq:=WilsonPositionProgramRelativeClock.restored r axis (fun i=>(i:ℤ)+2)
    (LocalScript.rank op tree draw intake r) (fun a b h=>by change (a:ℤ)+2 ≤ (b:ℤ)+2; omega)
    C (T.cloth k.prev) t ht
  rw [eq]
  exact (law.walks k).proper t ht x

end YM.Integration.WilsonPositionProgramDatedRelativeSource
end
