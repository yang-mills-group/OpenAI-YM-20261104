import YM.Integration.WilsonThermometerOriginalFilmRows
import YM.Integration.WilsonThermometerFilmClock

/-! The first signed ordinary and centered vacuum coefficients at a native chronological step. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerOriginalFilmStep
open Function Filter Finset Lattice Wilson Exterior Precision Tree Marker Multi
open Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Adjacent Comparison.RG02.Symmetry
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Binding RegulatorIR.Geometry
open PertExtension.Series PertExtension.Series.Tested Booth Pipeline Period.Field RG
open WilsonThermometerOriginalCoveredRows YM.Primitives.GCC.Anchor
open scoped Classical Topology BigOperators
variable {G:Gauge} {I:Type} [DecidableEq I] [Fintype I] {X:Type} {j:X→ℕ} {n:Page j→Side}
  {Q:KernelChoices} {Γ:RG.History G} {E:Circuit j n} (K:Bulk.Chain Γ) (P:SeriesT E Q Γ)
  (S:Census I) (u:I) (L:Page j→Binding.Scale) (per r:ℕ) (T:See.Times L r)
  (k:Flap j) (W:Colors S G (Γ.S.side (P.vol k.prev) per)) (W':Colors S G (Γ.S.side (P.vol k.next) per))
  (post:See.Task K P S u (p:=per) L r T k W W') (live : 0 < r) (D:BudgetPoint) (legal:Bulk.Well W)

local notation "ker" => P.readyKin E Γ K per k
local notation "tree" => Halo.bios (P.stepData E Γ per k)
local notation "draw" => directive (P.stepData E Γ per k)
local notation "incoming" => See.before P k W
local notation "clk" => T.cloth k.prev
local notation "drift" => -deriv (clk).rating 0
local notation "m" y:max=> base ker tree draw incoming y
local notation "h" y:max=> first ker tree draw incoming y

def old (x:fieldDir G (Γ.S.side (P.vol k.next) per) 1) := (Extra.Trajectories.connected (m x)).part (S.fire u)
def slope (x:fieldDir G (Γ.S.side (P.vol k.next) per) 1) :=
  ((h x)*inverseMass (m x)-Poly.bead S ((h x).part S.quiet)).part (S.fire u)

omit [Fintype I] in
include legal in
private theorem admitted : Bulk.Well incoming :=
  See.poster (fun i (c:Colors S G (Γ.S.side i per))=>Bulk.Well c) W (P.links k) legal

include post live D legal in
theorem marked (x:fieldDir G (Γ.S.side (P.vol k.next) per) 1) :
    See.noseC S u (T.cloth k.next) W' 0 x=old K P S u per k W x ∧
    See.noseC S u (T.cloth k.next) W' 1 x=slope K P S u per k W x+
      fderiv ℝ (old K P S u per k W) x (drift • x) := by
  have well:=admitted P S per k W legal
  have sheet:=Orbit.colored ker D tree draw incoming r (S.fire u) well
  have at0 : Orbit.words ker tree draw incoming r (S.fire u) 0=old K P S u per k W :=
    funext fun y=>(WilsonThermometerOriginalFilmRows.occupied ker tree draw incoming r live (S.fire u) y).1
  have at1:=(WilsonThermometerOriginalFilmRows.occupied ker tree draw incoming r live (S.fire u) x).2
  constructor
  · exact (post.mark_w 0 (Nat.zero_le _) x).trans ((WilsonThermometerOriginalClockSlope.zeroth _ clk r x).trans (congrFun at0 x))
  · have s₁:=WilsonThermometerFilmClock.first (Orbit.words ker tree draw incoming r (S.fire u)) clk r live
      (fun q hq=>(sheet.known q hq).differentiable (by simp)) x
    rw [at0,at1] at s₁
    exact (post.mark_w 1 live x).trans s₁

include post live D legal in
theorem vacuum (x:fieldDir G (Γ.S.side (P.vol k.next) per) 1) :
    let card:=P.records E Γ per k.next
    See.visible S card.clip card.path (T.cloth k.next) W' 0 x=
      Symmetry.price ker tree draw x-Symmetry.price ker tree draw 0 ∧
    See.visible S card.clip card.path (T.cloth k.next) W' 1 x=
      (h x).part S.quiet+fderiv ℝ (Symmetry.price ker tree draw) x (drift • x)-(h 0).part S.quiet := by
  have well:=admitted P S per k W legal
  have sheet:=Orbit.bed ker D tree draw incoming r well
  have at0 : Orbit.ground ker tree draw incoming r 0=Symmetry.price ker tree draw :=
    funext fun y=>(WilsonThermometerOriginalFilmRows.quiet ker tree draw incoming r live y).1
  have zero (y):born (Orbit.ground ker tree draw incoming r) clk 0 r 0 y=Symmetry.price ker tree draw y :=
    (WilsonThermometerOriginalClockSlope.zeroth _ clk r y).trans (congrFun at0 y)
  have firstAt (y):born (Orbit.ground ker tree draw incoming r) clk 0 r 1 y=
      (h y).part S.quiet+fderiv ℝ (Symmetry.price ker tree draw) y (drift • y) := by
    have s₁:=WilsonThermometerFilmClock.first (Orbit.ground ker tree draw incoming r) clk r live
      (fun q hq=>(sheet.known q hq).differentiable (by simp)) y
    rwa [at0,(WilsonThermometerOriginalFilmRows.quiet ker tree draw incoming r live y).2] at s₁
  constructor
  · exact (post.proper 0 (Nat.zero_le _) x).trans (congrArg₂ (·-·) (zero x) (zero 0))
  · simpa only [smul_zero,map_zero,add_zero] using
      (post.proper 1 live x).trans (congrArg₂ (·-·) (firstAt x) (firstAt 0))

end YM.Integration.WilsonThermometerOriginalFilmStep
