import YM.Integration.WilsonConditionalTaylorWheelConnectedCausality
import YM.Integration.WilsonConditionalTaylorWheelIndependentRoster

/-! The independently propagated connected field of the complete labeled
tuple agrees at every high date with the originally marked WUV program.
Only the given terminal mask data, independent Wick transfers and the
genuine finite set logarithm occur in the prescription. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelConnectedRoster
open Function Filter Lattice Laurent Exterior Wilson RG Precision Tree Matrix Bloch
open FormalBulk08 Flat Reef Jets Orb Series Next.Free PowerSeries Stationary Lotus Shore
open Work.F03 Work.F05 Work.F08 Mesa Gorge City Cork Rift Lava Kemp Wine Rial Roof Dove
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open PhysicalNext.Repeat.Legato Next.Foundations
open WilsonConditionalTaylorWheelIndependentRoster WilsonConditionalTaylorWheelConnectedReadout
open scoped Classical Matrix BigOperators Topology
variable {G:Gauge} {I:Type} [DecidableEq I] {D:I→ℕ}
variable (R:Run G) (u:G.ColorIndex)
local notation "V" => R.family.path.levels

def connected (N cap:ℕ) (K:I→ℕ) (seed:Outerm G D) (d j:ℕ) (x:I→ Cover) (A:Case D) (S:Finset I):Mesa.Pot G:=
  logged (fun J=>moments R u N cap K seed d j x J (touch A J)) S

variable (simple:G.Simple)
variable (tags:∀i n,(primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
include simple tags in
theorem purchased (money:WilsonConditionalTaylorVacuumWindingDeposit.Extra R.kit)
    (period:RG05Preconstruction.ReadoutPurchase R.b) (E:ℕ):
    ∀ᶠh:ℕ in atTop,∀ N b j:ℕ,h≤j→j≤b→b≤N→∀(K k:I→ℕ)(seed:Outerm G D),Wellness k seed→
      ∀(_a:Loc G 1)(cap:ℕ)(x:I→ Cover)(S:Finset I),mass k S≤cap→∀(A:Case D)(e r:ℕ),e≤E→
        pPly A S (Gears V R.metals.O K k N b j seed x S).2 e r=connected R u N cap K seed (b-j) j x A S e r:=by
  filter_upwards [WilsonConditionalTaylorWheelIndependentRoster.purchased (I:=I) (D:=D) R u simple tags money period E] with h cash N b j lower live upper K k seed well a cap x S rank A e r bound
  let T:=Gears V R.metals.O K k N b j seed
  have health:Wellness k T:=Cog V R.metals.O upper seed well simple R.alloy.B.ratio live
  have identify:=WilsonConditionalTaylorWheelConnectedReadout.original (T x) k (health.level' x) (health.quiet' x) A S
  have old:∀J⊆S,∀i≤E,read A J (levelsO (T x) J) i=moments R u N cap K seed (b-j) j x J (touch A J) i:=by
    intro J sub i hi
    funext l
    have fee:mass k J≤ mass k S:=Finset.sum_le_sum_of_subset sub
    exact cash N b j lower live upper K k seed well a cap x J (fee.trans rank) (touch A J) i l hi
  have loggedEq:=WilsonConditionalTaylorWheelConnectedCausality.held E _ _ S old e bound
  exact (congrArg (fun Y:Mesa.Pot G=>Y e r) identify).trans (congrFun loggedEq r)
end YM.Integration.WilsonConditionalTaylorWheelConnectedRoster
end
