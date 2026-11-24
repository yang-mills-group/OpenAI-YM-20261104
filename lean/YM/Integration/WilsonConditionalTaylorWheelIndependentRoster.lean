import YM.Integration.WilsonConditionalTaylorWheelBookedRoster

/-! The entire moment of a labeled mask at every physical age is computed by
an independent recursive FVA2 transfer, from the authentic terminal source.
Every spatial root offset and authenticated running clock is inside the recursion. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelIndependentRoster
open Function Filter Lattice Laurent Exterior Wilson RG Precision Tree Matrix Bloch
open FormalBulk08 Flat Reef Jets Orb Series Next.Free PowerSeries Stationary Lotus Shore
open Work.F03 Work.F05 Work.F08 Mesa Gorge City Cork Rift Lava Kemp Wine Rial Roof Dove
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open PhysicalNext.Repeat.Legato Next.Foundations
open WilsonConditionalTaylorWheelMaskReading WilsonConditionalTaylorWheelMarkedBooking
open scoped Classical Matrix BigOperators Topology
variable {G:Gauge} {I:Type} [DecidableEq I] {D:I→ℕ}
variable (R:Run G) (u:G.ColorIndex)
local notation "V" => R.family.path.levels

def moments (N cap:ℕ) (K:I→ℕ) (seed:Outerm G D):
    (d j:ℕ)→(I→ Cover)→(S:Finset I)→(Pen D S→L[ℝ]ℝ)→Mesa.Pot G
  | 0,_,x,S,f => (tuftV f (levelsO (seed x) S)).2
  | d+1,j,x,S,f =>
    let P:=loose V j
    ∑ z:backRow P.L S,scalesK P K S • rebook R u N j cap
      (moments N cap K seed d (j+1) (splitQ P x S z) S (probe P S f z))

theorem descend (simple:G.Simple) (h E:ℕ) (paid:WilsonConditionalTaylorWheelBookedRoster.Funded R u h E)
    (N b cap:ℕ) (upper:b≤N) (K k:I→ℕ) (seed:Outerm G D) (well:Wellness k seed) (a:Loc G 1) (d:ℕ):
    ∀j,h≤j→j+d=b→∀(x:I→ Cover)(S:Finset I),mass k S≤cap→∀(f:Pen D S→L[ℝ]ℝ)(e r:ℕ),e≤E→
      (tuftV f (levelsO (Gears V R.metals.O K k N b j seed x) S)).2 e r=
        moments R u N cap K seed d j x S f e r:=by
  induction d with
  | zero=>
    intro j _ date x S _ f e r _
    obtain rfl:j=b:=by omega
    rw [gearTop]
    rfl
  | succ d ih=>
    intro j lo date x S rank f e r he
    have live:j<b:=by omega
    have step:=WilsonConditionalTaylorWheelBookedRoster.one R u simple h E paid N b j live upper lo K k seed well a cap x S rank f e r he
    refine step.trans ?_
    simp only [moments,Finset.sum_apply,Pi.smul_apply]
    apply Finset.sum_congr rfl
    intro z _
    congr 1
    apply WilsonConditionalTaylorWheelBookedRoster.preserved R u N j cap E _ _ _ e r he
    intro i hi
    funext l
    exact ih (j+1) (by omega) (by omega) _ S rank _ i l hi

variable (simple:G.Simple)
variable (tags:∀i n,(primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
include simple tags in
theorem purchased (money:WilsonConditionalTaylorVacuumWindingDeposit.Extra R.kit)
    (period:RG05Preconstruction.ReadoutPurchase R.b) (E:ℕ):
    ∀ᶠh:ℕ in atTop,∀ N b j:ℕ,h≤j→j≤b→b≤N→∀(K k:I→ℕ)(seed:Outerm G D),Wellness k seed→
      ∀(_a:Loc G 1)(cap:ℕ)(x:I→ Cover)(S:Finset I),mass k S≤cap→∀(f:Pen D S→L[ℝ]ℝ)(e r:ℕ),e≤E→
      (tuftV f (levelsO (Gears V R.metals.O K k N b j seed x) S)).2 e r=
        moments R u N cap K seed (b-j) j x S f e r:=by
  filter_upwards [WilsonConditionalTaylorWheelMarkedBooking.purchased R simple u tags money period E] with h cash N b j lower live upper K k seed well a cap x S rank f e r cut
  exact descend R u simple h E cash N b cap upper K k seed well a (b-j) j lower (by omega) x S rank f e r cut
end YM.Integration.WilsonConditionalTaylorWheelIndependentRoster
end
