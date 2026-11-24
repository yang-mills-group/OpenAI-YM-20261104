import YM.Integration.WilsonConditionalTaylorWheelMaskReading
import YM.Integration.WilsonConditionalTaylorWheelMarkedBooking
import YM.Integration.WilsonConditionalTaylorWheelMarkCausality

/-! The actual labeled exponential of an enrolled whole marked program takes
one independently rebooked finite-to-cover step, with the original offsets. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelBookedRoster
open Function Filter Lattice Laurent Exterior Wilson RG Precision Tree Matrix Bloch
open FormalBulk08 Flat Reef Jets Orb Series Next.Free PowerSeries Stationary Lotus Shore
open Work.F03 Work.F05 Work.F08 Mesa Gorge City Cork Rift Lava Kemp Wine Rial Roof Dove
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open PhysicalNext.Repeat.Legato Next.Foundations
open scoped Classical Matrix BigOperators Topology
variable {G:Gauge} (R:Run G) (u:G.ColorIndex)
local notation "V" => R.family.path.levels
set_option quotPrecheck false in
local notation "wood" => (fun i:ℕ=>Flat.routes (R.family.path.levels.clock.op i 0).patch)
set_option quotPrecheck false in
local notation "branches" => (fun i:ℕ=>(R.family.path.levels.blocks i 0).branches)

theorem preserved (N j cap E:ℕ) (A B:Mesa.Pot G) (old:∀i≤E,A i=B i) (e r:ℕ) (he:e≤E):
    WilsonConditionalTaylorWheelMarkedBooking.rebook R u N j cap A e r=
      WilsonConditionalTaylorWheelMarkedBooking.rebook R u N j cap B e r:=by
  let P:=destination V N j
  let W:=Dove.model V wood branches R.metals.O u N (j+1)
  let H:=Wine.scalar u (FormalBulk08.Bank.waken P (wood j) W R.metals.O (branches j))
  change Wine.stamp (Wine.bookH H) (Wine.bookU H) _ e r=Wine.stamp (Wine.bookH H) (Wine.bookU H) _ e r
  exact WilsonConditionalTaylorWheelMarkedBooking.stamp (fun _ _=>rfl) (fun _ _=>rfl) _ _ e r he
    (fun i hi=>WilsonConditionalTaylorWheelMarkCausality.marked P (wood j) W A B R.metals.O (branches j)
       E cap i r (hi.trans he) old)

def Funded (h E:ℕ):Prop:=
  ∀N j,h≤j→j<N→∀q cap,q≤cap→∀(T:Era G ℝ),Auth q T→∀(_a:Loc G 1) e r,e≤E→
    (Mer.verseI V R.metals.O j N q T).2 e r=WilsonConditionalTaylorWheelMarkedBooking.rebook R u N j cap T.2 e r

variable {I:Type} [DecidableEq I] {D:I→ℕ}
include R u in
theorem one (simple:G.Simple) (h E:ℕ) (money:Funded R u h E) (N b j:ℕ) (live:j<b) (upper:b≤N) (lo:h≤j)
    (K k:I→ℕ) (seed:Outerm G D) (well:Wellness k seed) (a:Loc G 1) (cap:ℕ)
    (x:I→ Cover) (S:Finset I) (rank:mass k S≤cap) (f:Pen D S→L[ℝ]ℝ) (e r:ℕ) (he:e≤E):
    let Q:=Gears V R.metals.O K k N b (j+1) seed
    let P:=loose V j
    (tuftV f (levelsO (Gears V R.metals.O K k N b j seed x) S)).2 e r=
      ∑ z:backRow P.L S,scalesK P K S • WilsonConditionalTaylorWheelMarkedBooking.rebook R u N j cap
        (tuftV (WilsonConditionalTaylorWheelMaskReading.probe P S f z) (levelsO (Q (splitQ P x S z)) S)).2 e r:=by
  intro Q P
  have prior:Wellness k Q:=Cog V R.metals.O upper seed well simple R.alloy.B.ratio live
  rw [MeterC V R.metals.O upper seed well simple R.alloy.B.ratio live x]
  rw [show margin V R.metals.O j N K k Q x S=unite P K (fun t=>edV V R.metals.O j N (Q t) k) x S from rfl,
    WilsonConditionalTaylorWheelMaskReading.offset]
  apply Finset.sum_congr rfl
  intro z _
  let s:=splitQ P x S z
  let L:=WilsonConditionalTaylorWheelMaskReading.probe P S f z
  let old:=levelsO (Q s) S
  have ink:Auth (mass k S) old:=placedO (Q s) (prior.level' s) S
  have moved:=Mer.ply_verse V (lt_of_lt_of_le live upper) simple R.alloy.B.ratio ink L
  have billed:=money N j lo (live.trans_le upper) (mass k S) cap rank (tuftV L old) (ink.tuft L) a e r he
  change _ • (tuftV L (Mer.verseI V R.metals.O j N (mass k S) old)).2 e r=_
  rw [moved,billed]
end YM.Integration.WilsonConditionalTaylorWheelBookedRoster
end
