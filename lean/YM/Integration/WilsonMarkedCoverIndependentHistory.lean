import YM.Integration.WilsonMarkedCoverIndependentStep
import YM.Integration.WilsonConditionalTaylorWheelMaskReading

/-! Complete cover recursion for every occupied subset of a funded Wilson roster. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedCoverIndependentHistory
open Function Filter Lattice Laurent Exterior Wilson RG Precision Tree Matrix Bloch
open FormalBulk08 Flat Reef Jets Orb Series Next.Free PowerSeries Stationary Lotus Shore
open Work.F03 Work.F05 Work.F08 Mesa Gorge City Cork Rift Lava Kemp Wine Rial Roof Dove
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open PhysicalNext.Repeat.Legato Next.Foundations
open scoped Classical Matrix BigOperators Topology
variable {G:Gauge} {I:Type} [DecidableEq I] {D:I→ℕ}
open WilsonConditionalTaylorWheelMaskReading (probe offset)
open FormalBulk08.Shore FormalBulk08.Mesa

variable (R:Run G)(u:G.ColorIndex)
local notation "V" => R.family.path.levels
variable (tags:∀i n,(FormalBulk08.Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)

def moments (N cap:ℕ)(K:I→ℕ)(seed:Outerm G D):
    (d j:ℕ) → (I → Cover) → (S:Finset I) → (Pen D S→L[ℝ]ℝ) → Pot G
  | 0,_,x,S,f => (tuftV f (levelsO (seed x) S)).2
  | d+1,j,x,S,f =>
    let P:=loose V j
    ∑ z:backRow P.L S,scalesK P K S • WilsonMarkedCoverIndependentStep.fixed R u N j cap
      (moments N cap K seed d (j+1) (splitQ P x S z) S (probe P S f z))

include tags in
theorem descend (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (N b cap:ℕ)(upper:b≤N)(K k:I→ℕ)(seed:Outerm G D)(well:Wellness k seed)(a:Loc G 1)(d:ℕ):
    ∀j,j+d=b→∀(x:I → Cover)(S:Finset I),mass k S≤cap→∀(f:Pen D S→L[ℝ]ℝ),
    (tuftV f (levelsO (Gears V R.metals.O K k N b j seed x) S)).2=moments R u N cap K seed d j x S f:=by
  induction d with
  | zero=>
    intro j date x S _ f
    obtain rfl:j=b:=by omega
    rw [gearTop]
    rfl
  | succ d ih=>
    intro j date x S cost f
    funext e r
    have live:j<b:=by omega
    let P:=loose V j
    let Q:=Gears V R.metals.O K k N b (j+1) seed
    have valid:Wellness k Q:=Cog V R.metals.O upper seed well simple R.alloy.B.ratio live
    rw [MeterC V R.metals.O upper seed well simple R.alloy.B.ratio live x]
    rw [show margin V R.metals.O j N K k Q x S=unite P K (fun t=>edV V R.metals.O j N (Q t) k) x S from rfl,WilsonConditionalTaylorWheelMaskReading.offset]
    simp only [moments,Finset.sum_apply,Pi.smul_apply]
    apply Finset.sum_congr rfl
    intro z _
    congr 1
    let s:=splitQ P x S z
    let L:=probe P S f z
    let old:=levelsO (Q s) S
    have ink:Mer.Auth (mass k S) old:=placedO (Q s) (valid.level' s) S
    have moved:=Mer.ply_verse V (lt_of_lt_of_le live upper) simple R.alloy.B.ratio ink L
    have prev:(tuftV L old).2=moments R u N cap K seed d (j+1) s S L:=
      ih (j+1) (by omega) s S cost L
    have one:=WilsonMarkedCoverIndependentStep.original R u tags simple v funded
      (live.trans_le upper) (mass k S) cap cost (tuftV L old) (ink.tuft L) a
    have next:=congrArg (WilsonMarkedCoverIndependentStep.fixed R u N j cap) prev
    change (tuftV L (Mer.verseI V R.metals.O j N (mass k S) old)).2 e r=_
    rw [moved]
    exact congrFun (congrFun (one.trans next) e) r

include tags in
theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    {N b j:ℕ}(live:j≤b)(upper:b≤N)(K k:I→ℕ)(seed:Outerm G D)(well:Wellness k seed)(a:Loc G 1)
    (x:I → Cover)(S:Finset I)(cap:ℕ)(cost:mass k S≤cap)(f:Pen D S→L[ℝ]ℝ):
    (tuftV f (levelsO (Gears V R.metals.O K k N b j seed x) S)).2=
      moments R u N cap K seed (b-j) j x S f:=
  descend R u tags simple v funded N b cap upper K k seed well a (b-j) j (by omega) x S cost f

end YM.Integration.WilsonMarkedCoverIndependentHistory
end
