import YM.Integration.WilsonMarkedFiniteIndependentStep
import YM.WilsonCoeffUV.Emit.RentedCapture

/-! Every ordinary face in the actual finite marked history agrees with the independent unaliased
recursion on all finite sides. Each step retains the earlier finite vacuum and every mesh preimage. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedFiniteIndependentHistory
open Function Filter Lattice Laurent Exterior Wilson RG Precision Tree Matrix Bloch
open FormalBulk08 Flat Reef Jets Orb Series Next.Free PowerSeries Stationary Lotus Shore
open Work.F03 Work.F05 Work.F08 Mesa Gorge City Cork Rift Lava Kemp Wine Rial Roof Dove
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open PhysicalNext.Repeat.Legato Next.Foundations
open scoped Classical Matrix BigOperators Topology
variable {G:Gauge} {I:Type} [DecidableEq I] {D:I→ℕ}
def coeff {V:Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f:V→L[ℝ]ℝ) (n:Side) (e r:ℕ) (v:Fin r → Woods G n):Era G V →ₗ[ℝ]ℝ where
  toFun X:=f (X.1 n e r v)
  map_add' X Y:=by change f (_+_)=_;rw [map_add]
  map_smul' c X:=by change f (c • _)=_;rw [map_smul];rfl

def probe (P:Patch) (S:Finset I) (f:Pen D S→L[ℝ]ℝ) (i:backRow P.L S):Pen D S→L[ℝ]ℝ:=
  f.comp (mend P (inflate P S i) D S)

theorem offset (P:Patch) (K:I→ℕ) (X:Outerm G D) (loc:I→ Cover) (S:Finset I) (f:Pen D S→L[ℝ]ℝ)
    (n:Side) (e r:ℕ):
    (tuftV f (unite P K X loc S)).1 n e r=
      ∑ i:backRow P.L S,scalesK P K S •
        (tuftV (probe P S f i) (X (splitQ P loc S i) S)).1 n e r:=by
  funext v
  let measure:=coeff f n e r v
  change measure (∑i:backRow P.L S,portV P K X loc S i)=_
  rw [map_sum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [portV,map_smul]
  rfl
variable (R:Run G) (u:G.ColorIndex)
local notation "V" => R.family.path.levels


open FormalBulk08.Series WilsonCoeffUV.Blue
variable (tags:∀i n,(FormalBulk08.Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)


def moments (N:ℕ) (K:I→ℕ) (seed:Outerm G D):
    (d j:ℕ) → (I → Cover) → (S:Finset I) → (Pen D S →L[ℝ] ℝ) → (n:Side) → PChart G n
  | 0,_,x,S,f,n => (tuftV f (levelsO (seed x) S)).1 n
  | d+1,j,x,S,f,n =>
    let P:=loose V j
    ∑ z:backRow P.L S,scalesK P K S • WilsonMarkedFiniteIndependentStep.fixed R u tags N j n
      (moments N K seed d (j+1) (splitQ P x S z) S (probe P S f z) (n*P.L))

theorem descend (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    {N b:ℕ} (upper:b≤N) (K k:I→ℕ) (seed:Outerm G D) (well:Wellness k seed) (d:ℕ):
    ∀j,j+d=b → ∀(x:I → Cover) (S:Finset I) (f:Pen D S →L[ℝ] ℝ) (n:Side),
    (tuftV f (levelsO (Gears V R.metals.O K k N b j seed x) S)).1 n=
      moments R u tags N K seed d j x S f n:=by
  induction d with
  | zero=>
    intro j date x S f n
    obtain rfl:j=b:=by omega
    rw [gearTop]
    rfl
  | succ d ih=>
    intro j date x S f n
    funext e r
    have live:j<b:=by omega
    let Q:=Gears V R.metals.O K k N b (j+1) seed
    let P:=loose V j
    have valid:Wellness k Q:=Cog V R.metals.O upper seed well simple R.alloy.B.ratio live
    rw [MeterC V R.metals.O upper seed well simple R.alloy.B.ratio live x]
    rw [show margin V R.metals.O j N K k Q x S=unite P K (fun t=>edV V R.metals.O j N (Q t) k) x S from rfl,
      offset]
    simp only [moments,Finset.sum_apply,Pi.smul_apply]
    apply Finset.sum_congr rfl
    intro z _
    congr 1
    let s:=splitQ P x S z
    let L:=probe P S f z
    let old:=levelsO (Q s) S
    have ink:Mer.Auth (mass k S) old:=placedO (Q s) (valid.level' s) S
    have moved:=Mer.ply_verse V (lt_of_lt_of_le live upper) simple R.alloy.B.ratio ink L
    have prev:(tuftV L old).1 (n*P.L)=moments R u tags N K seed d (j+1) s S L (n*P.L):=
      ih (j+1) (by omega) s S L _
    have one:=WilsonMarkedFiniteIndependentStep.original R u tags simple v funded N j (mass k S)
      (live.trans_le upper) (tuftV L old) (ink.tuft L) n
    have next:=congrArg (WilsonMarkedFiniteIndependentStep.fixed R u tags N j n) prev
    change (tuftV L (Mer.verseI V R.metals.O j N (mass k S) old)).1 n e r=_
    rw [moved]
    exact congrArg (fun T:PChart G n=>T e r) (one.trans next)

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    {N b j:ℕ} (live:j≤b) (upper:b≤N) (K k:I→ℕ) (seed:Outerm G D) (well:Wellness k seed)
    (x:I → Cover)(S:Finset I)(f:Pen D S→L[ℝ]ℝ)(n:Side):
    (tuftV f (levelsO (Gears V R.metals.O K k N b j seed x) S)).1 n=
      moments R u tags N K seed (b-j) j x S f n:=
  descend R u tags simple v funded upper K k seed well (b-j) j (by omega) x S f n

end YM.Integration.WilsonMarkedFiniteIndependentHistory
end
