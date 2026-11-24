import YM.Integration.WilsonThermometerUnitFilingWeakReadback
import YM.Integration.WilsonThermometerUnitFilingPinned

/-! Exact source that the native positional ordinary program reads at capture. Each occupied slot takes its own true child at each level; the original root test and its engineering factor travel with that choice. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingBranches
open Function Filter Finset Lattice Laurent RG Precision Wilson Input WilsonCoeffUV
open WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Shard WilsonCoeffUV.Embroider
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonThermometerUnitFilingWeakReadback WilsonThermometerUnitFilingPinned
open scoped Classical BigOperators
variable {G:Gauge} {ι W:Type} [DecidableEq ι] {D:ι→ℕ}
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

def roster (A:Levels G)(K:ι→ℕ)(b v:ℕ)(X:Outerm G D)(p:Note D W):Era G W:=
  if live:v<b then ∑j:backRow (ll A v).L p.face,roster A K b (v+1) X (child (ll A v) K p j)
    else hear p X
termination_by b-v
decreasing_by omega

theorem top (A:Levels G)(K:ι→ℕ)(b:ℕ)(X:Outerm G D)(p:Note D W):
    roster A K b b X p=hear p X:=by rw [roster,dif_neg (lt_irrefl _)]

theorem step (A:Levels G)(K:ι→ℕ)(b v:ℕ)(X:Outerm G D)(p:Note D W)(live:v<b):
    roster A K b v X p=∑j:backRow (ll A v).L p.face,roster A K b (v+1) X (child (ll A v) K p j):=by
  rw [roster,dif_pos live]

variable [CompleteSpace W]

omit [CompleteSpace W] in
theorem issued (A:Levels G)(K k:ι→ℕ){b v h:ℕ}(X:Outerm G D)(stock:Wellness k X)
    (vb:v≤b)(p:Note D W)(cap:mass k p.face ≤h):Auth h (roster A K b v X p):=by
  induction vb using Nat.decreasingInduction generalizing p with
  | self=>
    rw [top]
    exact ((((placedO (X p.site) (stock.level' p.site) p.face).tuft p.test).μ p.factor).tall cap)
  | of_succ i live ih=>
    rw [step _ _ _ _ _ _ live]
    exact Auth.sum (fun j _=>ih (child (ll A i) K p j) cap)

theorem original (A:Levels G)(O:ChartRatio G)(K k:ι→ℕ){N b v h:ℕ}(simple:G.Simple)
    (ratio:LocalRatio O)(bn:b≤N)(vb:v≤b)(X:Outerm G D)(stock:Wellness k X)(p:Note D W)
    (cap:mass k p.face≤h):
    hear p (Gears A O K k N b v X) = march A O N b v h (roster A K b v X p):=by
  induction vb using Nat.decreasingInduction generalizing p with
  | self=>rw [WilsonThermometerUnitFilingPinned.top,top,gearTop _ _ _]
  | of_succ i live ih=>
    rw [WilsonThermometerUnitFilingWeakReadback.original A O K k N b i bn live X stock simple ratio p h cap,
      WilsonThermometerUnitFilingPinned.step _ _ _ _ _ _ _ live,step _ _ _ _ _ _ live,
      WilsonThermometerUnitFilingPinned.sum A O simple ratio bn (Nat.succ_le_of_lt live) _
        (fun j=>issued A K k X stock (Nat.succ_le_of_lt live) (child (ll A i) K p j) cap)]
    apply congrArg (verseI A O i N h)
    exact sum_congr rfl (fun j _=>ih (child (ll A i) K p j) cap)

end YM.Integration.WilsonThermometerUnitFilingBranches
