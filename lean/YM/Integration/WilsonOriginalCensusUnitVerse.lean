import YM.Integration.WilsonReceivedFixedDigitCanonical
import YM.Integration.WilsonReceivedCanonicalSocketLevels

/-! Scalarized occupied and deleted proper rows on the actual finite and covering Wilson course. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusUnitVerse
open Function Finset Lattice RG Wilson
open Precision Laurent Source Labels Marker WilsonCoeffUV.Embroider WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding
open WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Bank
open WilsonReceivedFixedDigitHistory
open scoped BigOperators Classical

variable {G:Gauge}{I:Type}[DecidableEq I][Fintype I]{h k:I→ℕ}

abbrev observed (M:family G h)(A:Case h)(s:Finset I):Era G ℝ:=
  tuftV (touch A s) (levelsO M s)

theorem reflected (Y Z:Era G ℝ){a b:ℕ}(pay:Auth a Y)(fee:Auth b Z)
    (allBoards:∀n,flash (Y.1 n)=flash (Z.1 n)):Y=Z:=by
  apply Auth.ext pay fee
  funext n
  exact by_flash (pay.span n) (fee.span n) (fun i=>pay.pale n i)
    (fun i=>fee.pale n i) (allBoards n)

theorem scaled (V:Levels G)(O:ChartRatio G){m N a:ℕ}(live:m<N)
    (simple:G.Simple)(ratio:LocalRatio O){X:Era G ℝ}(fee:Auth a X)(d:ℝ):
    verseI V O m N a (d • X)=d • verseI V O m N a X:=by
  simpa only [Finset.sum_singleton] using verse_sum V (Ñ:=O)
    (P:=fun _:Unit=>X) simple live ratio (S:={()}) (fun _ _=>fee) (fun _=>d)

theorem step (V:Levels G)(O:ChartRatio G){m N:ℕ}(live:m<N)(simple:G.Simple)
    (ratio:LocalRatio O)(M:family G h)(sound:Eu k M)(A:Case h)(s:Finset I):
    observed (logO V O m N M k) A s=verseI V O m N (mass k s) (observed M A s):=by
  unfold observed
  rw [step_S V O m N M k live simple ratio sound]
  exact ply_verse V live simple ratio (placedO M sound s) (touch A s)

theorem age (V:Levels G)(O:ChartRatio G)(N:ℕ)(digit:Digits V I)
    (simple:G.Simple)(ratio:LocalRatio O)(seed:Outerm G h)(sound:Wellness k seed)
    (A:Case h)(s t:Finset I)(same:mass k s=mass k t)(d:ℝ)
    (atBirth:∀x,observed (seed x) A s=d • observed (seed x) A t)
    (days m:ℕ)(live:m+days≤N)(x:I → Cover):
    let Y:=itinerary V O k N digit days m seed x
    observed Y A s=d • observed Y A t:=by
  induction days generalizing m x with
  | zero=>exact atBirth x
  | succ days ih=>
    let older:=itinerary V O k N digit days (m+1) seed
    let y:=chartIn (loose V m) x (digit m)
    have well:=WilsonReceivedFixedDigitHistory.sound V O k N digit simple ratio seed sound days (m+1) (by omega : m+1+days≤N)
    have original:=ih (m+1) (by omega) y
    change observed (logO V O m N (older y) k) A s=d • observed (logO V O m N (older y) k) A t
    rw [step V O (by omega) simple ratio _ (well.level' y) A s,
      step V O (by omega) simple ratio _ (well.level' y) A t,same,original]
    exact scaled V O (by omega) simple ratio ((placedO _ (well.level' y) t).tuft _) d

end YM.Integration.WilsonOriginalCensusUnitVerse
