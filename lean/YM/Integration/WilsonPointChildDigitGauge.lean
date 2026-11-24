import YM.Integration.WilsonPointChildDigitFinite
import YM.Integration.WilsonMarkedOriginalGaugeLaw
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildDigitGauge
open YM FormalBulk08 Lattice RG Laurent Next.Foundations PhysicalNext.Repeat.Legato
open Reef Flat Stationary Dawn Pose Kemp Palm Shore Mesa Wine Quire Roof Lotus Sierra Gorge Dove Rial
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Winding
open WilsonPointChildTestCoordinates WilsonNeutralPointCourse WilsonPointChildCoverStep
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped ContDiff BigOperators Topology Classical
variable {G:Gauge}{d D:ℕ}
variable (R:Run G)(u:G.ColorIndex)(depth:d<D)
variable (digit:∀i,Site (R.family.S.block i))
variable (tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)

open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Winding WilsonCoeffUV.Blue
open WilsonCoeffUV.Power FormalBulk08.Lotus FormalBulk08.Kemp FormalBulk08.Reef
open WilsonPointChildDigitLedger
open WilsonPointChildDigitFinite (table)

theorem translated {n:Side}(x:Site n)(Y:PChart G n)(stop:Blue.shellK d Y)
    (ward:Rite (flash Y) (flash Y) 1 0):Rite (flash (skewV x Y)) (flash (skewV x Y)) 1 0:=by
  have same:(jog x:Equiv.Perm (Woods G n))=Lotus.tint x:=by
    apply Equiv.ext; intro t
    change (x+t.1,t.2)=(t.1+x,t.2)
    rw [add_comm x t.1]
  have record:flash (skewV x Y)=Kemp.resite x (flash Y):=by
    rw [show flash (skewV x Y)=_ from translate_value n x Y stop,loom_spear,same]
    rfl
  rw [record]
  simpa using (Kemp.repulp x (1:Signed) (flash Y) (flash Y) ward)

include tags in
theorem original (simple:G.Simple)(o:Loc G 1)(price:ℕ→Gear G→ℝ)
    (paid:FundedMarkedCoverRows.prices price R.kit)(N h j:ℕ)(live:j+h≤N)
    (v:Letter (R.family.labels.level d))(p:Scroll D)(n:Side):
    let Z:=flash ((ledger R u depth digit N h j v p).1 n)
    Rite Z Z 1 0:=by
  induction h generalizing j v p n with
  | zero=>
    have top:=Roof.topC o (R.family.labels.level d) (R.family.localSection d) R.family.params (R.makes.sections d) (Next.Foundations.valuation G d) depth
    have birth:=((solo_iff ..).mp (clef_through (top.officers v) (slotsFits _ v)).ward) n (physical p)
    change Rite (flash (Shore.rancho _)) (flash (Shore.rancho _)) 1 0
    simpa only [WilsonPointChildFiniteWard.recorded] using birth
  | succ h ih=>
    let V:=R.family.path.levels
    let P:=WilsonCoeffUV.loose V j
    let F:=fun s=>ledger R u depth digit N h (j+1) s (growWord P (digit j) D p)
    let y:=wrap (n*P.L) (lift (digit j))
    have paidTerm(s:Letter (R.family.labels.level d)):=WilsonPointChildFiniteWard.step R u tags simple price paid
      (N:=N) (j:=j) (by omega) n (skewV y ((F s).1 (n*P.L)))
      (translated y ((F s).1 _) ((honest R u depth digit simple o N h (j+1) (by omega) s _).span _)
        (ih (j+1) (by omega) s _ _)) (P.L.val^d)
    have same(s:Letter (R.family.labels.level d)): (F s).1 (n*P.L)=table R u depth digit tags N h (j+1) s (growWord P (digit j) D p) (n*P.L):=
      WilsonPointChildDigitFinite.original R u depth digit tags simple o price paid N h (j+1) (by omega) s _ _
    change Rite (flash ((ledger R u depth digit N (h+1) j v p).1 n)) (flash ((ledger R u depth digit N (h+1) j v p).1 n)) 1 0
    rw [WilsonPointChildDigitFinite.original R u depth digit tags simple o price paid N (h+1) j live v p n]
    simp only [table,WilsonPointChildFiniteWard.recorded]
    intro U i a b g ha hb ca cb gauge constant localEq
    simp only [map_sum,map_mul,Wine.worm_roam]
    apply Finset.sum_congr rfl
    intro s hs
    have res:=paidTerm s U a b g ha hb ca cb gauge constant localEq
    rw [same] at res
    rw [res]
end YM.Integration.WilsonPointChildDigitGauge
