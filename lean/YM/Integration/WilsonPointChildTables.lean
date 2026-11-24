import YM.Integration.WilsonPointChildProgram
import YM.Integration.WilsonMarkedCoverIndependentHistory

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildTables
open Function Finset Filter Lattice RG Wilson Gauge Precision PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Soil
open Next.Free Stationary Next.Foundations PhysicalNext.Repeat.Legato
open WilsonPointChildProgram
open WilsonMarkedFiniteIndependentHistory (probe)
open scoped BigOperators Classical Topology
variable {G:Gauge}{I:Type}[DecidableEq I]{D k:I→ℕ}
variable (R:Run G)(u:G.ColorIndex)
local notation "V" => R.family.path.levels
variable (tags:∀i n,(FormalBulk08.Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)

/-- Finite and covered independently contracted histories at the fixed
microscopic residue of each sample grid. -/
def finite (N:ℕ)(d:I→ℕ)(X:Outerm G D)(s:I):
    (h j:ℕ)→(I → Cover)→(Pen D {s}→L[ℝ]ℝ)→(n:Side)→PChart G n
  | 0,_,x,f,n=>(tuftV f (X x {s})).1 n
  | h+1,j,x,f,n=>
    let P:=loose V j
    (P.L.val:ℝ)^(d s) • WilsonMarkedFiniteIndependentStep.fixed R u tags N j n
      (finite N d X s h (j+1) (splitQ P x {s} 0) (probe P {s} f 0) (n*P.L))

def covered (N cap:ℕ)(d:I→ℕ)(X:Outerm G D)(s:I):
    (h j:ℕ)→(I → Cover)→(Pen D {s}→L[ℝ]ℝ)→FormalBulk08.Mesa.Pot G
  | 0,_,x,f=>(tuftV f (X x {s})).2
  | h+1,j,x,f=>
    let P:=loose V j
    (P.L.val:ℝ)^(d s) • WilsonMarkedCoverIndependentStep.fixed R u N j cap
      (covered N cap d X s h (j+1) (splitQ P x {s} 0) (probe P {s} f 0))

theorem finite_history (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (N:ℕ)(d:I→ℕ)(X:Outerm G D)(base:Wellness k X)(s:I)(h j:ℕ)(live:j+h≤N)
    (x:I → Cover)(f:Pen D {s}→L[ℝ]ℝ)(n:Side):
    (tuftV f (history V R.metals.O N d k X h j x {s})).1 n=finite R u tags N d X s h j x f n:=by
  induction h generalizing j x f n with
  | zero=>rfl
  | succ h ih=>
    let P:=loose V j
    let Y:=history V R.metals.O N d k X h (j+1)
    let z:=splitQ P x {s} 0
    let g:=probe P {s} f 0
    have step:j<N:=by omega
    have ok:=lawful V R.metals.O N (j+1) h (by omega) simple R.alloy.B.ratio d X base
    have read:=WilsonMarkedIndependentNormalizedRecursion.singleton V R.metals.O j N step
      simple R.alloy.B.ratio (Y z) (ok.level' z) (ok.quiet' z) s
    have auth:=ok.level' z {s}
    have moved:=Mer.ply_verse V step simple R.alloy.B.ratio auth g
    have one:=WilsonMarkedFiniteIndependentStep.original R u tags simple v funded N j (mass k {s})
      step (tuftV g (Y z {s})) (auth.tuft g) n
    have prev:=ih (j+1) (by omega) z g (n*P.L)
    rw [show WilsonPointChildProgram.history V R.metals.O N d k X (h+1) j=next V R.metals.O N j d k Y from rfl]
    funext a r
    change (tuftV f (plant P d (fun y=>logO V R.metals.O j N (Y y) k) x {s})).1 n a r=_
    rw [WilsonPointChildProgram.observed]
    change engineering P d {s} • (tuftV g (logO V R.metals.O j N (Y z) k {s})).1 n a r=_
    rw [read,moved,one]
    change engineering P d {s} • (WilsonMarkedFiniteIndependentStep.fixed R u tags N j n
      ((tuftV g (Y z {s})).1 (n*P.L))) a r=_
    change (tuftV g (Y z {s})).1 (n*P.L)=_ at prev
    rw [prev,engineering,Finset.prod_singleton]
    rfl

include tags in
theorem cover_history (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (N cap:ℕ)(d:I→ℕ)(X:Outerm G D)(base:Wellness k X)(s:I)(cost:mass k {s}≤cap)
    (loc:Loc G 1)(h j:ℕ)(live:j+h≤N)(x:I → Cover)(f:Pen D {s}→L[ℝ]ℝ):
    (tuftV f (history V R.metals.O N d k X h j x {s})).2=covered R u N cap d X s h j x f:=by
  induction h generalizing j x f with
  | zero=>rfl
  | succ h ih=>
    let P:=loose V j
    let Y:=history V R.metals.O N d k X h (j+1)
    let z:=splitQ P x {s} 0
    let g:=probe P {s} f 0
    have step:j<N:=by omega
    have ok:=lawful V R.metals.O N (j+1) h (by omega) simple R.alloy.B.ratio d X base
    have read:=WilsonMarkedIndependentNormalizedRecursion.singleton V R.metals.O j N step simple
      R.alloy.B.ratio (Y z) (ok.level' z) (ok.quiet' z) s
    have auth:=ok.level' z {s}
    have moved:=Mer.ply_verse V step simple R.alloy.B.ratio auth g
    have one:=WilsonMarkedCoverIndependentStep.original R u tags simple v funded step (mass k {s}) cap cost
      (tuftV g (Y z {s})) (auth.tuft g) loc
    have prev:=ih (j+1) (by omega) z g
    funext e r w
    change f (engineering P d {s} • (mend P (inflate P {s} 0) D {s})
      ((logO V R.metals.O j N (Y z) k {s}).2 e r w))=_
    rw [map_smul]
    change engineering P d {s} • (tuftV g (logO V R.metals.O j N (Y z) k {s})).2 e r w=_
    rw [read,moved,one]
    change (tuftV g (Y z {s})).2=_ at prev
    rw [prev,engineering,Finset.prod_singleton]
    rfl

end YM.Integration.WilsonPointChildTables
end
