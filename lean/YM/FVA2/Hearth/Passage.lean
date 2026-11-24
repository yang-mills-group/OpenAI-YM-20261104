import YM.FVA2.Hearth.Reclose
/-! Composition of open evolution and preconditioning a suffix. Keep identical branches
& gauge convention on earlier layers. T.choose.Truss always legal; no early `Splice.enjoy`
operation at the cut point. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Hearth
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter PertExtension Precision Lattice GaussianScore Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb PertExtension.Series Tested Radial Facade PowerSeries
open scoped Classical Topology BigOperators
variable {G:Gauge} {n:Side} {L:Fabric G n} {J:ChartRatio G}

 def stitch {n:Side}(L:Fabric G n)(X:Fabric G (Bottom L)) : Fabric G n:= match L with
 | .endcap _ _=> X
 | .layer S H t f L => layer S H t f (Hearth.stitch L X)

def sew {n:Side}{L:Fabric G n}(T:Cloth L){X:Fabric G (Bottom L)}(v:Cloth X): Cloth (Hearth.stitch L X) :=by
 cases T with
 | floor=> exact v
 | @inLayer c f S H t hf L P C=> exact Cloth.inLayer P (sew (L:=L) C v)
termination_by structural T

def stateCost {n:Side}(L:Fabric G n)(X:Fabric G (Bottom L))(b:L.Cost→PowerSeries ℝ)(f:X.Cost→PowerSeries ℝ) : (Hearth.stitch L X).Cost→PowerSeries ℝ:= match L with
 | .endcap _ _=> f
 | .layer _ _ _ _ L=> fun x=> Option.elim x (b none) (fun i=> stateCost L X (b∘some) f i)

lemma sewn {n:Side}{L: Fabric G n}(T: Cloth L){X: Fabric G (Bottom L)}(v:Cloth X)(w:L.Cost→PowerSeries ℝ)(w':X.Cost→PowerSeries ℝ){U:Unmasked G n}(A: Ticket (Flats G n))(h:Commission J T U w) (p:Commission J (sew T v) U (stateCost L X w w')) :
   ∃ q : Commission J v (drive T w U A J h).1 w', course (sew T v) (stateCost L X w w') U J A p=course v w' (drive T w U A J h).1 J (drive T w U A J h).2 q:= by
 cases T with
 | floor=> exact ⟨p,rfl⟩
 | @inLayer c f S H t hf L P C=> exact sewn C v (w∘some) w' (Broadcast P t J (w none) U (Exists.choose h) (boost (blankRight P) A)) (Exists.choose_spec h) (Exists.choose_spec p)
termination_by structural T
end YM.FVA2.Hearth
namespace YM.FVA2.Hearth
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter PertExtension Precision Lattice GaussianScore Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb PertExtension.Series Tested Radial Facade PowerSeries
variable {G:Gauge} {n:Side} {L:Fabric G n} {J:ChartRatio G}
lemma paymentsBoth {n:Side}(L:Fabric G n)(X:Fabric G (Bottom L))(w:L.Cost→PowerSeries ℝ)(b:X.Cost→PowerSeries ℝ) (h:∀ i,0<term (w i) 0)(hb:∀i,0<term (b i) 0) :∀ i, 0< term (stateCost L X w b i) 0:= by
 cases L with
 | endcap=> exact hb
 | layer S H t hf L=>
    intro i; change Option _ at i; cases i with
                                   | none=> exact h none
                                   | some i=> exact paymentsBoth L X (w∘some) b (fun i=>h (some i)) hb i
termination_by structural L
variable {T:Cloth L}{X:Fabric G (Bottom L)}{v:Cloth X}
 def hybrid (w:L.Accounts→PowerSeries ℝ)(b:X.Cost→PowerSeries ℝ)(i:(Hearth.stitch L X).Accounts): PowerSeries ℝ:= i.elim (w none) (stateCost L X (w ∘ some) b)
variable (w:L.Accounts→PowerSeries ℝ)(b:X.Cost→PowerSeries ℝ)(h:∀ i,0<term (w i) 0)(hb:∀i,0<term (b i) 0)(hj:LocalRatio J)
include h hb
lemma hybrid_paid (i):0<term (hybrid w b i) 0:= Option.recOn i (h none) (paymentsBoth L X (w∘some) b (fun _=>h _) hb)
local notation "F"=> drive T (w ∘ some) (initialFull G n (w none))
local notation "p"=> collared T w hj h
lemma on_suffix (A: Ticket (Flats G n)):
   ∃ q : Commission J v (F A J p).1 b, purchase (sew T v) (hybrid w b) (hybrid_paid w b h hb) hj A=course v b (F A J p).1 J (F A J p).2 q:= sewn T v (w∘some) b A p (by
    have he:= collared (sew T v) _ hj (hybrid_paid w b h hb); exact he)
end YM.FVA2.Hearth
