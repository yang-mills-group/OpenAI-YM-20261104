import YM.AllOrder.Iron.Press
import YM.Next.STATIONARY.Joint.FourPoint
import YM.Next.STATIONARY.Joint.HaarJac
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Iron
open Lattice Laurent RG Filter Tree Metric Finset Function Gauge Matrix Module
open Exterior Wilson Precision Tree MeasureTheory Stationary
open scoped Matrix BigOperators Topology Classical ContDiff InnerProductSpace Matrix.Norms.Frobenius ENNReal
variable {G:Gauge}{c f:Side}{S:StepData c f} (F:Forest S.ratio)(t:S.Choices) {p:Clip}{R:PathData G}

open Work.F05
local notation "C"=> cash (helmets G c f)
abbrev Cou (G:Gauge) (c f:Side):= Bodies G c f→ ℝ
local notation "W"=> Cou G c f
variable (i: G.ColorIndex)
abbrev link (b:Edge (Site f)): W:= Pi.single (.inl (paintLink b i)) 1
def seed (F:Forest S.ratio) (i:G.ColorIndex)(x:Site f): W:= if h:leaf S.ratio x then
      (if (F.up x).neg then -(link i ((F.up x).used x):W) else link i ((F.up x).used x)) + seed F i (x+(F.up x).vec)
      else -Pi.single (.inr (S.ratio.parent x,vac,i)) 1
termination_by F.height x
decreasing_by exact F.rise x h
lemma seed_gauge (a:BaseSites G f)(x:Site f): dotProduct (seed F i x) (stood S (1:Joint G c f)*ᵥ a) = gaugeColor a x i:=by
 rw [Stationary.stands]; let X:= corps S (1:Joint G c f) a; have hx:= (soldier_mounted S (1:Joint G c f) a)
 induction x using Forest.hike.induct F with
 | case1 x hh ih=>
    rw [seed,dif_pos hh,add_dotProduct, ih]
    rcases hp:F.up x with ⟨b,_|_⟩
    · simp only [Bool.false_eq_true,↓reduceIte,link,single_dotProduct,one_mul]
      rw [helmets_link,hx.1,cant_at]; simp [Step.vec,Step.used]
    · change dotProduct (-_) _+_= _; rw [neg_dotProduct,link,single_dotProduct,one_mul,helmets_link,hx.1,cant_at]; simp [Step.used,Step.vec,← sub_eq_add_neg]
 | case2 x hx'=>
    rw [seed,dif_neg hx',neg_dotProduct,single_dotProduct,one_mul,helmets_site,hx.2,← (show x=S.ratio.embed _ from Classical.not_not.mp hx')]; simp
lemma seed_empty (a: AxisChart G F)(x:Site f): dotProduct (seed F i x) (rangers F G *ᵥ (cash (countingBasis F G) a))=0:=by
 rw [rangers,bill_at]; induction x using Forest.hike.induct F with
 | case1 x hh ih=>
    let z:= (F.up x).used x; have hp: dotProduct (link (c:=c) i z) (C (pad F a,0))=0:= by
       rw [link,single_dotProduct, one_mul,helmets_link]; let Z: ↥F.trunks:= ⟨z,F.trunk_mem_iff _ |>.mpr ⟨x,hh,rfl⟩⟩; have he:= pad_trunk F a Z; exact congr_arg (fun v:G.Color=>v i) he
    rw [seed,dif_pos hh,add_dotProduct, ih,add_zero]; split; rw [neg_dotProduct]; exact (congr_arg Neg.neg hp).trans (neg_zero ..); exact hp
 | case2 x hx=> rw [seed,dif_neg hx,neg_dotProduct,single_dotProduct,one_mul,helmets_site]; simp

def graces : Matrix (Key F G) (Bodies G c f) ℝ:= Matrix.of fun i z=> (link i.2 i.1.val - seed F i.2 i.1.val.1 + seed F i.2 (i.1.val.1+step i.1.val.2) : W) z
lemma grace_turn : graces F (G:=G)*stood S (1:Joint G c f)=0:=by
  apply Stationary.bill_eq (pocket _); intro v; rw [cash_pocket]; rw [← Matrix.mulVec_mulVec, zero_mulVec]; funext x; change dotProduct _ _=_; unfold graces; change dotProduct ((_:W)-_+_) _=_; rw [add_dotProduct,sub_dotProduct, seed_gauge, seed_gauge, link, single_dotProduct,one_mul, Stationary.stands,helmets_link,(soldier_mounted S _ v).1,cant_at]; simp
lemma grace_lift : graces F (G:=G)*rangers F G=1:= by
   apply Stationary.bill_eq (countingBasis F G); intro v; rw [← Matrix.mulVec_mulVec, one_mulVec]; funext x; change dotProduct ((_:W)-_+_) _=_; rw [add_dotProduct,sub_dotProduct,seed_empty,seed_empty,link,single_dotProduct,one_mul, rangers,bill_at,helmets_link,rangers_fee]; simp [show edgeColor (pad F v) x.1.val=v x.1 from pad_free F v x.1]
end YM.AllOrder.Iron
