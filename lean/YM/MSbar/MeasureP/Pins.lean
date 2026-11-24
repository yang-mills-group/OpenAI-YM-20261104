import YM.MSbar.MeasureP.Dusk
import YM.MSbar.Chord.Beds
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Crossing
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Measuring
open Function Filter Lattice Gauge Push Uniform
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
open Whisk RG Precision Next.Free Exterior Laurent Bloch
variable {α β :Type} {G:Gauge}{c n:Side}(g:Ratio c n)
local notation "A"=>Primary n G
local notation "B"=>Primary c G
local notation "L"=>(g.count.val:ℝ)
variable (P : Cross g.count (TypeFace 1) (TypeFace 1))
def chart (c:Side)(G:Gauge) (x:Primary c G) := x.1.1
def pension (G:Gauge)(l:List Axis) (x:Primary n G)(v:Primary c G) := if v.2=x.2 then installed g (advanceC _ P l) x.1 v.1 else 0
noncomputable def grot (G:Gauge)(η:ℝ)(p:ℕ)(x:Site n)(i:Primary c G):=factor η p (2*separation x (g.embed i.1.1)/L)
noncomputable def treasure (G:Gauge)(η:ℝ)(p:ℕ)(x:Primary n G)(i:Primary c G):= grot g G η p x.1.1 i
local notation "K₁"=>pension g P G
variable {D p:ℕ}{a b η r C E:ℝ} {h l: List Axis}
local notation "φ"=>factor a p
variable (x:Primary n G)(v:Primary c G)(j:Site n)
lemma grot_positive(i:Primary c G)(x:Site n):0 < grot g G a p x i:=by unfold grot factor; positivity
lemma rocks (ha:4*a≤η)(hb:0≤a)(hE:0≤E)(h:∀ x : ℝ,0≤x→(1+x)^p ≤ E*Real.exp (η/4*x)): grot g G a p j v ≤ E*crossW g η j v.1.1:=by
    let X:=(separation j (g.embed v.1.1):ℝ)/L; have hx:0≤X:=by unfold X; positivity
    change factor a p _ ≤ E*Real.exp (η*X); rw [mul_div_assoc]; change factor a p (2*X)≤ _; unfold factor
    refine (mul_le_mul_of_nonneg_right (h (2*X) (by positivity)) (Real.exp_pos _).le).trans ?_; rw [mul_assoc,←Real.exp_add]; gcongr; nlinarith only [mul_le_mul_of_nonneg_right ha hx]
lemma crown(h: (advanceC _ P l).strip η C)(hi:4*a ≤η)(hb:0≤a)(hE:0 ≤ E)(hh:∀ x:ℝ,0≤x→(1+x)^p≤E*Real.exp (η/4*x)):
    (∑ w:B,treasure g G a p x w*|pension g P G l x w|) ≤ E*Real.exp η*(Fintype.card (TypeFace 1)*C):=by
     rw [Fintype.sum_prod_type]; let i:=x.2; let f:=advanceC _ P l; let K:= installed g f; let X:= x.1.1
     have ht (v':Body 1 c) : (∑ i':G.ColorIndex, treasure g G a p x (v',i')*|K₁ l x (v',i')|)= grot g G a p X (v',i)*‖K x.1 v'‖:=by unfold pension; rw [Finset.sum_eq_single i]; simp [i,treasure,K,X,f]; intro b _ h; rw [if_neg h]; simp; simp
     simp_rw [ht, mul_assoc]; have hx:=mul_le_mul_of_nonneg_left (cross_sprawl g (by linarith only [hi,hb]) h x.1) hE; rw [Finset.mul_sum] at hx; exact le_trans (Finset.sum_le_sum fun i' _=> by rw [←mul_assoc];exact mul_le_mul_of_nonneg_right (rocks g (i',i) X hi hb hE hh) (norm_nonneg _)) hx
lemma coin(h: (advanceC _ P l).strip η C)(hi:4*a ≤η)(hb:0≤a)(hE:0 ≤ E)(hh:∀ x:ℝ,0≤x→(1+x)^p≤E*Real.exp (η/4*x)):
    (∑ w:A,treasure g G a p w v*|pension g P G l w v|) ≤ L^4*(E*Real.exp η*(Fintype.card (TypeFace 1)*C)) :=by
     rw [Fintype.sum_prod_type]; let i:=v.2; let f:=advanceC _ P l; let K:= installed g f
     have ht (v':Body 1 n) : (∑ i':G.ColorIndex, treasure g G a p (v',i') v*|K₁ l (v',i') v|)= grot g G a p v'.1 v*‖K v' v.1‖:=by unfold pension; rw [Finset.sum_eq_single i]; simp [i,treasure,K,f]; intro b _ h; rw [if_neg (Ne.symm h)]; simp; simp
     simp_rw [ht]; have hx:=mul_le_mul_of_nonneg_left (crossColumns g (by linarith only [hi,hb]) h v.1) hE; rw [show E*(Real.exp η*_)= L^4*(E*Real.exp η*(Fintype.card (TypeFace 1)*C)) from ?_,Finset.mul_sum] at hx -- ambiguous dependent
     · exact le_trans (Finset.sum_le_sum fun i' _=> by rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (rocks g v i'.1 hi hb hE hh) (norm_nonneg _)) hx
     ring
-- localized Taylor.L. Earn row closeness without dimension.
namespace Debut
open MultiNext.SignedSource Newt
variable {g}
-- recenter at x.F.Keep tail. axis & tint.Co.W.T.Chart.Scholar.
noncomputable def circle (x:Site n)(y:Primary n G)(z:Cover):Primary n G:= ((wrap n z+x,y.1.2),y.2)
noncomputable def lyrics (g:Ratio c n)(P:Cross g.count (TypeFace 1) (TypeFace 1))(x:Site n)(i:A)(v:B) := fun z:Cover=> pension g P G [] (circle x i z) v
lemma linear(x:Site n)(i:A)(z:Cover)(U:B→ℝ)(l:List Axis)(hp:Odd g.count.val)(h:∀ s: List Axis, s.length≤l.length → Whole (advanceC _ P s)) : Newt.iterate (fun t:Cover=>∑ v:B,lyrics g P x i v t*U v) l z= ∑ v:B, pension g P G l.reverse (circle x i z) v*U v:=by
    let q:Co c (TypeFace 1)→ℝ:=fun v=>U (v,i.2)
    have hv(A':Cross g.count (TypeFace 1) (TypeFace 1))(l:List Axis)(z:Cover) : (∑ v:B, pension g A' G l (circle x i z) v*U v)=load (installed g (advanceC _ A' l)) q (wrap n z+x, i.1.2) :=by
       rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun v' _=> ?_; simp [pension,circle,ite_mul,q]
    rw [show (fun z: Cover=>∑ v:B,lyrics g P x i v z*U v)=(fun z:Cover=>load (installed g P) q (wrap n z+x,i.1.2)) from funext (fun z=> hv P [] z),hv]; exact Newt.spatial g P q l hp h x i.1.2 z
end Debut
end YM.MSbar.Measuring
