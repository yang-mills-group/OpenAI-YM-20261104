import YM.MS.Color.Invol
import YM.MS.KoszulSyms

set_option autoImplicit false
noncomputable section
namespace YM.MS.Lifting
open Function Filter Set Finset Plane Koszul Color Real Momentum Tensor Book
open Local Local.BV Woven Landau Detect Detect.Mark MeasureTheory Submodule
open Complex (I)
open scoped Topology ContDiff BigOperators
variable {G:Gauge} {n:ℕ} {F H:Law G} {b:Bool}
abbrev sense (G:Gauge) : Sector (Lane4 G):= field Landau.parity
lemma riseC (u:G.El) : repeatC u (Koszul.sign (sense G) b F)= Koszul.sign (sense G) b (repeatC u F):= by
    ext w; induction w generalizing F with
    | nil=>simp
    | cons a l ih=>
       simp only [D_eval a, c_prefix,sign_D,map_sum,map_smul,Finset.smul_sum,Finset.sum_apply,Pi.smul_apply]; apply Finset.sum_congr rfl; intro i _; rw [ih]; exact smul_comm .. -- sign local
lemma linkC (u:G.El): repeatC u (product (sense G) F H)= product (sense G) (repeatC u F) (repeatC u H):= by
   ext w; induction w generalizing F H with
   | nil=>simp
   | cons a l ih=>
       simp only [D_eval a, c_prefix, D_product,map_sum,map_add,map_smul,LinearMap.smul_apply, LinearMap.sum_apply, Pi.add_apply, smul_add, Finset.sum_add_distrib,Finset.sum_apply, Pi.smul_apply, ih]; simp_rw [show ∀ i,sense G (setLeg a i)=sense G a from fun i=>rfl,riseC]
lemma over_sign : overC (Koszul.sign (sense G) b F)= Koszul.sign (sense G) b (overC F):= by
   ext w; induction w generalizing F with
   | nil=> simp [over_at,invertMom]
   | cons a w ih=> simp only [D_eval a,over_D,sign_D,map_smulₛₗ,Pi.smul_apply,ih]; cases b <;> cases he:sense G a <;> simp [show sense G (invert a)=sense G a from rfl,he]
lemma over_p : overC (product (sense G) F H)= product (sense G) (overC F) (overC H):= by
   ext w; induction w generalizing F H with
   | nil=> simp only [over_at,invertMom,List.map_nil,nil_product,star_mul']
   | cons a w ih=> simp only [D_eval a,D_product,over_D,map_add,D_product,Pi.add_apply,ih,over_sign]; rfl
lemma ticket (f:Grade G): Koszul.mono f=Local.bud f hit:= by ext l; rcases l with _|⟨a,_|_⟩ <;> simp [Koszul.mono]
lemma overM (f:Grade G): overC (Koszul.mono f)= Koszul.mono (over f):= by rw [ticket,over_bud,ticket]; rw [show overC (G:=G) hit=hit from over_line (n:=0) (fun _=>f)] ; rfl
end YM.MS.Lifting
