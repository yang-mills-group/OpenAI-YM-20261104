import YM.RegulatorIR.Skein.Fees

/-!
# Response curve. First held-leg vehicle and tariffs
Row in earlier measures carries seam to adjacent sites. Include all color.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Skein
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Train Pupil
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries
variable {I X Y W:Type}{t n p s e:ℕ}{v u:ℝ≥0∞}
-- Loom fan. Uses joint height matrices F
section Loom
variable [Fintype W] {F:X→ Packet W p}{K: X→ W→ Y→ℝ}
variable (T:Tariff I)(z:X→I)(y:Y→I) (c:ℝ≥0∞)
def tileS (K:X→ W→Y→ℝ) (T:Tariff I)(z:X→I)(y:Y→I)(c:ℝ≥0∞): Prop:=
   ∀ w:W,Layer.row (fun x=>K x w) T z y c ∧ Layer.row (fun y x=>K x w y) T y z c
variable {T z y c}
variable (h: tileS K T z y c)
include h

local notation "A" => T.uses y
omit [Fintype W] in
lemma weave (i:Fin p)(q:Y)(t:Tuple W p) (x:X): plotK (fun x=> Gain.thread (K x) t) T z y i q x ≤
    (‖K x (t i) q‖ₑ*T.road (y q) (z x))*∏ _∈ univ.erase i,c:=by
 let f(k:Fin p)(v:Y):=‖K x (t k) v‖ₑ*T.road (z x) (y v)
 let P:= (Premium.rooted T (z x)).uses y
 have he(p':Tuple Y p): ‖Gain.thread (K x) t p'‖ₑ*P.width p'≤∏ i,f i (p' i):=by
    unfold f; rw [Finset.prod_mul_distrib]; refine mul_le_mul' ?_ (lap_road T ..)
    have hz(l:Finset (Fin p)): ‖∏ i∈l,K x (t i) (p' i)‖ₑ=∏ i∈l,‖K x (t i) (p' i)‖ₑ:=by induction l using Finset.induction_on with
     | empty=>simp
     | insert i l h ih=>rw [prod_insert h,prod_insert h,enorm_mul,ih]
    exact (hz univ).le
 unfold plotK quota; apply le_trans (b:=∑' v:Hold i q, ∏ j,f j (v.val j)) (ENNReal.tsum_le_tsum (fun t=>he _))
 rw [show (∑' v:Hold i q,_)=_ from family_hold f i (·=q)]
 have heq : (∑' v:{v:Y//v=q},f i v.val)= f i q:=by
    haveI : Subsingleton {v:Y//v=q}:= ⟨fun a b=> Subtype.ext (a.property.trans b.property.symm)⟩; exact tsum_eq_single (b:= (⟨q,rfl⟩:{v:Y//v=q})) (fun a ha=> (ha (Subsingleton.elim ..)).elim)
 rw [heq,T.symm (y q)]; apply mul_le_mul_right; exact prod_le_prod' (fun i _=> ((h (t i)).1 x))
-- p>0; pay lifts by card*M. combine symmetry.Hp may access repeated.
lemma wool (j:Fin (s+1))(q:Y)(u:ℝ≥0∞)(F:X→Packet W (s+1))(H:∀ x,quota (F x) 1≤u):
    (∑' x, plotK (fun x=>loom (F x) (K x)) T z y j q x) ≤ Fintype.card (Tuple W (s+1))*u*c^(s+1):=by
 let S:= Finset.univ.erase j;let d(x:X)(p:Tuple W (s+1)):= ‖K x (p j) q‖ₑ*T.road (y q) (z x)
 have he(x:X): plotK (fun x=>loom (F x) (K x)) T z y j q x ≤ ∑ p:Tuple W _,u*(d x p*c^s):=by
    unfold plotK; dsimp only; let V(t: Hold j q):=((Premium.rooted T (z x)).uses y).width t.val
    rw [show (fun p:Hold j q=>loom (F x) (K x) p.val)= ∑ i:Tuple W _, fun z:Hold j q=>F x i * Gain.thread (K x) i z.val from ?_]; swap
    · ext1 t;unfold loom; simp_rw [Finset.sum_apply];rfl
    apply (quota_sum ..).trans;apply Finset.sum_le_sum; intro i _;rw [quota_times]
    apply mul_le_mul';exact (le_trans (by simpa using term_le (F x) 1 i) (H x)) -- check
    have hp:S.card=s:=by unfold S;rw [Finset.card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]; omega
    exact (weave (K:=K) (c:=c) h j q i x).trans_eq (by -- h missing
       rw [Finset.prod_const,show (Finset.univ.erase j).card=s from hp])
 apply le_trans (ENNReal.tsum_le_tsum he); rw [Summable.tsum_finsetSum (fun i _=> ENNReal.summable)]; let g:= u*c^(s+1)
 apply le_trans (b:=∑ _ :Tuple W (s+1),g)
 · apply Finset.sum_le_sum; intro i _; rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right];apply mul_le_mul_right; rw [pow_succ,mul_comm (c^s)]; apply mul_le_mul_left ((h _).2 q)
 rw [sum_const,card_univ,nsmul_eq_mul]; apply le_of_eq; rw [mul_assoc]
lemma fabric (F:X→Packet W (s+1))(H:∀ x,quota (F x) 1≤u)(x:X) : markQ ((Premium.rooted T (z x)).uses y) (loom (F x) (K x))≤u*c^(s+1):=(loom_cost (F x) (K x) T (z x) y (fun i=> (h i).1 x)).trans (mul_le_mul_left (H x) _)
end Loom
section Lens
variable {G:Gauge} {D:Layer (Foot G) (Foot G)} {V:Gain.Bride G} 
variable {l p:ℝ}{b:ℕ}(h:0<l)(hP:l ≤ p)
local notation "B"=> Tariff.native p (h.trans_le hP) b
-- `tubeL` indexed by Lift.Point.G.H.X.θ.Color count repeat.
lemma colB (c d:ℝ≥0∞)(z:Foot G→Room)(hh:row (swap D) (Tariff.native p (h.trans_le hP) b) z (localL l) c)(hp:row (swap V) (Tariff.native p (h.trans_le hP) b) z (Gain.pointS l) d)(i:Mood G)(t:Foot G):
 quota (fun x:Foot G=> tubeL D V x.1 i t) (fun x=> (B).road (z t) (localL l x)) ≤ c*Fintype.card G.ColorIndex + d * 2^b * (4*Fintype.card G.ColorIndex):=by
 let f(i:Mood G)(x:Edge Cover)(v:G.ColorIndex):= ‖tubeL D V x i t‖ₑ*(B).road (z t) (localL l (x,v))
 have hx(i):quota (fun x:Foot G=> tubeL D V x.1 i t) (fun x=>(B).road (z t) (localL l x)) = ∑' v:G.ColorIndex,∑' x:Edge Cover,f i x v:=by
    unfold quota; rw [ENNReal.tsum_prod'];exact ENNReal.tsum_comm
 rcases i with ⟨i,e⟩
 let M:=Fintype.card G.ColorIndex
 have hr(v v' : G.ColorIndex)(q: Edge Cover): localL l (q,v)=localL l (q,v'):=rfl
 let g(x:Gain.Point G):= ‖V x t‖ₑ*(B).road (z t) (Gain.pointS l x)
 have hb: (∑' u:Cover,g (u,e))≤d:= le_trans (ENNReal.tsum_comp_le_tsum_of_injective (f:=fun i:Cover=>(i,e)) (fun i j h=> Prod.mk.inj h|>.1) g) (hp t) -- signature
 have hp(u:Edge Cover)(v:G.ColorIndex): f (1,e) u v≤g (u.1,e)*2^b:=by
    change ‖V _ _‖ₑ* (B).road _ (localL l (u,v))≤ _; unfold g; rw [mul_assoc]; apply mul_le_mul_right
    let p:= pointS l ((u.1,e):Gain.Point G); apply ((B).tri _ p _).trans
    rw [(B).symm p]; apply mul_le_mul_right
    have hy : dist (localL l (u,v)) p=l/2:= rate₁ h (u,v); rw [show (B).road _ p= _ from congr_arg (Tariff.amount _ _) hy];exact sector_move h hP
 have hm(u:Edge Cover)(v:G.ColorIndex): f (2,e) u v ≤ g (u.1+step u.2,e)*2^b:=by
    change ‖V _ _‖ₑ* (B).road _ (localL l (u,v))≤ _; unfold g; rw [mul_assoc];apply mul_le_mul_right
    let p:=pointS l ((u.1+step u.2,e):Gain.Point G); apply ((B).tri _ p _).trans; rw [(B).symm p]; apply mul_le_mul_right
    have hy : dist (localL l (u,v)) p=l/2:= rate₂ h (u,v); rw [show (B).road _ p= _ from congr_arg (Tariff.amount _ _) hy];exact sector_move h hP
 have hz:(∑' v:G.ColorIndex,∑' x:Edge Cover,g (x.1,e)*2^b)≤d*2^b*(4*M):=by
    have ht:(∑' x:Edge Cover,g (x.1,e)*2^b) ≤ (4:ℝ≥0∞)*(d*2^b):=by
       change (∑' x:Cover × Axis,g (x.1,e)*2^b) ≤ _;rw [ENNReal.tsum_prod']; simp_rw [tsum_fintype,sum_const,nsmul_eq_mul, card_univ,Fintype.card_fin,ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]; norm_num; exact mul_le_mul_right (mul_le_mul_left hb _) _ -- norm_num
    rw [tsum_fintype,sum_const,nsmul_eq_mul]; apply le_trans (mul_le_mul_right ht _); rw [card_univ]; apply le_of_eq; change (M:ℝ≥0∞)*_= _;ring
 rw [hx]; fin_cases i
 · apply le_trans _ (le_self_add (a:=c*Fintype.card G.ColorIndex)); rw [tsum_fintype]; apply le_trans _ (show (∑ _ : G.ColorIndex,c) ≤ _ from by rw [sum_const, nsmul_eq_mul,card_univ,mul_comm]); apply sum_le_sum; intro i _;apply le_trans _ (hh t)
   let F(v:Edge Cover):=(v,e); let p(x:Foot G):= ‖D x t‖ₑ*(B).road (z t) (localL l x); have hl: (∑' v:Edge Cover,p (F v))≤ quota (swap D t) (fun x=> (B).road (z t) (localL l x)):= ENNReal.tsum_comp_le_tsum_of_injective (f:=F) (fun _ _ h=>Prod.mk.inj h |>.1) p
   exact le_trans (le_of_eq rfl) hl -- defeq local L v ignores color
 · exact le_trans (ENNReal.tsum_le_tsum fun i=> ENNReal.tsum_le_tsum fun u=> hp u i) (hz.trans le_add_self)
 let E : Equiv.Perm (Edge Cover):={ toFun:=fun x=>(x.1+Lattice.step x.2,x.2),invFun:=fun x=>(x.1-step x.2,x.2),left_inv:= fun x=>by simp,right_inv:=fun x=>by simp }
 let P:=(∑' v:G.ColorIndex,∑' x:Edge Cover,g ((E x).1,e)*2^b)
 apply le_trans (b:=P) (ENNReal.tsum_le_tsum fun i=> ENNReal.tsum_le_tsum fun x=>hm x i); apply le_trans _ (hz.trans le_add_self)
 unfold P; apply ENNReal.tsum_le_tsum;intro i;exact ((E).tsum_eq (fun x=>g (x.1,e)*2^b)).le
end Lens
end YM.RegulatorIR.Skein
