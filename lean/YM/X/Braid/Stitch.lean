import YM.X.Grow.Solid
/-!
# Wick ⋆ composition. internal connections of any size. Split single and multiple hits, identities. Derivatives commute.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Braid
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter MeasureTheory Metric Finsupp
open scoped Topology ContDiff BigOperators Classical
variable {V W:Type*} (Q : Symmetric V)
local notation "P"=> Normal.poly V
local notation "R"=> V →₀ ℂ
lemma miles (p:P): milk Q (milk (-Q) p)=p:= by rw [warms, Symmetric.cancels,froze] -- orientation warm
lemma minus (p:P): milk (-Q) (milk Q p)=p:= by rw [warms,show -Q+Q=0 from Symmetric.ext (neg_add_cancel Q.cov),froze]
def knot (p q:P):= milk Q (milk (-Q) p * milk (-Q) q)
lemma gen_pair (p q:P): milk Q (p*q)=knot Q (milk Q p) (milk Q q):= by rw [knot,minus,minus]
lemma pmul (p q:P): milk (-Q) (knot Q p q)=milk (-Q) p * milk (-Q) q:= by rw [knot,minus]
lemma pcomm (p q:P):knot Q p q= knot Q q p:= by unfold knot; rw [mul_comm] --  (mul_comm (milk (-Q) p) (milk (-Q) q))
lemma passoc (p q x:P):knot Q (knot Q p q) x=knot Q p (knot Q q x):= by unfold knot; rw [minus,minus,mul_assoc]
lemma passoc' (p q x:P): knot Q p (knot Q q x)=knot Q q (knot Q p x):= by rw [← passoc, pcomm Q p q, passoc]
lemma padd (p q x:P):knot Q (p+q) x= knot Q p x+knot Q q x:= by unfold knot;rw [_root_.map_add,add_mul,map_add]
lemma padd' (p q x:P):knot Q p (q+x)=knot Q p q+knot Q p x:= by rw [pcomm,padd,pcomm Q p q,pcomm Q p x]
lemma pscale (a:ℂ)(p q:P):knot Q (a • p) q=a • knot Q p q:= by unfold knot; rw [map_smul,smul_mul_assoc,map_smul]
lemma pscale' (a:ℂ)(p q:P):knot Q p (a • q)=a • knot Q p q:= by rw [pcomm,pscale,pcomm Q p q]
def oral : P →ₗ[ℂ] P →ₗ[ℂ] P:= LinearMap.mk₂ ℂ (knot Q) (padd Q) (pscale Q) (padd' Q) (fun a x y=>pscale' Q a x y)
lemma oral_point (p q:P): oral Q p q=knot Q p q:= rfl
@[simp] lemma pzero (p:P): knot Q 0 p=0:= by simp [knot]
@[simp] lemma pzero' (p:P):knot Q p 0=0:= by simp [knot]
@[simp] lemma pone (p:P): knot Q 1 p=p:= by simp [knot,miles]
@[simp] lemma pone' (p:P): knot Q p 1=p:= by simp [knot,miles]
lemma psub (p q x:P): knot Q (p-q) x=knot Q p x-knot Q q x:= map_sub ((oral Q).flip x) p q
lemma psub' (p q x:P): knot Q p (q-x)=knot Q p q-knot Q p x:= map_sub (oral Q p) ..
lemma psum {I:Type*}(t:Finset I)(f:I→P)(p:P): knot Q (∑ i∈t,f i) p=∑ i∈t,knot Q (f i) p:= map_sum ((oral Q).flip p) f t
lemma pc (a:ℂ)(p:P): knot Q (C a) p=a • p:= by simp only [knot,fine,C_mul',map_smul,miles]

def edge (x:R):= slit (Finsupp.linearCombination ℂ Q.cov x)
def corner (x y:R):= treats Q x y
lemma link_g {x:R}(f:V→ℂ): slit f (glyph x)=C (Finsupp.linearCombination ℂ f x) := by
   induction x using Finsupp.induction_linear with
   | zero=> simp
   | add a b h h'=> simp only [_root_.map_add,h,h']
   | single i c=> rw [glyph,Finsupp.linearCombination_single,Finsupp.linearCombination_single,(slit f).map_smul,slit_X,← C_mul',smul_eq_mul,map_mul] -- need smul=mul
lemma link (x y:R): edge Q x (glyph y)= C (treats Q x y):= link_g _
lemma edge_line (x:R)(p:P) : knot Q (glyph x) p= glyph x * p+edge Q x p:= by
   have ht (Q:Symmetric V) (i:P): milk Q (glyph x*i)=glyph x*milk Q i+edge Q x (milk Q i):= refresh ..
   have he: milk (-Q) (glyph x)= glyph x:= by simpa only [Normal.pure,mul_one,Derivation.map_one_eq_zero,add_zero] using ht (-Q) 1 -- names
   rw [knot,he,ht,miles]
lemma skimmers (f:V→ℂ)(p q:P): slit f (knot Q p q)=knot Q (slit f p) q + knot Q p (slit f q):= by
   unfold knot; rw [skims,(slit f).leibniz]; simp only [smul_eq_mul,map_add,skims]; rw [add_comm,mul_comm (milk (-Q) q)]
lemma pstep (x:R)(f p:P): knot Q (glyph x*f) p=glyph x*knot Q f p+knot Q f (edge Q x p):= by
   rw [show glyph x*f=knot Q (glyph x) f-edge Q x f by rw [edge_line]; abel, psub,passoc,edge_line,edge,skimmers]; abel

-- one-line between these two groups ONLY

def hit (p:P):= MvPolynomial.mkDerivation ℂ (fun i:V=> slit (Q.cov i) p)
lemma hit_point (p:P)(i:V): hit Q p (X i)= slit (Q.cov i) p:= by simp [hit]
lemma hit_zero (p:P): hit Q p 0=0:= map_zero _
lemma hit_c (p:P)(i:ℂ): hit Q p (C i)=0:=Derivation.map_algebraMap ..
lemma hit_add (p q:P): hit Q (p+q)=hit Q p+hit Q q:= by ext i;rw [hit_point]; simp only [Derivation.add_apply,map_add]; rw [hit_point,hit_point]
lemma hit_scale (a:ℂ)(p:P):hit Q (a • p)= a • hit Q p:= by ext i; simp [hit_point]
lemma hit_glyph (p:P)(x:R):hit Q p (glyph x)= edge Q x p:= by
    induction x using Finsupp.induction_linear with
    | zero=> rw [map_zero,map_zero,edge,map_zero,slit_zero]
    | add a b h g=> unfold edge at *; rw [_root_.map_add,_root_.map_add,h,g,map_add, slit_linear]
    | single i c=> rw [glyph,edge,Finsupp.linearCombination_single,Finsupp.linearCombination_single,(hit Q p).map_smul, slit_smul, hit_point]
lemma hit_slit (f:V→ℂ)(p q:P): slit f (hit Q p q)=hit Q (slit f p) q+hit Q p (slit f q):= by
   induction q using MvPolynomial.induction_on with
   | C a=> rw [hit_c,map_zero,hit_c,slit_C,map_zero,zero_add]
   | add p' q h g=> simp only [_root_.map_add,h,g];abel
   | mul_X q i h=> rw [mul_comm q, (hit Q p).leibniz]; simp only [_root_.map_add,_root_.map_smul, Derivation.leibniz,smul_eq_mul,hit_point,h,slit_X,hit_c]; rw [slit_slit f]; ring
lemma dual (x:P):LinearMap.id («R»:=ℂ) (M:=P) x=x:= rfl -- remove

def multi (p q:P) := knot Q p q-p*q-hit Q p q
lemma m_op (p q:P) : knot Q p q = p*q+hit Q p q+ multi Q p q:= by unfold multi; ring -- implicit
lemma madd₀(p q x:P): multi Q p (q+x)=multi Q p q+multi Q p x:= by unfold multi;rw [padd',mul_add,map_add];ring
lemma madd(p q x:P): multi Q (q+x) p=multi Q q p + multi Q x p:= by unfold multi; rw [padd,add_mul,hit_add]; simp only [Derivation.add_apply]; ring
lemma mscale (a:ℂ)(p q:P):multi Q p (a • q)=a • multi Q p q:= by unfold multi;rw [pscale',mul_smul_comm,(hit Q p).map_smul,smul_sub,smul_sub]
lemma mscale' (a:ℂ)(p q:P):multi Q (a • p) q=a • multi Q p q:= by unfold multi;rw [pscale,smul_mul_assoc,hit_scale,smul_sub,smul_sub];rfl
def toned : P →ₗ[ℂ] P→ₗ[ℂ] P:= LinearMap.mk₂ ℂ (multi Q) (fun i j k=> madd Q _ _ _) (mscale' Q) (madd₀ Q) (fun a x y=>mscale Q a x y)
lemma mno (p:P):multi Q p 1=0:= by rw [multi,pone',mul_one,sub_self, Derivation.map_one_eq_zero]; simp
lemma mzero (p:P): multi Q p 0 =0:= map_zero (toned Q p)
lemma mg (p:P)(x:R):multi Q p (glyph x)=0:= by unfold multi; rw [hit_glyph,pcomm,edge_line,mul_comm];abel
lemma ms (f:V→ℂ)(p q:P): slit f (multi Q p q)= multi Q (slit f p) q + multi Q p (slit f q):= by unfold multi; simp only [map_sub, skimmers,hit_slit, Derivation.leibniz,smul_eq_mul]; ring
lemma mstep (x:R)(p q:P): multi Q p (glyph x*q)=glyph x*multi Q p q+hit Q (edge Q x p) q+multi Q (edge Q x p) q:= by unfold multi; rw [pcomm Q p,pstep, (hit Q p).leibniz]; simp only [pcomm Q q _,smul_eq_mul,hit_glyph];ring -- simp comm potential
lemma m2 (x y:R)(p:P):multi Q p (glyph x*glyph y)=edge Q y (edge Q x p):= by rw [mstep,mg,mg,hit_glyph]; ring
lemma m3(x y z:R)(p:P) : multi Q p (glyph x* (glyph y*glyph z))= (glyph x*edge Q z (edge Q y p) + glyph y*edge Q z (edge Q x p) + glyph z*edge Q y (edge Q x p)) +edge Q z (edge Q y (edge Q x p)):= by rw [mstep,m2,m2,(hit Q _).leibniz]; simp only [smul_eq_mul,hit_glyph]; ring
end YM.PositionX.Braid
