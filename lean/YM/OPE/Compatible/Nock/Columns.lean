import YM.OPE.Compatible.Nock.Beachy
/-!
# Arithmetic in three jet slots. division only by units in callers. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Cascade
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency
open PertExtension Series Asymptotics GaussianScore Radial Finset
abbrev Token:= JetS ℝ
namespace JetS
@[simp] lemma ml_s (a b:Token):(a*b).s=a.s*b.s:= rfl
@[simp] lemma ml_l (a b:Token):(a*b).l=a.s*b.l+a.l*b.s:= rfl
@[simp] lemma ml_h (a b:Token):(a*b).h=a.s*b.h+a.l*b.l+a.h*b.s:= rfl
@[simp] lemma pl_s (a b:Token):(a+b).s=a.s+b.s:= rfl
@[simp] lemma pl_l (a b:Token):(a+b).l=a.l+b.l:= rfl
@[simp] lemma pl_h (a b:Token):(a+b).h=a.h+b.h:= rfl
@[simp] lemma sp_s (a:Token):(a⁻¹).s=a.s⁻¹:=rfl
@[simp] lemma sp_l (a:Token):(a⁻¹).l= -(a.l / a.s^2):=by change -a.l/a.s^2=_; ring
@[simp] lemma sp_h (a:Token):(a⁻¹).h=a.l^2/a.s^3 - a.h/a.s^2:=rfl
@[simp] lemma o_s : (1:Token).s=1:=rfl
@[simp] lemma o_l : (1:Token).l=0:=rfl
@[simp] lemma o_h : (1:Token).h=0:=rfl
@[simp] lemma z_s : (0:Token).s=0:=rfl
@[simp] lemma z_l : (0:Token).l=0:=rfl
@[simp] lemma z_h : (0:Token).h=0:=rfl
instance : CommRing (JetS ℝ) where
    add_assoc a b c:= by apply eta <;> simp [add_assoc]
    add_comm a b:=by apply eta<;> simp [add_comm]
    zero_add a:=by apply eta <;> simp
    add_zero a:=by apply eta<;> simp
    nsmul:= nsmulRec
    zsmul := zsmulRec
    neg_add_cancel a := by apply eta; change -_+_= (_:ℝ); exact neg_add_cancel _; exact neg_add_cancel a.l; exact neg_add_cancel a.h
    mul_assoc a b c:=by apply eta<;> simp only [ml_s,ml_l,ml_h] <;> ring
    mul_comm a b:=by apply eta <;> simp only [ml_s,ml_l,ml_h] <;> ring
    one_mul a:=by apply eta <;> simp only [ml_s,ml_l,ml_h,o_s,o_l,o_h] <;>ring
    mul_one a:=by apply eta <;> simp only [ml_s,ml_l,ml_h,o_s,o_l,o_h] <;>ring
    left_distrib a b c:=by apply eta <;>simp only [ml_s,ml_l,ml_h,pl_s,pl_l,pl_h] <;>ring
    right_distrib a b c:=by apply eta <;>simp only [ml_s,ml_l,ml_h,pl_s,pl_l,pl_h] <;>ring
    zero_mul a:=by apply eta <;> simp
    mul_zero a:=by apply eta <;> simp
-- divide relates, lemma names distinct
lemma dv (a b:Token): a/b=a*b⁻¹:=rfl
lemma uniting {p:Token}(he: p.s≠0): p⁻¹*p=1:=by apply eta <;> simp only [ml_s,ml_l,ml_h,o_s,o_l,o_h,sp_s,sp_l,sp_h]<;> field_simp <;>ring
def plainJ (c:ℝ):Token:=⟨c,0,0⟩
@[simp] lemma plain_s (c:ℝ): (plainJ c).s=c:=rfl
@[simp] lemma plain_l (c:ℝ): (plainJ c).l=0:=rfl
@[simp] lemma plain_h (c:ℝ): (plainJ c).h=0:=rfl
lemma plain_full (a:ℝ)(k:Token): plainJ a*k=a • k:= by apply eta <;>simp only [ml_s,ml_l,ml_h,plain_s,plain_l,plain_h,zero_mul,add_zero] <;> rfl
lemma transfer (x a p:Token)(hx:x.s≠0)(h:p.s≠0): (x*a)/(x*p)=a/p := by
     have hy:(x*p).s≠0:=by rw [ml_s]; exact mul_ne_zero hx h
     rw [dv, dv]; calc
          x*a*(x*p)⁻¹=(x*p)⁻¹ *(x*a*(p⁻¹*p)):= by rw [uniting h];ring
          _=(a*p⁻¹)*((x*p)⁻¹*(x*p)):=by ring
          _= _:=by rw [uniting hy,mul_one]
end JetS
end YM.OPE.Libra
