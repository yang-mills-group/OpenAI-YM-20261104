import YM.OPE.Compatible.Rail.Track
/-! # Row reshape and acts (branch independent) -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Tree Exterior Stationary Woody
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J Q E:Type*} {G:Gauge}{n m:Side}
namespace Script
-- transport ordinary
open Page
def braidRow (e:I→E)(x:J→Q)(P: Row E Q): Row I J:= fun i j=> P (e i) (x j)
lemma braidP (e:I→E)(x:J→Q)(P:Row E Q)(h: Whole P):Whole (braidRow e x P):=by obtain ⟨s,D,h,hx⟩:=h; exact ⟨s,D,h,fun i j=> hx ..⟩
def laceC (e:I≃J): Tab I n≃Tab J n:= Equiv.prodCongr (Equiv.refl _) e
lemma braidRead (e:I≃E)(x:J≃Q)(V: Row E Q): (braidRow e x V).acts n=(V.acts n).submatrix (laceC e) (laceC x):= by ext; rfl
-- join table general
abbrev Margin (P:Type*) (Q:Type*) := P ⊕ Q -- note: Inhabited
abbrev starI {I:Type*}{J:Type*} (i: Tab I n): Tab (I ⊕ J) n:= (i.1,.inl i.2)
abbrev starJ {I:Type*}{J:Type*}(i:Tab J n): Tab (I⊕J) n:=(i.1,.inr i.2)
def fromMargin : Tab (I⊕J) n≃ (Tab I n ⊕ Tab J n) where
    toFun i:= match i.2 with |.inl a=>.inl (i.1,a)| .inr b=>.inr (i.1,b)
    invFun i:= i.elim starI starJ
    left_inv i:= by rcases i with ⟨i,j|j⟩ <;> rfl
    right_inv i:= by rcases i with i|i<;> rfl
section table
variable [Fintype I][Fintype J]
lemma sumBoard (f: Tab (I⊕J) n→ℝ): (∑ i,f i)=(∑ i,f (starI i))+(∑ j,f (starJ j)):=by rw [← Equiv.sum_comp fromMargin.symm f, Fintype.sum_sum_type];rfl
lemma splitMargin (v: Tab (I⊕J) n→ℝ) (g: Matrix Q (Tab (I⊕J) n) ℝ)(i:Q): (g*ᵥv) i=(∑ j:Tab I n,g i (starI j)*v (starI j))+(∑ j:Tab J n,g i (starJ j)*v (starJ j)):= sumBoard _
end table
def toLeft (p:Row I Q)(q:Row J Q): Row (I⊕J) Q:=fun i j=> i.elim (fun i=>p i j) (fun j'=>q j' j)
lemma toLeft_read (p:Row I Q)(q:Row J Q)(i:Tab I n)(j:Tab Q n): (toLeft p q).acts n (starI i) j=p.acts n i j:=rfl
lemma toLeft_reap (p:Row I Q)(q:Row J Q)(i:Tab J n)(j:Tab Q n): (toLeft p q).acts n (starJ i) j=q.acts n i j:=rfl
lemma toLeft_cash (p:Row I Q)(q:Row J Q)(hp:Whole p)(hx:Whole q): Whole (toLeft p q):=by
    obtain ⟨s,U,hs,H⟩:=hp; obtain ⟨η,V,h,Q⟩:=hx; refine ⟨min s η,max U V,lt_min hs h,?_⟩; rintro (i|i) j
    · exact strip_mono H (min_le_left ..) (le_max_left ..) ..
    exact strip_mono Q (min_le_right ..) (le_max_right ..) ..
def ROOT (A:Row J J):Row (I⊕J) (I⊕J):= toLeft 0 (fun i j k=> j.elim (fun _=>0) (fun j=>A i j k))
lemma root_cash (A:Row J J)(h:Whole A):Whole (ROOT (I:=I) A):=by
    apply toLeft_cash; exact ⟨1,0,one_pos,fun i j=> by simp [Width,SumBudget]⟩; obtain ⟨s,D,h,H⟩:=h; refine ⟨s,max D 0,h,?_⟩; rintro i (j|j)
    · change Width _ (max D 0) (0:Cover→ℝ); simp [Width,SumBudget]
    exact strip_mono H le_rfl (le_max_left ..) i j
lemma ROOT_left (A:Row J J)(i:Tab I n)(j:Tab (I⊕J) n): (ROOT A).acts n (starI i) j=0:=by
    rw [ROOT,toLeft_read]; change (∑' u:Cover, if j.1=i.1 + wrap n u then (0:ℝ) else 0)=0; simp
lemma ROOT_cross (A:Row J J)(i:Tab J n)(j:Tab I n):(ROOT A).acts n (starJ i) (starI j)=0:=by rw [ROOT,toLeft_reap];change (∑' u:Cover, if j.1=i.1 +wrap n u then (0:ℝ) else 0)=0;simp
lemma ROOT_right (A:Row J J)(i j:Tab J n):(ROOT (I:=I) A).acts n (starJ i) (starJ j)=A.acts n i j:=rfl
-- zero and ones
end Script
end YM.OPE.Flume
