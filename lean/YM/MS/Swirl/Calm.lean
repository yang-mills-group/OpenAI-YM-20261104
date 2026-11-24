import YM.MS.Swirl.Mill
/-!
# Projector relation for one momentum
 Track b weights by kinds including ghost vs longitudinal. Sign using conventions S[-p,p].
  The only matrix assertion needed for Euler cancellation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Swirl.Near
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Tone Frame Lattice City Latch Detect Tone Momentum Heat Orbit Cog Orbit.LogReal Book Convolve Program
open Complex (I)
open scoped Topology ContDiff Interval
variable {G:Gauge}{A E:Type}{n:Side}{b:Bool} [Fintype A][DecidableEq A]
-- partition invariant weight.t
abbrev Tag := Bool×Bool -- isNone? , anti?
abbrev tagged (i:Atom A): Tag:= ( i.1.isNone,i.2 )
variable (w:Tag→ℂ)(p:Momentum A)(x y: Atom A)
-- afi ↓
def Sqpart : YMflow A
 | (some i,false),(some j,false),p=> -(precision i j p:ℂ)
 | (some i,true),(none,false),p=> Complex.I*(p i)
 | (none,false),(some i,true),p=> Complex.I*(p i)
 | _,_,_=>0
private lemma taxed (i j:A): (∑ k:A,(precision i k p:ℂ)*(precision k j p:ℂ))=(p.sq:ℂ)* (precision i j p:ℂ):= by exact_mod_cast k_times i j p
omit [DecidableEq A] in
private lemma moment : (∑ k:A,(p k:ℂ)*(p k:ℂ))= p.sq:= by simp [Momentum.sq,pow_two]
lemma sipT : ∑ i:Atom A,∑ j:Atom A, w ( tagged i ) * Tail x i p * Sqpart i j p * Tail j y p = -w ( tagged y ) * Tail x y p := by
   by_cases h:p.sq=0; · simp_rw [zeroShift _ _ h]; simp
   have hv : (p.sq:ℂ)≠0:= by exact_mod_cast h
   let Q:ℂ:= p.sq;
   have Hq (w c:ℂ) : ∑ x:A,w*(I*((p x:ℂ)/Q))*(I*(p x))*c= - (w*c):= by
        simp_rw [ show ∀ x:A,w*(I*((p x:ℂ)/Q))*(I*p x)*c = (( -(w*c) )/Q) * ((p x:ℂ)*(p x:ℂ)) from fun x=>by ring_nf; simp [Complex.I_sq] ]; rw [ ← Finset.mul_sum, moment ]; exact div_mul_cancel₀ _ hv
   have hr (w:ℂ)(i a:A): ∑ k:A, w * ( (precision i k p:ℂ)/Q^2 )*( precision k a p:ℂ ) = (w/Q)*(precision i a p:ℂ):= by
        simp_rw [ show ∀ k:A,w * ( (precision i k p:ℂ)/Q^2 )*( precision k a p:ℂ )=(w/Q^2)*( (precision i k p:ℂ)*(precision k a p:ℂ) ) from fun k=>by ring, ← Finset.mul_sum,taxed ]; unfold Q; field_simp
   rcases x with ⟨_|a,_|_⟩ <;> rcases y with ⟨_|b,_|_⟩ <;> simp [Fintype.sum_prod_type,Fintype.sum_option,Tail,Sqpart,tagged,Option.isNone_some]
   · exact Hq _ _
   · rw [ Finset.sum_comm ]; simp_rw [ ← Finset.sum_mul ]; unfold Q at hr; simp_rw [hr]; -- maybe notation `simp_rw` hr not elaborated
     simp_rw [ show ∀ k:A, w (false,false)/(p.sq:ℂ)*(precision a k p:ℂ)*((precision k b p:ℂ)/(p.sq:ℂ)^2)= (w (false,false)/(p.sq:ℂ))*((precision a k p:ℂ)/(p.sq:ℂ)^2)*(precision k b p:ℂ) from fun k=>by ring, hr ]; field_simp
   apply Eq.trans _ (Hq ( w (true,false) ) _); exact Finset.sum_congr rfl fun x _=> by ring
-- colors. 
def Tagged (i:BH G): Tag:= tagged i.1 -- not coloring
abbrev Eyes (b:FixedMode G n):= Tagged b.1
lemma oriented (p:QP)(a b:BH G): styleK (-p) a b= Landau.choir Sqpart wave a b p:= by
   unfold Landau.choir styleK; simp_rw [matchA]; split; · rcases a with ⟨⟨_|a,_|_⟩,i⟩ <;> rcases b with ⟨⟨_|b,_|_⟩,j⟩ <;> simp only [ μ2,α₂,Sqpart,wave_neg,k_even,zero_add,add_zero, Pi.neg_apply,Complex.ofReal_neg, mul_neg,neg_neg ]
   rfl
lemma sesame (p:QP)(x y:BH G): (∑ i:BH G,∑ j:BH G,w ( Tagged i ) * ( Landau.choir Tail wave x i p ) * styleK (-p) i j * ( Landau.choir Tail wave j y p ))= -w ( Tagged y ) * ( Landau.choir Tail wave x y p ) := by
    rcases x with ⟨x,a⟩; rcases y with ⟨y,b⟩; simp_rw [oriented,Fintype.sum_prod_type (α₁:=Atom Axis)]; by_cases h:a=b; · subst b; simp [ Landau.choir, Tagged,mul_ite,ite_mul ]; rw [ ← neg_mul ]; exact sipT w _ _ _
    simp [Landau.choir,Tagged,h, mul_ite,ite_mul]
end YM.MS.Swirl.Near
