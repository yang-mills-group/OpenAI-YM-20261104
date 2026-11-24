import YM.QuadraticLocal.Aperture.Stack
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Aperture
open Function MeasureTheory Filter Finset Lattice Wilson RG Marker
open scoped Topology ENNReal ContDiff BigOperators Classical
open AllOrder AllOrder.Fire AllOrder.Laplace AllOrder.Laplace.SigmaP Response PertExtension PertExtension.Series Radial
open Sunrise Focus Comparison.Cumulants Extra.Trajectories Toggle Drawer
open Multi Comparison.RG02 Comparison.RG02.Order Primitives.GCC PositionX.Gauss
open AllOrder.Catch AllOrder.Catch.Clock ConnectedActivityE6 Blaze Brush PositionX.Jet
variable {X Y Z ι:Type*} {V:Type}[Fintype V][DecidableEq V] {b a c:ι→ℝ} {k j n:ℕ}
namespace Turnstile
variable {T:AllOrder.Catch.Clock ι}
-- utility bills
variable (x:ι→(V→ℝ)→ℝ) (v:ι→Book (V→ℝ))
variable {f:ι→ℝ}{C:ι→Word ℝ} (h:TaylorCap T k b f C)
local notation "K"=> TaylorCap T
include h
lemma fixed (q:ℝ): TaylorCap T k b (q • f) (q • C):= by
 refine ⟨fun i hi=> (h.steps i hi).lscale _, fun i hi=> ((h.stamps i hi).lscale q).eq_mem (Eventually.of_forall fun j=>?_ )⟩; unfold delay; simp only [Pi.smul_apply,smul_eq_mul, mul_sub, Finset.mul_sum]; congr 1; exact Finset.sum_congr rfl fun i _=>mul_left_comm ..
omit h
lemma together {f:X→ι→ℝ}{g:X→ι→Word ℝ} (s:Finset X)(h:∀ i∈s,TaylorCap T k b (f i) (g i)): TaylorCap T k b (∑ i∈s,f i) (∑ i∈s,g i):= by
 induction s using Finset.induction_on with
 | empty=> rw [Finset.sum_empty, Finset.sum_empty]; convert TaylorCap.const («b»:=b) T (Meter.const T 0) using 1 <;> first|rfl|funext i j; simp [just] -- fix
 | insert i s hi ih=> rw [Finset.sum_insert hi,Finset.sum_insert hi]; exact (h i (mem_insert_self ..)).pair (ih fun j hj=> h j (mem_insert_of_mem hj))
local notation "Vu"=> Drawer.Knife V
variable (V) (d:ℕ)
def data (x:ι→(V→ℝ)→ℝ):ι→ℝ:= fun i=> Toggle.alt (x i)
def array (v:ι→Book (V→ℝ)): ι→Word ℝ:= fun i j=> Toggle.alt (v i j)
variable (x:ι→(V→ℝ)→ℝ)
local notation "G"=> Fintype.card V
set_option quotPrecheck false
lemma declared (h:∀ v':Crew V, TaylorCap T k b (fun i=> x i (convertS v')) (fun i j=> v i j (convertS v'))): TaylorCap T k b (data V x) (array V v):= by
 let f' t (i:ι):=x i (convertS t); let g t (i:ι) (j:ℕ):= v i j (convertS t)
 convert together (s:=(univ:Finset (Crew V))) (f:=fun t=> Toggle.theta t • f' t) (g:=fun t=>Toggle.theta t • g t) (fun i _=> fixed (h i) (Toggle.theta i)) using 1
 · ext1 i; rw [Finset.sum_apply]; rfl
 funext i j; simp only [Finset.sum_apply]; rfl
lemma stray (q:ℝ)(hc:Nonempty V): alt (V:=V) (fun _=> q)= 0 := by
 obtain ⟨v⟩:=hc; let g(x:V→ℝ):=Drawer.view x (0:Multiset V); rw [show (fun _=>(q:ℝ))=q•g from funext (fun i=> (mul_one q).symm), Toggle.alt_times,show alt g=0 from Toggle.opposite v 0 (by simp),mul_zero]
lemma empties (g:(V→ℝ)→ℝ)(q:ℝ)(hc:Nonempty V) : alt (V:=V) (fun v:V→ℝ=> g v-q)=alt g:= by rw [show (fun v:V→ℝ=>g v-q)=g+fun _=>-q from funext (fun i=> sub_eq_add_neg ..),alt_plus,stray V _ hc,add_zero]
lemma ribbon {p:Word ℝ}(n t:ℕ)(t':ℝ)(h:∀ i<n,p i=0): delay p (n+t) t'= t'^n *delay (fun i=>p (n+i)) t t':= by unfold delay; rw [Nat.add_assoc,Finset.sum_range_add, show ∑ i∈Finset.range n,t'^i • p i=0 from Finset.sum_eq_zero (fun i hi=>by rw [h i (Finset.mem_range.mp hi),smul_zero]),zero_add, Finset.mul_sum]; simp_rw [smul_eq_mul,pow_add,mul_assoc]
lemma lance {p:Word ℝ}(n:ℕ)(t:ℝ)(h:∀ i<n,p i=0): delay p n t=t^n*p n:=by rw [show delay p n t=t^n*delay (fun i=>p (n+i)) 0 t from ribbon n 0 t h]; simp [delay]
-- Real low-output.Power.Acc. Uniform any pattern of surveys paid before. Intakes in S.Year.Price.
variable (hd:0<d) (z:ι→Book (V→ℝ))(Q:ι→ℝ)
variable (he:∀ᶠ i in T.rail,0<b i)(hx:T.Meter (fun i=>(b i)⁻¹) (1/2))
-- IMPORTANT: d (response weight) can be much larger than Fk caller Loan.
include he hx hd
set_option maxHeartbeats 200000 in
lemma meter {x:ι→(V→ℝ)→ℝ} (h:TaylorCap T k b (data V x) (array V v)) (hp:TaylorCap (Sage.lift d hd T) (Fintype.card V) (fun i=> b i^d) (data V x) (array V z))
   (hg:∀ᶠ i in T.rail,∀ t,t<Fintype.card V → (array V z) i t=0)(hQ:∀ᶠ i in T.rail,∀ p,p<Fintype.card V*d → (array V v) i p=0) (hk:Fintype.card V*d+j ≤ k)(hj:j < d):
    T.Meter (fun i=> (array V z) i (Fintype.card V)-delay (fun p=> array V v i (Fintype.card V*d+p)) j (b i)) (graded (j+1)):= by
 let m:= Fintype.card V * d; let V':=array V v; let Z':=array V z; let B i:= delay (fun k=>V' i (m+k)) j (b i); let v' i:=Z' i (G); have hF:= ((Sage.meter d hd T).1 (hp.stamps (G) le_rfl));
 have hm:(graded (G+1))*d ≤ graded (m+j+1):=(by unfold graded m; have h:=(Nat.cast_le (α:=ℝ)|>.mpr (show j+1≤d from hj) ); push_cast at h ⊢; nlinarith only [h]);
 let ht:= hx.pow m; let u:= ((h.stamps _ hk).sub (hF.weak hm)); refine ((ht.mul u).weak ?_).eq_mem ?_; · unfold graded m; push_cast; linarith
 filter_upwards [he,hg,hQ] with i hi hG hQ; rw [lance _ _ hG,ribbon _ _ _ hQ, ← pow_mul, Nat.mul_comm d]; let y:= (b i)^m; have hp:0<y:=pow_pos hi _; rw [inv_pow]; change y⁻¹*( data V x i-y*B i - (data V x i-y*v' i))= v' i-B i; field_simp; ring
-- In later use, maybe `∀ᶠ` hg if cert requires.Then fit by congr.
end Turnstile
end YM.QuadraticLocal.Aperture
