import YM.FVA2.O.Score.Rental
/-!
# Uniform power-log budgets, with real log-scale variables

`Rain a`: a power T^(-a) times a polynomial estimate, T=exp(t), uniform
over an arbitrary test parameter space I (not growing depending on t).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Enh
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime
variable { I J E : Type }[ NormedAddCommGroup E ]
abbrev post (a t:ℝ)(k:ℕ): ℝ:= (1+t)^k*Real.exp (-a*t)
lemma penny (a t:ℝ)(k:ℕ): post a t k=LogTime.polyExp a k t:=rfl
lemma post_at {t:ℝ}{k:ℕ}{a:ℝ}(h:0≤t): 0<post a t k:= by unfold post; positivity
-- for fixed spaces $I$ may be small subset, later projected.
abbrev Rain (a:ℝ)(f:I→ℝ→ E): Prop:= ∃ C:ℝ,0<C∧∃ k:ℕ, ∀ᶠ s in atTop,∀ i:I, ‖f i s‖≤ C*post a s k
namespace Rain
variable {n k:ℕ} {a b:ℝ} {f g h:I→ℝ→ E}
lemma size (h:Rain a f)(he:b≤a): Rain b f:= by
    obtain ⟨C,hC,k,H⟩:=h; refine ⟨C,hC,k,?_⟩; filter_upwards [ H,eventually_ge_atTop (0:ℝ) ] with s h hs; intro i; apply (h i).trans; unfold post; gcongr
lemma raise (H:Rain a f)(he:∀ᶠ s in atTop,∀ i:I,‖g i s‖≤‖f i s‖): Rain a g:= by obtain ⟨C,hC,k,h⟩:=H; exact ⟨ C,hC,k,( he.and h ).mono fun s ⟨hs,hv⟩ i=> (hs i).trans (hv i) ⟩
lemma pull (H:Rain a f)(p:J→I): Rain a (f∘ p):= by obtain ⟨C,hC,k,h⟩:=H; exact ⟨ C,hC,k,h.mono fun i hi j=> hi ( p j ) ⟩
lemma nil (a:ℝ): Rain a (fun (_:I) (_:ℝ)=> (0:E)):= by refine ⟨1,zero_lt_one,0,( eventually_ge_atTop (0:ℝ)).mono (fun s hs i=>?_ )⟩; rw [one_mul,norm_zero]; exact (post_at hs).le
lemma cash {p:I→ E}(h:∃ C:ℝ,∀ i, ‖p i‖ ≤ C): Rain 0 (fun i (_:ℝ)=>p i):= by
    obtain ⟨C,hC⟩:= h; refine ⟨ max C 1,lt_max_of_lt_right zero_lt_one,0,Eventually.of_forall fun t i=>?_⟩; simp only [post,neg_zero,zero_mul,exp_zero,pow_zero,mul_one]; exact ( hC i ).trans ( le_max_left .. )
lemma fixed (v:E): Rain 0 (fun (_:I) (_:ℝ)=> v):= cash ⟨ ‖v‖,fun _=>le_rfl ⟩
lemma plus (h:Rain a f)(ht: Rain a g): Rain a ( fun i t=> f i t+g i t ):= by
    obtain ⟨C,hC,k,h⟩:=h; obtain ⟨D,hD,n,H⟩:= ht; refine ⟨ C+D,add_pos hC hD,k+n,?_⟩; filter_upwards [h,H,eventually_ge_atTop (0:ℝ) ] with t h H ht; intro i; apply le_trans (norm_add_le ..); apply le_trans (add_le_add ( h i ) ( H i )); rw [ add_mul ]; unfold post; gcongr <;> linarith
lemma neg (h:Rain a f): Rain a ( fun i t=> - f i t ):= h.raise ( Eventually.of_forall fun _ _=> ( norm_neg _ ).le )
lemma minus (h:Rain a f)(he:Rain a g): Rain a ( fun i t=> f i t - g i t ):= by simp only [sub_eq_add_neg]; exact plus h he.neg
lemma sum (s: Finset J){f:J→ I→ℝ→ E}(h:∀ i∈s,Rain a ( f i )): Rain a ( fun i t=>∑ j∈s,f j i t ):= by
    classical induction s using Finset.induction_on with| empty=> simp only [Finset.sum_empty]; exact nil _| insert i s hi ih=> simp only [Finset.sum_insert hi ]; exact plus (h i (Finset.mem_insert_self ..)) ( ih fun j hj=> h j (Finset.mem_insert_of_mem hj) )
lemma lapse (hp: Rain a f)(h:0<a): TendstoUniformly (fun t i=> f i t) 0 atTop:= by
    obtain ⟨C,hC,k,H⟩:= hp; obtain hv:= ( LogTime.vanishes h k ).const_mul C; rw [mul_zero] at hv; refine Metric.tendstoUniformly_iff.mpr (fun ε hε=>?_ ); filter_upwards [H,hv.eventually ( gt_mem_nhds hε )] with t h H; intro i; rw [ Pi.zero_apply, dist_zero_left ]; exact lt_of_le_of_lt (h i) ( show C*post a t k< ε from H )
variable {f g:I→ℝ→ℂ}
lemma mul (h:Rain a f)(he:Rain b g): Rain (a+b) (fun i t=> f i t*g i t):= by
    obtain ⟨C,hC,k,h⟩:=h; obtain ⟨D,hD,l,ht⟩:=he; refine ⟨ C*D,mul_pos hC hD,k+l,?_⟩; filter_upwards [h,ht] with s h ht; intro i; rw [norm_mul]; apply (mul_le_mul (h i) ( ht i ) (norm_nonneg _) ( (norm_nonneg _).trans (h i))).trans_eq; unfold post; rw [ neg_add,add_mul,Real.exp_add,pow_add ]; ring
lemma wig (h: Rain a f)(he: Rain 0 g): Rain a (fun i t=> f i t*g i t):= by simpa only [add_zero] using mul h he
lemma cover (h:Rain 0 f)(he:Rain a g): Rain a (fun i t=> f i t*g i t):= by simpa only [zero_add] using mul h he
lemma scalar (h:Rain a f)(c:ℂ): Rain a (fun i t=> c * f i t):= cover (fixed c) h
lemma powers (h:Rain 0 f) (n:ℕ): Rain 0 (fun i t=> f i t ^ n):= by induction n with| zero=> simp only [pow_zero]; exact fixed _| succ i ih=> simp_rw [pow_succ]; exact wig ih h
lemma all_fee : Rain a (fun (_:I) t=> fee t a):= by
    refine ⟨1,zero_lt_one,0,(eventually_ge_atTop (0:ℝ)).mono fun t ht _=>?_ ⟩; unfold post Score.fee; rw [ Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ( exp_pos _|>.le ), pow_zero,one_mul,one_mul ]; exact le_of_eq (congr_arg Real.exp (by ring) )
lemma anyR : Rain 0 ( fun (_:I) (t:ℝ)=> (t:ℂ) ):= by refine ⟨1, zero_lt_one,1,(eventually_ge_atTop (0:ℝ)).mono fun t ht _=>?_⟩; simp only [post,neg_zero,zero_mul,exp_zero,pow_one,mul_one,one_mul,Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht ]; linarith
lemma rhythm {f:ℝ→ℂ} (h:Rhythm f): Rain 0 (fun (_:I)=> f):= by
    obtain ⟨p,rfl⟩:= Rhythm.from_poly.mp h; clear h
    induction p using Polynomial.induction_on' with
    | add p q hp hq=> simp_rw [Polynomial.eval_add]; exact plus hp hq
    | monomial n c=> simp_rw [ Polynomial.eval_monomial ]; exact cover ( fixed c ) ( powers anyR n )
end Rain
end YM.FVA2.O.Enh
