import YM.X.Jet.Sparkle
/-!
# Momentum-proven rates through formal jet operations

Rate statement comparing two arrays after leveling.Scheme. Includes two independent moving sets via Locally uniform Lipschitz. Ratio f finite momentum. purpose: normalization inherits power rates, also on separated sampled profiles.
-/
set_option autoImplicit false
set_option maxHeartbeats 620000
noncomputable section
namespace YM.FVA2.Prow
open MeasureTheory Set Function Metric Filter Topology Asymptotics Pert.Position PositionX PositionX.Jet
open scoped Topology ContDiff Classical
variable {I E F: Type*} {l:Filter I}{t:I→ℝ}
structure Rag (l:Filter I)(t:I→ℝ): Prop where
     nonneg : ∀ᶠ i in l,0≤t i
     vanish : Tendsto t l (𝓝 0)
variable [NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F]
    {f g a:I→E}{x:E} (h:Rag l t)
def Fast (l: Filter I)(t:I→ℝ){K:Type*}[PseudoMetricSpace K](f g:I→K): Prop:= ∃ C:ℝ,0<C∧∀ᶠ i in l,dist ( f i ) ( g i ) ≤ C*t i
section
variable {X:Type*} [PseudoMetricSpace X]{A B C:I→X}{z:X}
protected lemma Fast.congr (p:A =ᶠ[l] B)(hx:Fast l t A C): Fast l t B C:= by obtain ⟨c,hc,F⟩:=hx; exact ⟨ c,hc,(p.and F).mono fun i hi=> hi.1 ▸ hi.2 ⟩
include h
lemma Fast.self (A:I→X) : Fast l t A A:= by refine ⟨1,zero_lt_one,?_⟩; simp only [dist_self,one_mul]; exact h.nonneg
lemma hugs (hv:Fast l t A B)(hB:Tendsto B l (𝓝 z)): Tendsto A l (𝓝 z):= by
    obtain ⟨c,hc,h0⟩:= hv; apply Metric.tendsto_nhds.mpr; intro ε hε; have hd:Tendsto (fun i=>c*t i) l (𝓝 0):= by simpa only [mul_zero] using! h.vanish.const_mul c
    filter_upwards [ h0,hd.eventually (gt_mem_nhds (half_pos hε)), Metric.tendsto_nhds.mp hB _ (half_pos hε) ] with i hi hi' hk; linarith [dist_triangle ( A i ) ( B i ) z]
end
structure Tandem (l:Filter I)(t:I→ℝ){K:Type*}[PseudoMetricSpace K](f g:I→K)(x:K):Prop where
    pay: Fast l t f g
    tend: Tendsto g l (𝓝 x)
namespace Tandem
variable (hB:Tandem l t f g x)
include h
lemma stable {V:Type*}[PseudoMetricSpace V] (x:V): Tandem l t (fun _=>x) (fun _=>x) x:= ⟨ Fast.self h _,tendsto_const_nhds ⟩
include hB
lemma after (u:E→F) (he:ContDiffAt ℝ 1 u x): Tandem l t (u ∘ f) (u ∘ g) (u x):= by -- keyword rename
   obtain ⟨K,s,hs,hK⟩:=he.exists_lipschitzOnWith; obtain ⟨c,hc,hL⟩:=hB.pay; refine ⟨⟨ ((K:ℝ)+1)* c,by positivity,?_⟩, he.continuousAt.tendsto.comp hB.tend⟩; filter_upwards [ hB.tend.eventually hs,( hugs h hB.pay hB.tend ).eventually hs,hL,h.nonneg ] with i hx hy hh ht;
   apply le_trans (hK.dist_le_mul _ hy _ hx); apply (mul_le_mul_of_nonneg_left hh K.2).trans; rw [mul_assoc]; gcongr; simp -- context
omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
lemma pairUp {B A:I→ F}{y:F}(hp:Tandem l t A B y) : Tandem l t (fun i=>(f i,A i)) (fun i=>( g i,B i)) (x,y):= by
   obtain ⟨c,hc,H⟩:=hB.pay; obtain ⟨z,hz,R⟩:=hp.pay; refine ⟨⟨ c+z,by positivity,?_⟩, hB.tend.prodMk_nhds hp.tend⟩; filter_upwards [ H,R,h.nonneg ] with i hi he hn; apply max_le <;> first| exact hi.trans ( mul_le_mul_of_nonneg_right ( le_add_of_nonneg_right hz.le ) hn ) | exact he.trans (mul_le_mul_of_nonneg_right ( le_add_of_nonneg_left hc.le ) hn )
lemma add {y:I→E}{z:E}(hC:Tandem l t a y z): Tandem l t (f+a) (g+y) (x+z):= by exact ( hB.pairUp h hC ).after h (fun z=>z.1+z.2) (by fun_prop)
omit [NormedSpace ℝ E] in
lemma reverse : Tandem l t g f x:= ⟨ show Fast l t g f from (by obtain ⟨c,hc,H⟩:= hB.pay; exact ⟨ c,hc,H.mono fun i hi=>by rw [dist_comm]; exact hi ⟩), hugs h hB.pay hB.tend ⟩
omit [NormedSpace ℝ E] h in
lemma congr (hp:f =ᶠ[l] a): Tandem l t a g x:= ⟨ hB.pay.congr hp,hB.tend ⟩
omit hB
variable {V:Type*}{P:V→Type*}[Fintype V][∀ i,PseudoMetricSpace (P i)]
lemma every {A B:I→((i:V)→ P i)}{L: (i:V)→P i}(hH:∀ i:V,Tandem l t (fun j=> A j i ) (fun j=> B j i ) (L i)): Tandem l t A B L:= by
    choose C hC hc using fun i=> (hH i).pay; let q:=∑ i:V,C i; refine ⟨⟨q+1,by linarith [show 0≤ q from Finset.sum_nonneg (fun i _=> (hC i).le)],?_⟩, tendsto_pi_nhds.mpr (fun i=>(hH i).tend) ⟩; filter_upwards [ eventually_all.mpr hc, h.nonneg ] with i hi ht; have hp:0≤ (q+1)*t i:= mul_nonneg (by linarith [show 0≤ q from Finset.sum_nonneg (fun i _=> (hC i).le)]) ht; exact (dist_pi_le_iff hp).mpr fun j=> (hi j).trans (mul_le_mul_of_nonneg_right (le_trans ( Finset.single_le_sum (fun i _=> (hC i).le ) ( Finset.mem_univ _ ) ) ( show q≤q+1 from by linarith )) ht )
omit [∀ i,PseudoMetricSpace (P i)] [Fintype V]
lemma smult {p q:I→ℝ}{z:ℝ}(he:Tandem l t p q z)(hf:Tandem l t f g x) : Tandem l t (fun i=> p i • f i ) (fun i=> q i • g i) ( z • x ):= by exact ( he.pairUp h hf ).after h (fun z=>z.1 • z.2) (by fun_prop)
lemma sums (A:Finset V){ a b: V→I→E}{c:V→E}(hp:∀ i∈A,Tandem l t ( a i ) ( b i ) ( c i )) : Tandem l t (fun i=> ∑ j∈A,a j i) (fun i=>∑ j∈ A,b j i) (∑ i∈A,c i):= by
    induction A using Finset.induction_on with| empty=> simp_rw [Finset.sum_empty]; exact Tandem.stable h 0| insert i s hi ih=> simp_rw [Finset.sum_insert hi]; exact (hp _ (by simp) ).add h ( ih ( fun j hj=> hp _ ( by simp [hj])))
lemma products (A:Finset V){ a b:V→I→ℝ}{c:V→ℝ}(hp:∀ i∈A,Tandem l t ( a i ) ( b i ) ( c i )) : Tandem l t ( fun i=>∏ j∈A,a j i ) (fun i=>∏ j∈A,b j i) (∏ i∈A,c i):= by
    induction A using Finset.induction_on with| empty=>simp_rw [Finset.prod_empty]; exact Tandem.stable h _ | insert i s hi ih=> simp_rw [Finset.prod_insert hi]; exact Tandem.smult h (hp _ (by simp)) ( ih (fun j hj=> hp j (by simp [hj])))
end Tandem
variable {X Y:I→ Word E} {a:Word E }
def side (l:Filter I)(t:I→ℝ){E:Type*}[PseudoMetricSpace E](X Y:I→Word E)(a:Word E): Prop:= ∀ n:ℕ,Tandem l t (fun i=>X i n) (fun i=>Y i n) (a n)
variable (hx:side l t X Y a)
-- straightforward.Sparkle
include h hx
omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
lemma side.pairS {U V:I→Word F}{b:Word F} (hp:side l t U V b): side l t (fun i=> pair ( X i ) ( U i )) (fun i=> pair ( Y i ) ( V i )) (pair a b):= fun i=> Tandem.pairUp h (hx i) (hp i)
lemma side.twistS {u v:I→Word ℝ}{b:Word ℝ}(he:side l t u v b): side l t (fun i=>ren ( u i ) ( X i )) (fun i=>ren ( v i ) ( Y i )) (ren b a):= by
    intro k; unfold ren order; exact Tandem.smult h ( Tandem.stable h _ ) ( Tandem.sums h _ ( fun i _=> Tandem.smult h (Tandem.products h _ (fun j _=> Tandem.smult h (Tandem.stable h _) (he _))) ( Tandem.smult h ( Tandem.stable h _ ) (hx _ ) )))
omit h hx in
-- follow Pert.Position.Implicit
private lemma partR {f : E→ℝ→F} (x : E) (n : ℕ) (h : ContDiffAt ℝ ω (uncurry f) (x,0)) : ContDiffAt ℝ ω (fun u => iteratedDeriv n (f u) 0) x := by
  have hd : ∀ n : ℕ, ContDiffAt ℝ ω (uncurry fun u => iteratedDeriv n (f u)) (x,0) := by
    intro k; induction k with
    | zero => simp [h]
    | succ k ih =>
      let K u := iteratedDeriv k (f u)
      simp_rw [iteratedDeriv_succ,uncurry_def]
      change ContDiffAt ℝ ω (fun p => fderiv ℝ (K p.1) p.2 1) (x,0)
      apply ContDiffAt.clm_apply (ContDiffAt.fderiv (n:=ω) (f:=fun p : E×ℝ => K p.1) (g:=Prod.snd) _ contDiffAt_snd (by simp)) contDiffAt_const
      exact ih.comp (f:=fun p : (E×ℝ)×ℝ => (p.1.1,p.2)) ((x,0),(0:ℝ)) (by fun_prop)
  exact (hd n).comp (f:=fun u : E => (u,(0:ℝ))) x (by fun_prop)

-- positive-order jet limit inherits power (analytic bound ⊂ contdiff). motion etc
lemma side.runs (f:E→F)(he: ContDiffAt ℝ ω f (a 0)): side l t (fun i=> run f ( X i )) (fun i=> run f ( Y i )) (run f a):= by
  intro n; let V(P:Word E)(i:Fin (n+1)):= P (i:ℕ); let A (u:Fin (n+1)→E)(t:ℝ) := ∑ i:Fin (n+1), t^(i:ℕ) • u i; let F'(u:Fin ( n+1 )→ E)(t:ℝ):= f ( A u t );
  have hE (P:Word E)(t:ℝ): delay P n t=A ( V P ) t:= by unfold delay A; rw [Finset.sum_range]
  have hp : Tendsto (fun i=>V (Y i)) l (𝓝 (V a)):= tendsto_pi_nhds.mpr (fun i=> (hx i).tend); -- unused
  have hg: ContDiffAt ℝ ω (uncurry F') ( V a,0):= by
      apply ContDiffAt.comp (g:=f) ( f:=uncurry A ) ( n:=ω ) (V a,0) _ ?_; swap; unfold A uncurry; fun_prop; -- comma? order
      change ContDiffAt ℝ ω f ( A ( V a ) 0 ); rwa [ ← hE, delay_zero ];
  let r(P:Word E):= F' ( V P ); have hl(P:Word E) : r P=f ∘ delay P n:= funext (fun i=> congr_arg f ( hE P i ).symm );
  unfold run someJ; simp_rw [ ← hl ]; apply Tandem.smult h (Tandem.stable h _ ); exact Tandem.after h ( f:=fun i=>V ( X i ) ) ( g:=fun i=> V ( Y i )) (x:=V a) ( Tandem.every h (fun i=> hx i ) ) _ (( partR _ n hg ).of_le le_top)
end YM.FVA2.Prow
