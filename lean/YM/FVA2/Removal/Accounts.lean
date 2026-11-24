import YM.FVA2.Removal.Two
/-!
 # Link period comparison for insertions on unrestricted indices.

 Arithmetic lemmas. Stronger form of `Tide.NearPlan.costG` (still before power schedule):
 allow all lattice-space periods and obtain the honest period-power gain. Also eventual-only UV
 rate with no linking requirement. Full unspecialized array operations at that cost. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Removal
open Function Set Filter Finset Metric MeasureTheory Real
open MS MS.Koszul MS.Plane MS.Landau MS.Tone Lattice MS.Land MS.Latch MS.Latch.Job MS.Tide MS.High
open MS.Vane MS.Rake MS.Rake.Geo MS.Vista MS.Vane MS.Fleet MS.Dial
open MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Engine MS.Puff.SplitP MS.Puff.Actors MS.Puff.Mom MS.Swirl
open scoped Topology ContDiff Interval
variable {I:Type} {l:Filter I}{P:Geo I}{L:I→Side}{V: MS.Vista.Visa I}{μ:ℝ}
variable {x y u v:I→ℂ}
-- not assuming growth toward any prescribed exponent
lemma polylog (k:ℕ): ∃ C:ℝ, 0<C∧ ∀ x:ℝ,1≤x→ (1+ Real.log (1+x))^k*x^(-mildG) ≤ C:= by
 let f(x:ℝ):= max 1 x; obtain ⟨z,hz⟩:= eventually_atTop.mp ((timeW ( f:=atTop ) ( Filter.tendsto_atTop_mono ( g:= f ) ( fun i=>le_max_right .. ) tendsto_id ) ( fun i=> le_max_left .. ) _ mild_p k).eventually ( ge_mem_nhds zero_lt_one )); let t:= max 1 z; let r:= 1+ log (1+t); have hB:1≤t:= le_max_left ..; have hR:1≤ r:= le_add_of_nonneg_right (log_nonneg (by linarith)); refine ⟨ r^k,pow_pos (lt_of_lt_of_le zero_lt_one hR) _,fun x hx=>?_⟩; by_cases h: x < t
 · apply ( mul_le_of_le_one_right ( pow_nonneg (by have hL:0≤ Real.log (1+x):= Real.log_nonneg (by linarith); positivity) k ) (rpow_le_one_of_one_le_of_nonpos hx (neg_nonpos.mpr mild_p.le)) ).trans; unfold r; gcongr; · have hP: 0≤Real.log (1+x):= Real.log_nonneg (by linarith); linarith; -- log_le_log monotone req; gcongr errors?
 refine le_trans ?_ (one_le_pow₀ hR); obtain he:= hz x ( (le_max_right 1 z).trans (le_of_not_gt h)); simpa only [f,max_eq_right hx,Set.mem_Iic] using he
set_option quotPrecheck false
lemma allowance (h: cash_out ( loose P μ ) L x): ∃ (C:ℝ),0<C∧ ∃ m, ∀ i, ‖x i‖≤ C*vol P L m i := by
 obtain ⟨C,hC,k,hK⟩:= pay_repr h; obtain ⟨D,hD,hT⟩:= polylog k; let Z:= (1+|μ|)^k; have hz:0<Z:= (by unfold Z; positivity); refine ⟨ C*Z*D,by positivity,k,fun i=>?_⟩; apply ( hK i ).trans; let A:= tickA L i; let f:= until0 L i; have hX : A^(-eps_gain)=A^(-mildG) * A^(-mildG):= by rw [← Real.rpow_add (δ_p L i)]; ring_nf; rfl
 let x:=vol P L k i; have hx:0<x:=money ..; specialize hT A (δ_L L i); rw [pays]; unfold vol; change C*((_*(1+|μ|))*(1+f))^k* (A^(-eps_gain)) ≤ C*Z*D*x; rw [mul_pow,mul_pow,hX]; calc
   _ = C*Z*x * ((1+f)^k*A^(-mildG)):= by unfold x Z vol A; rw [ exp_nat_mul ]; ring
   _ ≤ _:= le_trans ( mul_le_mul_of_nonneg_left hT (by positivity : 0≤C*Z*x)) ( by ring_nf; exact le_rfl ) -- defeq f?) might annotate
lemma paid_out (h:cash_out (loose P μ) L x): Vol l P L x:= by obtain ⟨ C,hC,m,H⟩:= allowance h; exact ⟨C,hC,m,Eventually.of_forall H⟩
lemma shapeO (h:Tendsto P.θ l atTop)(H:∀ i,P.η i=μ-P.θ i){d:ℕ}(hp:title P eps_gain d x): PeakT l P ((d:ℝ)+mildG) x:= by
 -- can create artificial L' dependent on θ or replay existing argument
 have ha(i:I): tarB P i≤ (1+|μ|+P.θ i)^2:= by
   unfold tarB habitat; rw [H]; have ht:= abs_sub μ (P.θ i); rw [abs_of_nonneg (P.room i)] at ht; rw [pow_two]; apply mul_le_mul _ _ _ _ <;> linarith [abs_nonneg μ, P.room i]
 obtain ⟨C,hC,k,hK⟩:=hp; refine ⟨ C,hC,?_⟩; obtain ht : ∀ᶠ i in l,(1+|μ|+ P.θ i)^(2*k)*exp (-mildG*P.θ i)≤1:= (( exp_keep _ mild_p (2*k) _ ).comp h).eventually ( ge_mem_nhds ( zero_lt_one ) )
 filter_upwards [ht] with i hi; apply ( hK i ).trans; apply mul_le_mul_of_nonneg_left _ hC.le; unfold moneyX lake; have hu : -(d:ℝ)-eps_gain=-mildG+(-( ( d:ℝ )+mildG)):= by unfold mildG; ring
 calc
   _ ≤ ((1+|μ|+P.θ i)^2)^k * exp (( -( d:ℝ ) - eps_gain )* P.θ i ):= by
      gcongr; · exact zero_le_one.trans (atmoP i)
      exact ha i
   _ ≤ exp ( -( ( d:ℝ )+mildG )*P.θ i ) := by rw [ hu, add_mul,exp_add,← pow_mul,← mul_assoc ]; exact mul_le_of_le_one_left ( exp_pos _|>.le) hi
lemma Vol.entire (p:Vol l P L x)(h: Super l L P.θ)(s:ℝ): PeakT l P s x:= by
 obtain ⟨C,hC,m,hM⟩:=p; refine ⟨C,hC,?_⟩; filter_upwards [ h ((m+s)/mildG),hM ] with i hi hx; apply hx.trans; apply mul_le_mul_of_nonneg_left _ hC.le; unfold vol; rw [rpow_def_of_pos (δ_p L i), ← exp_add]; apply exp_monotone; rw [div_mul_eq_mul_div,div_le_iff₀ mild_p] at hi; linarith
lemma Total.link (p:Total l P L x)(h:Super l L P.θ): PeakT l P mildG x:= by
 obtain ⟨C,hC,m,hM⟩:=p; refine ⟨ 2*C,by positivity,?_⟩; filter_upwards [ h ((m+mildG)/mildG),hM ] with i hi hx; apply hx.trans
 have hu : vol P L m i≤ lake P mildG i:= by unfold vol; rw [rpow_def_of_pos (δ_p L i), ← exp_add]; apply exp_monotone; rw [div_mul_eq_mul_div,div_le_iff₀ mild_p] at hi; linarith
 unfold cost; nlinarith [mul_le_mul_of_nonneg_left hu hC.le]
-- and lifts. unmarked will identify all fields. Need Cheer = bury.
variable {J W:Type}{f g:I→J→ℂ}
lemma Tight.sum (s:Finset J)(hp:∀ j∈s, Tight l P L ( fun i=> f i j ) ( fun i=>g i j )): Tight l P L ( fun i=> ∑ j∈s, f i j ) ( fun i=>∑ j∈s,g i j ):= by
 classical induction s using Finset.induction_on with| empty=> simp_rw [Finset.sum_empty]; exact constant 0| insert i s hi ih=> simp_rw [ Finset.sum_insert hi ]; exact (hp _ (by simp)).plus ( ih fun j hj=> hp j (Finset.mem_insert_of_mem hj))
abbrev Tier (l:Filter I)(P:Geo I)(L:I→Side)(x y:I→J→T ℂ): Prop:= ∀ i n, Tight l P L (fun j=> x j i n) (fun j=> y j i n)
variable {a b c d:I→J→T ℂ}
lemma Tier.times (S: SplitP J)(h:Tier l P L a b)(hp:Tier l P L c d): Tier l P L (fun i=> S.Lift (Trunk.core) ( a i ) (c i)) (fun i=> S.Lift Trunk.core ( b i ) ( d i )):= by intro x n; simp_rw [S.loan, Finset.sum_apply]; exact Tight.sum _ fun j _=> Tight.sum (antidiagonal n) (fun k _=> Tight.join (h j.1 k.1) (hp j.2 k.2)) -- Trunk not imported? open Actors
lemma Tier.cheer (S:SplitP J)(h:Tier l P L a b)(u:J)(n:ℕ) : Tight l P L (fun i=> Cheer Trunk S ( a i ) u n) (fun i=> Cheer Trunk S ( b i ) u n):= by
 have hp(n:ℕ): Tier l P L ( fun i=> (Trunk.stack S).power ( a i ) n ) (fun i=> (Trunk.stack S).power ( b i ) n):= by induction n with| zero=> intro x j; exact Tight.constant _| succ _ ih=> exact Tier.times S h ih
 unfold Cheer MS.Puff.Actors.cheers; simp_rw [Finset.sum_apply]; exact Tight.sum _ fun j _=> Tight.join (Tight.constant (MS.Puff.Actors.phase j)) (hp j u n)
lemma Tier.push [LinearOrder W] (F B:Terrify W I)(h:∀ (s:Finset W) (k:ℕ), Tight l P L ( F s k ) ( B s k )) (s:Finset W)(n:ℕ): Tight l P L ( PeakT.ordZ F s n ) ( PeakT.ordZ B s n ):= by -- LinearOrder
 let Q(t:I)(a:Terrify W I):= fun i n=> a i n t; apply Tier.cheer ( S:=marked W ) ( a:=fun t=> Q t F ) (b:=fun t=> Q t B) _; exact fun i n=> h i n
end YM.FVA2.Removal
