import YM.OPE.Compatible.Cum.Pace
/-!
# L-budgets of Tap. scales independent of excitations; multiply cub bills
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Shell
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page Planned.PrimaryIntegral295.Carrier
variable {I J E:Type}{N:Side} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] [MeasurableSpace E][BorelSpace E] {μ:Measure E}[μ.IsAddHaarMeasure]{L:Law E} [Fintype I]
local notation "Q!"=> deck I N
local notation "W"=> E→ℝ
variable [DecidableEq J]{C c:ℝ}{Z:E→L[ℝ] deck I N}{p:J→E→ℝ}{v:J→ℕ}{x:deck I N}{b:J→ℝ}{n:ℕ}
def Prone (p:J→E→ℝ)(v:J→ℕ)(b:J→ℝ)(u: E→ℝ)(V:ℝ)(s:Finset J):Prop:=∀ i∈s,0≤b i∧ BeamS (p i) (V*b i) u (v i)
abbrev Visit (b:J→ℝ)(s:Finset J):=∏ i∈s,b i
abbrev grain (n:Side)(d:ℕ):=(n.val:ℝ)^d
abbrev Mani (v:J→ℕ)(s: Finset J):=∑ i∈s,v i
abbrev scrollK (s: Finset J):ℕ:= 4*s.card
lemma grainPlus (d e:ℕ): grain N (d+e)=grain N d * grain N e:=pow_add ..
variable {s:Finset J} (ha:Sustains L Z c) {f g:E→ℝ}{u:ℝ}
lemma grain_b (x:ℕ):1≤grain N x:= by unfold grain; apply one_le_pow₀; exact_mod_cast N.pos
omit [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] in
lemma Beaming (hf: BeamS f u (clockY x Z) n) (he:0≤u)(hp:Prone p v b (clockY x Z) (grain N 4) s): BeamS (f * powr p s) (u*grain N (scrollK s)*Visit b s) (clockY x Z) (n+Mani v s):=by
      induction s using Finset.induction_on with
      | empty=> simpa only [powr, grain, scrollK, card_empty,mul_zero,pow_zero,Visit,prod_empty, Mani,sum_empty, Nat.add_zero,mul_one] using hf
      | insert i s hi ih=>
           obtain ⟨hx,hQ⟩:= hp i (mem_insert_self i s)
           have hh:= ih (fun i hi'=> hp _ (mem_insert_of_mem hi')); rw [show powr _ (insert i s)= (powr p s)*(p i) from (by unfold powr; rw [prod_insert hi,mul_comm]),← mul_assoc]; refine ⟨hh.1.mul hQ.1,fun z=>?_⟩
           have hz:0 ≤ clockY x Z z:=zero_le_one.trans (tallY Z x z); rw [Pi.mul_apply,norm_mul]; apply (mul_le_mul (hh.2 z) (hQ.2 z) (norm_nonneg _) (by have hx : 0 ≤ (∏ j∈s,b j):= prod_nonneg fun j hj=>(hp _ (mem_insert_of_mem hj)).1; positivity)).trans_eq; unfold Visit Mani scrollK; rw [prod_insert hi, sum_insert hi, card_insert_of_notMem hi,Nat.mul_succ,grainPlus]; ring
include ha in
lemma Beer (hf: BeamS f u (clockY x Z) n)(he:0≤u)(hp:Prone p v b (clockY x Z) (grain N 4) s):
     ‖drink μ L p f s‖≤ grain N (4+scrollK s)* quotaB I c (n+Mani v s)* (1+‖x‖)^(n+Mani v s)*u* Visit b s:=by
          apply (Mile μ L Z ha x _ _ (by have hS:0 ≤ Visit b s:= Finset.prod_nonneg fun i hi=> (hp _ hi).1; have hQ:1 ≤ grain N (scrollK s):=grain_b _; positivity) _ (Beaming hf he hp)).trans_eq
          rw [grainPlus]; unfold grain; ring
-- cure budgets via powerset formula
abbrev HueS (s:Finset J):ℕ:= 4+8*s.card
lemma vesselC {q:Finset J}(h:q∈ s.powerset.erase s):q⊂s:= Finset.ssubset_iff_subset_ne.mpr ⟨mem_powerset.mp (mem_of_mem_erase h),ne_of_mem_erase h⟩
def Aroma (J I:Type)[DecidableEq J][Fintype I](v:J→ℕ)(c:ℝ)(n:ℕ)(s:Finset J):ℝ:= quotaB I c (n+Mani v s)+∑ q∈ (s.powerset.erase s).attach, Aroma J I v c n q.val* quotaB I c (0+Mani v (s\q.val))
termination_by s.card
decreasing_by exact Finset.card_lt_card (vesselC q.property)
lemma aromaR : Aroma J I v c n s=quotaB I c (n+Mani v s)+∑ q∈s.powerset.erase s, Aroma J I v c n q * quotaB I c (0+Mani v (s\q)):=by rw [Aroma]; exact congr_arg _ (Finset.sum_attach _ (fun q=> Aroma J I v c n q * quotaB I c (0+Mani v (s\q))))
lemma aroma0 (hc:0≤c):0≤Aroma J I v c n s:=by
     have h(i):0 ≤ quotaB I c i:=by unfold quotaB; positivity
     induction s using Finset.strongInduction with | _ s ih=> rw [aromaR]; exact add_nonneg (h _) (sum_nonneg fun i hi=>mul_nonneg (ih _ (vesselC hi)) (h _))
include ha
lemma Brick (hf:BeamS f u (clockY x Z) n)(he:0≤u)(hp:Prone p v b (clockY x Z) (grain N 4) s):
     ‖Tap μ L p f s‖ ≤ Aroma J I v c n s *(1+‖x‖)^(n+Mani v s) *grain N (HueS s) *u* Visit b s:=by
         induction s using Finset.strongInduction with
         | _ s ih=>
           unfold Tap;rw [Tab_rec,aromaR]; apply (norm_sub_le ..).trans
           rw [add_mul,add_mul, add_mul, add_mul]; apply add_le_add
           · apply (Beer (μ:=μ) ha hf he hp).trans; apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun i hi=> (hp i hi).1); apply mul_le_mul_of_nonneg_right _ he; rw [mul_comm _ (quotaB ..),mul_right_comm]; have hv : grain N (4+scrollK s)≤ grain N (HueS s):=pow_le_pow_right₀ (show 1 ≤ (N.val:ℝ) from by exact_mod_cast N.pos) (by unfold scrollK HueS; omega); apply mul_le_mul_of_nonneg_left hv; unfold quotaB; have hc:= ha.1; positivity
           apply (norm_sum_le ..).trans; simp_rw [sum_mul]; apply sum_le_sum fun i hi=>?_ ; have he' := vesselC hi; have hg: i.card<s.card:= Finset.card_lt_card he'; let w:=s\i; have hx:w⊆s:=sdiff_subset; have hv:= Beer (s:=w) (μ:=μ) ha (f:=1) (u:=1) (n:=0) (x:=x) ⟨Bond.one,fun x=> by simp ⟩ zero_le_one (p:=p) (b:=b) (v:=v) fun i hi => hp _ (hx hi)
           let F:=Aroma J I v c n i; let Y:=1+‖x‖; let q:= quotaB I c (0+Mani v w); let V:= Visit b i; have hI:= ih i he' (fun j hj=> hp j (he'.le hj)); have hk:w.card+i.card=s.card:= card_sdiff_add_card_eq_card he'.le; have hd: grain N (HueS i)*grain N (4+scrollK w)≤grain N (HueS s):= by rw [← grainPlus];apply pow_le_pow_right₀ (show 1≤(N.val:ℝ) from by exact_mod_cast N.pos); unfold scrollK HueS; omega
           have hx : V*Visit b w=Visit b s:=(mul_comm ..).trans (prod_sdiff he'.le)
           rw [norm_mul]; refine le_trans (mul_le_mul hI hv (norm_nonneg _) ((norm_nonneg _).trans hI)) ?_; change _≤ F*q*Y^_*_*_*_
           calc
             _=(F*q*Y^(n+Mani v s)*u*Visit b s)*(grain N (HueS i)*grain N (4+scrollK w)):=by rw [← hx,show n+Mani v s= n+Mani v i+(0+Mani v w) from (by have he:Mani v w+Mani v i=Mani v s:=sum_sdiff he'.le; omega)]; unfold F V q Y w; ring
             _ ≤_:=by have h:0 ≤ F:=aroma0 ha.1; have hB:0 ≤ Visit b s:= prod_nonneg fun i hi=> (hp _ hi).1; have hc:0 ≤ q:=by unfold q quotaB; have ha:= ha.1; positivity
                      exact (mul_le_mul_of_nonneg_left hd (by unfold Y; positivity)).trans_eq (by ring)
end YM.OPE.Libra.Shell
