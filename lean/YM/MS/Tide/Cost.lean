import YM.MS.Tide.Coi
import YM.MS.Port.Spire
/-!
# Converting the two-cutoff rate to physical scaling
Define within this proof strong (power-rate) convergence.I indexed all placements permitted.
Parameters any ordered scaling. θ actual log spacing units. Super-poly side
atoms unbounded, formal interpret after linked choices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Tide
open Function Filter Set Finset MeasureTheory Real
open Koszul Plane Landau Tone High Latch Job Vista Rake Rake.Geo Vane Port Fleet Lattice
open scoped Topology ContDiff Interval
variable {I E X:Type}[NormedAddCommGroup E][NormedAddCommGroup X] {V:Visa I}{L:I→Side}{P:Geo I}{l:Filter I}
    {F H D X':I→ ℂ} {x μ:ℝ}{w:ℕ}{v: I→ℝ}
abbrev mildG := eps_gain/2
lemma mild_p : 0 < mildG:= by norm_num
abbrev lake (P:Geo I)(h:ℝ)(i:I):= exp ( -h* P.θ i )
def PeakT (l:Filter I)(P:Geo I)(h:ℝ)(F:I→ℂ): Prop:= ∃ C:ℝ,0<C∧ ∀ᶠ i in l,‖F i‖≤ C* lake P h i
namespace PeakT
lemma fromζ (hv: PeakT l P x F)(h:H =ᶠ[l] F): PeakT l P x H:= by obtain ⟨c,hc,hx⟩:= hv; exact ⟨ c,hc,( h.and hx ).mono (fun i hi=> by rw [hi.1]; exact hi.2) ⟩
lemma zero : PeakT l P x 0:= by refine ⟨1, zero_lt_one,Eventually.of_forall fun i=>?_⟩; simp [lake,(exp_pos _).le]
lemma downs (h:μ≤x) (hc:PeakT l P x F): PeakT l P μ F:= by obtain ⟨c,hv,H⟩:=hc; exact ⟨ c,hv,H.mono fun k hk=> hk.trans (by unfold lake; gcongr; exact P.room k)⟩
lemma plus (h: PeakT l P x F)(hp: PeakT l P x H): PeakT l P x (F+H):= by
   rcases h with ⟨c,hc,h⟩; rcases hp with ⟨d,hd,h'⟩; exact ⟨c+d,by positivity,(h.and h').mono fun i hi=>(norm_add_le ..)|>.trans ( ( add_le_add hi.1 hi.2 ) |>.trans_eq (Eq.symm (add_mul ..)) )⟩
lemma mul (h: PeakT l P x F)(hp: PeakT l P μ H): PeakT l P (x+μ) ( F*H ):= by
   obtain ⟨c,hc,h⟩:=h; obtain ⟨d,hd,h'⟩:=hp; refine ⟨ c*d,by positivity,(h.and h').mono fun i hi=>?_⟩; rw [ Pi.mul_apply, norm_mul ]; refine (mul_le_mul hi.1 hi.2 (norm_nonneg _) (le_trans (norm_nonneg _) hi.1))|>.trans_eq ?_; unfold lake; rw [mul_mul_mul_comm, ← Real.exp_add, neg_add,add_mul ]
-- ∀ small. can use base-norm (peak positive). 
lemma topos {x:ℝ}(h:0<x)(he:Tendsto P.θ l atTop)(hp: PeakT l P x F): Tendsto F l (𝓝 0):= by
   rcases hp with ⟨C,hC,hF⟩; let A:= lake P x; have hu := tendsto_exp_atBot.comp (( he.const_mul_atTop_of_neg (show -x<0 from neg_lt_zero.mpr h)) ); apply tendsto_zero_iff_norm_tendsto_zero.mpr; exact squeeze_zero' ( Eventually.of_forall (fun i=>norm_nonneg _) ) hF ( ( by simpa only [mul_zero] using! hu.const_mul C ) : Tendsto (fun i=> C*A i) l (𝓝 0))
end PeakT
-- superpoly means log side eventually dominates any stipulated multiple
abbrev Super (l:Filter I)(L:I→Side)(v:I→ℝ): Prop:= ∀ h:ℝ, ∀ᶠ i in l,h*v i ≤ log ( tickA L i )
-- Wv not automatically bounded so provision. center offset by c.P.
structure NearPlan (l:Filter I)(P:Geo I)(V:Visa I)(L:I→Side)(μ:ℝ): Prop where
   vanish : Tendsto P.θ l atTop
   liftM : Super l L P.θ
   dimm i: P.η i=μ-P.θ i
   bankV : ∃ a:ℝ,∀ᶠ i in l,V.bank i ≤ exp (a* P.θ i)
namespace NearPlan
variable (h:NearPlan l P V L μ)
include h
lemma grows : Tendsto ( tickA L ) l atTop:= by
    have H:= h.liftM 1; refine tendsto_atTop_mono' _ ?_ ( tendsto_exp_atTop.comp h.vanish ); filter_upwards [ H ] with i hi; rw [one_mul] at hi; exact ( exp_monotone hi )|>.trans_eq ( exp_log ( δ_p L i )) 
lemma exlog (i:I): Vane.tarB P i≤ (1+ |μ| + P.θ i)^2:= by
    unfold Vane.tarB Rake.Geo.habitat; rw [ h.dimm ]; have ht:= abs_sub μ (P.θ i); rw [abs_of_nonneg ( P.room _ )] at ht; rw [pow_two]; apply mul_le_mul _ _ _ _ <;> linarith [abs_nonneg μ,P.room i]

lemma gain (hp:title P eps_gain w F): PeakT l P ( (w:ℝ)+mildG ) F:= by
   obtain ⟨C,hC,k,hK⟩:=hp; refine ⟨ C,hC,?_⟩; obtain ht : ∀ᶠ i in l,(1+|μ|+ P.θ i)^(2*k)*exp (-mildG*P.θ i)≤1:= ( ( exp_keep _ mild_p (2*k) _ ).comp h.vanish ).eventually ( ge_mem_nhds ( zero_lt_one ) ) 
   filter_upwards [ht] with i hi; apply ( hK i ).trans; apply mul_le_mul_of_nonneg_left _ hC.le; unfold moneyX lake; have hu : -(w:ℝ)-eps_gain=-mildG+(-( ( w:ℝ )+mildG)):= by unfold mildG; ring
   calc
     _ ≤ ((1+|μ|+P.θ i)^2)^k * exp (( -( w:ℝ ) - eps_gain )* P.θ i ):= by
         gcongr; · exact zero_le_one.trans (atmoP i)
         exact exlog h i
     _ ≤ exp ( -( (w:ℝ)+mildG )*P.θ i ) := by
           rw [hu, add_mul,exp_add,← pow_mul,← mul_assoc]; exact mul_le_of_le_one_left ( exp_pos _|>.le) hi
-- log estimate.Scalar `∀F Cash-out`. principle exponent plan
lemma costG (hp:cash_out V L F)(x:ℝ): PeakT l P x F:= by
   rcases h.bankV with ⟨a,ha⟩; obtain ⟨C,hC,k,hK⟩:= pay_repr hp; refine ⟨ C,hC,?_⟩; obtain hx:= h.liftM ((k*a+x)/mildG)
   have he : ∀ᶠ i in l,(1+ log (1+tickA L i ))^k* (tickA L i)^(-mildG) ≤ 1 := ( timeW (grows h) (δ_L L) _ mild_p k ).eventually ( ge_mem_nhds ( zero_lt_one ) ); -- _
   filter_upwards [he,hx,ha] with i hi ht he; apply ( hK i ).trans; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hC.le; rw [ mul_pow ]; let A:= tickA L i; have hm:= δ_p L i; have hu : A^(-eps_gain) = A^(-mildG)* A^(-mildG):= Eq.symm (by rw [← Real.rpow_add hm,show -mildG+-mildG=-eps_gain from (by unfold mildG; ring) ]) -- rfl numeric.Need norm_num
   rw [ hu ]; let t:= until0 L i; calc
    _ = V.bank i^k * A^(-mildG)* ((1+t)^k* A^(-mildG)) := by unfold A t until0; ring -- hu rewrite?
    _ ≤ V.bank i^k * A^(-mildG):= mul_le_of_le_one_right (by have he: 0< V.bank i:= lt_of_lt_of_le zero_lt_one ( V.here i ); unfold A; positivity) hi
    _ ≤ (exp (a*P.θ i))^k * A^(-mildG):= by gcongr; · exact zero_le_one.trans (V.here i)
    _ ≤ _:= by
       rw [← Real.exp_nat_mul, Real.rpow_def_of_pos hm, ← exp_add]; apply Real.exp_monotone; have ht2:= ht; rw [ div_mul_eq_mul_div, div_le_iff₀ mild_p ] at ht2; linarith only [ht2] -- norm_nf at hm huge
end NearPlan
end YM.MS.Tide
