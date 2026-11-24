import YM.MS.Alps.Sluice
/-!
# Costs of local log movements (away from radial poles)

Use either bounds/full panes or rails. α constant on step proof however. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Alps
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum
open Momentum Metric
open scoped Topology ContDiff
variable {G:Gauge}{I A B E P F H:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup P][NormedSpace ℝ P]
  [NormedAddCommGroup F][NormedSpace ℝ F]{m:ℕ}
variable {p r:ℝ}{s:I→ℝ} {a b:I→ℝ}{α:ℂ}{z:UScale I}{f:I→ E→ F}{u:I→ ℂ}
local notation "Ns" => Arc.path z
lemma limitF (h:veg z f a)(hp: ∀ i,s i ≤ p): veg z (fun i x=>f i (Real.exp (s i) • x)) a:= by
   let v(i:I): E→L[ℝ] E:= exp (s i) • ContinuousLinearMap.id ℝ E; refine Arc.hike (fun i=> (h.smooth i).comp (v i).contDiff) (fun j=>?_); obtain ⟨C,hC,b,hb⟩:= ride h j
   let Q:=1+ Real.exp p; have hQ : Q>0:= by unfold Q; positivity
   refine ⟨C*Q^(j+b),mul_pos hC (pow_pos hQ _),b,fun i x=>?_⟩ -- indent
   let s':=exp (s i); have hz : 0<s':= exp_pos _; have hx:s' ≤ exp p:= exp_monotone (hp i); have hv : ‖v i‖≤Q:= by unfold v; rw [norm_smul,norm_of_nonneg (exp_pos (s i)).le]; unfold Q; exact (mul_le_of_le_one_right hz.le (ContinuousLinearMap.norm_id_le)).trans (hx.trans (le_add_of_nonneg_left zero_le_one))
   have hv' : (1+ |z i|)*(1+‖v i x‖) ≤ Q*((1+|z i|)*(1+‖x‖)):= by change (1+ |z i|)*(1+‖s' • x‖)≤ _; rw [norm_smul_of_nonneg hz.le,mul_left_comm Q]; refine mul_le_mul_of_nonneg_left ?_ (by positivity); unfold Q; nlinarith [norm_nonneg x]
   change ‖iteratedFDeriv ℝ j ( f i ∘ v i) _‖ ≤ _; rw [(v i).iteratedFDeriv_comp_right (h.smooth i) x (by exact_mod_cast le_top)]; apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans; rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin];
   let W:=(1+|z i|)*(1+‖x‖); have hw:W≥0:=by unfold W; positivity
   have ha:=terrain h i; calc
     _ ≤ C*((1+ |z i|)*(1+‖v i x‖))^b*a i*Q^j:= by apply mul_le_mul (hb ..) (pow_le_pow_left₀ (norm_nonneg _) hv j) (by positivity) (by positivity)
     _ ≤ C*(Q*W)^b*a i* Q^j:= by gcongr
     _ = _:= by unfold W; rw [pow_add,mul_pow]; ring

lemma limitL (h: Line Ns (fun _=>Set.univ) f a)(hp:∀ i,p ≤ s i)(hr:∀ i,s i ≤ r): rails z a fun i x=>f i (exp (s i) • x):= by
   let A(i:I): E→L[ℝ] E:= exp (s i) • ContinuousLinearMap.id ℝ E; have hA i : ‖A i‖≤ exp r:= by unfold A; rw [norm_smul,norm_of_nonneg (exp_pos (s i)).le]; exact (mul_le_of_le_one_right (exp_pos _).le (ContinuousLinearMap.norm_id_le)).trans (exp_monotone (hr i));
   let H:=1+(exp p)⁻¹; have hx:H>0:= by unfold H; positivity
   intro b; refine ⟨fun i=> ( h b|>.smooth i).comp (A i).contDiff, fun j=>?_⟩; obtain ⟨C,hC,w,hw⟩:= (h b).quoted j;
   refine ⟨C*H^b*(exp r)^j,by positivity,w,fun i x _=>?_⟩
   have ha:=terrain (railto h) i
   have hm : (Arc.path z).weight i x≤H*(Arc.path z).weight i (A i x):= by
      change 1+1*‖x‖≤ (1+(exp p)⁻¹)*(1+1*‖exp (s i) • x‖); simp only [one_mul,norm_smul_of_nonneg (exp_pos (s i)).le]; have hh : ‖x‖ ≤ (exp p)⁻¹ * (exp (s i)*‖x‖):= by rw [← div_eq_inv_mul,le_div_iff₀ (exp_pos p),mul_comm]; gcongr; exact hp i
      nlinarith [norm_nonneg x,exp_pos (s i),inv_pos.mpr (exp_pos p)]
   change ‖iteratedFDeriv ℝ j ( f i∘ A i) _‖ ≤ _; rw [(A i).iteratedFDeriv_comp_right ((h b).smooth i) x (by exact_mod_cast le_top)]; apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans; rw [Finset.prod_const,Finset.card_univ, Fintype.card_fin]
   have hQ:=hw i (A i x) (mem_univ _); let U := (Arc.path z).basic i; simp only [Scale.strict,cheap_length,one_pow,mul_one] at hQ ⊢;
   let u:=(Arc.path z).weight i x; let v:= (Arc.path z).weight i (A i x); have hu:u>0:= (Arc.path z).weight_pos i x; have hv : v>0:= (Arc.path z).weight_pos i _; have hf : U>0:= (Arc.path z).basic_pos _
   have hl: a i/v^b ≤ H^b*(a i/u^b):= by rw [← mul_div_assoc, div_le_div_iff₀ (pow_pos hv _) (pow_pos hu _), mul_comm (H^b),mul_assoc,← mul_pow]; gcongr
   calc
     _ ≤ C*U^w*(a i/v^b)*(exp r)^j:= by apply mul_le_mul hQ (pow_le_pow_left₀ (norm_nonneg _) (hA i) _) (by positivity) (by positivity)
     _ ≤ C*U^w*(H^b*(a i/u^b))*(exp r)^j := by gcongr
     _ = _ := by unfold U u; ring
end YM.MS.Alps
