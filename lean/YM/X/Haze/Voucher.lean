import YM.X.Haze.Visa
/-!
Contributions with factors from line powers and integer root powers.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Haze
open Lattice Wilson Next.Rank CellsInt Beamer Interval PertExtension LatticePT Normal Filter Set Function Metric MeasureTheory Asymptotics
open Reed Stems Fielding Print
open scoped Topology BigOperators Classical ENNReal
variable {q : ℕ+} (hq:1<q.val) {n:Side} {k m v:ℕ} {R:ℝ}
local notation "Fℕ"=>(atTop:Filter ℕ)
local notation "ε"=>epsilon q
variable {V W S:Type*}[NormedAddCommGroup V][NormedAddCommGroup W][NormedAddCommGroup S][NormedSpace ℝ V][NormedSpace ℝ W][NormedSpace ℝ S]{a b c d:ℤ}
variable {f:Mist V}
def Once (i:ℕ→V) : Mist V:=fun t _=> i t
namespace Visa
lemma mapL (h:Visa q R a b f)(L:V→L[ℝ] W): Visa q R a b (fun i z=> L (f i z)):= by
   obtain ⟨C,hc,he⟩:= h.who; refine ⟨⟨‖L‖*C,by positivity,?_⟩,fun x hx hr z hz=>?_⟩
   · filter_upwards [he] with i hi z hz; refine (L.le_opNorm (f i z)).trans ?_; rw [mul_assoc];gcongr;apply hi z hz
   simp_rw [← map_smul]; obtain ⟨y,hy⟩:= h.whereL x hx hr z hz; exact ⟨L y,L.continuous.continuousAt.tendsto.comp hy⟩
lemma pairL {g:Mist W}(h:Visa q R a b f)(hx:Visa q R c d g)(L:V→L[ℝ] W→L[ℝ] S) : Visa q R (a+c) (b+d) (fun i z=> L (f i z) (g i z)):= by
   obtain ⟨C,hc,he⟩:= h.who; obtain ⟨A,ha,hd⟩:= hx.who; refine ⟨⟨‖L‖*C*A,by positivity,?_⟩,fun x hp hr z hz=>?_⟩
   · filter_upwards [he,hd] with i hi hk z hz; rw [← decomp]; calc
          _ ≤ ‖L‖*‖f i z‖*‖g i z‖:= L.le_opNorm₂ ..
          _ ≤ ‖L‖*(C*price q a b i z)*(A*price q c d i z):= by have := price_pos q a b i z; gcongr; exact hi z hz; exact hk z hz
          _ = _:= by ring
   obtain ⟨y,hy⟩:= h.whereL x hp hr z hz; obtain ⟨r,hR⟩:= hx.whereL x hp hr z hz; refine ⟨L y r,?_⟩; let u i:=((ε i ^ (b-a)) • f i (z i)); let w i:= ((ε i ^(d-c)) • g i (z i));
   have heq(i:ℕ): ((ε i)^(b+d-(a+c))) • L (f i (z i)) (g i (z i))= L (u i) (w i):= by unfold u w;simp only [map_smul,ContinuousLinearMap.smul_apply,smul_smul]; rw [add_sub_add_comm,zpow_add₀ (epsilon_pos q _).ne' ,mul_comm (ε i ^ (b-a))]
   have hn: Tendsto (fun i=>L (u i) (w i)) atTop (𝓝 ((fun x:V×W=> L x.1 x.2) (y,r))) := (show Continuous (fun x:V×W=> L x.1 x.2) by fun_prop).continuousAt.tendsto.comp (hy.prodMk_nhds hR)
   exact hn.congr fun i=> (heq i).symm
lemma scales {v:Mist ℝ}(h:Visa q R a b v)(hx:Visa q R c d f): Visa q R (a+c) (b+d) (fun i z=> v i z • f i z):= by
   exact h.pairL hx (ContinuousLinearMap.lsmul ℝ ℝ (E:=V)) -- signature
lemma mulC {f g:Mist ℂ}(h:Visa q R a b f)(p:Visa q R c d g): Visa q R (a+c) (b+d) (f*g):= h.pairL p (ContinuousLinearMap.mul ℝ ℂ)
lemma mulR {f g:Mist ℝ}(h:Visa q R a b f)(p:Visa q R c d g): Visa q R (a+c) (b+d) (f*g):= h.scales p
lemma smultC {f:Mist ℂ}(c:ℂ)(h:Visa q R a b f): Visa q R a b (c • f):= h.mapL ((ContinuousLinearMap.lsmul ℂ ℂ c).restrictScalars ℝ)
lemma com {f:Mist ℝ} (h:Visa q R a b f): Visa q R a b (fun i z=>Complex.ofReal (f i z)):= h.mapL Complex.ofRealCLM
lemma once (f:ℕ→V)(h: Released (fun i=> (ε i ^(-a)) • f i)) : Visa q R a 0 (Once f):= by
   obtain ⟨C,hc,he⟩ := (Released.old h).exists_pos; refine ⟨⟨C,hc.le,?_⟩,fun x hx hr z hz=> ?_⟩
   · filter_upwards [he.bound] with i hi z hz; rw [Once,price,zpow_zero,mul_one]; rw [norm_smul,Real.norm_eq_abs, abs_of_pos (zpow_pos (epsilon_pos q _) _),zpow_neg, inv_mul_eq_div] at hi; exact (div_le_iff₀ (zpow_pos (epsilon_pos q _) _)).mp (by simpa using hi)
   rw [zero_sub]; exact h
lemma fix (x:V): Visa q R 0 0 (Once (fun _=>x)):= once _ (by simp only [neg_zero,zpow_zero,one_smul]; exact ⟨x,tendsto_const_nhds⟩)
lemma powR : Visa q R a 0 (Once (fun i=> (ε i ^ a))) := once _ (by simp only [smul_eq_mul,zpow_neg]; simp only [inv_mul_cancel₀ ((zpow_pos (epsilon_pos q _) _).ne')]; exact ⟨1,tendsto_const_nhds⟩)
lemma asPow (h:Visa q R a b f): Visa q R (c+a) b (fun i z=> ε i ^ c • f i z):= by rw [← zero_add b]; exact powR.scales h -- maybe shapes
lemma prod {I:Type*} (u:Finset I){a b:I→ℤ}{f:I→Mist ℂ}(h:∀ i∈u, Visa q R (a i) (b i) (f i)): Visa q R (∑ i∈u,a i) (∑ i∈u,b i) (∏ i∈u,f i):= by
   induction u using Finset.induction_on with
   | empty=> rw [Finset.sum_empty,Finset.sum_empty,Finset.prod_empty]; exact fix (1:ℂ)
   | insert i u hU IH=> rw [Finset.sum_insert hU,Finset.sum_insert hU,Finset.prod_insert hU]; exact (h i (by simp)).mulC (IH (fun j hj=> h j (by simp [hj])))
end Visa
-- core price for grounded lines
variable {B:GridF}
include hq
lemma bird_comp (z:Cover)(hr:R≥0): ∀ᶠ i:ℕ in Fℕ, lift (wrap (side q i) z)=z:= plot_lift hq (plot.constant hq z)
lemma rooted_bird (hr:R≥0)(h:B∈bird k): Visa q R 0 (-((2+k:ℕ):ℤ)) (fun i z=> B (side q i) 0 z):= by
   let b:=2+k; obtain ⟨c,hc,he⟩:= Print.cost hq h; refine ⟨⟨c*(4:ℝ)^b,by positivity,?_⟩,fun x hx hy z hz=>?_⟩
   · filter_upwards [he,spot_lift hq R] with i hi hh z hz; let n:=side q i; let x:=wrap n z; let f:= B n 0 z; let m:=Print.scale n 0 z; have hm:m>0:= zero_lt_one.trans_le (Print.scale_pos ..); have hp : day z≤4*m:= by
         have he:street z≤4*pdist x:= (show Lattice.lift x=z from hh _ (gate_range R hr z hz)) ▸ round_lift x
         unfold day m; rw [Print.scale,mass_eq,map_zero,zero_sub,pdist_neg]; linarith [show (street z:ℝ)≤4*pdist x by exact_mod_cast he]
     rw [price,zpow_zero,one_mul,zpow_neg,zpow_natCast]; rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos (day_pos z) _)]; calc
         _ ≤ ‖f‖*(4*m)^b:= by have hz:= day_pos z; change ‖f‖*day z^b ≤ _; gcongr
         _ ≤ _:= by rw [mul_comm (4:ℝ) m,mul_pow,← mul_assoc]; gcongr; exact hi ..
   simp only [sub_zero, zpow_neg, zpow_natCast, smul_eq_mul, inv_mul_eq_div]; exact Print.glides hq h hx.symm (plot.constant hq 0) hz
end YM.PositionX.Haze
