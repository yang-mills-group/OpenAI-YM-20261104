import YM.MS.High.Logs
import YM.MS.Pearl.Angel
import Mathlib.Analysis.SpecialFunctions.PolynomialExp
/-!
# `R` stationarity logarithmic pole cohorts
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Pearl
open Set Filter Function Finset MeasureTheory Metric Arc Real Polynomial
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm
open scoped Topology ContDiff Interval
variable {I E:Type} {G:Gauge} {W Y F: Mob G} {x:ℂ} {b:Bool} {n ℓ m:ℕ} {h:ℕ}{s:ℝ}
variable {f g:ℝ→ Mob G}
-- no estimates on λ²/etc.
private lemma flare {a:ℝ}{l:Filter ℝ}(ha:a≠0)(p:Poly)(y:ℝ) (h:Tendsto (fun t=>a*t) l atTop): Tendsto (fun t=> exp (-(a*t))*p.eval (y+t)) l (𝓝 0):= by
    let q := Polynomial.C y + Polynomial.C a⁻¹*X; apply Tendsto.congr _ ((p.comp q).tendsto_div_exp_atTop.comp h); intro t; simp [q,ha,exp_neg]; ring -- parse check
lemma neg_exp {a:ℝ}(p:Poly)(y:ℝ)(h:a<0): Tendsto (fun t:ℝ=> amount (a:ℂ) t*((p.eval (y+t:ℝ):ℝ):ℂ)) atTop (𝓝 0):= by
    obtain he:= Complex.continuous_ofReal.continuousAt.tendsto.comp (flare (a:= -a) (by linarith) p y ((tendsto_const_mul_atTop_of_pos (by linarith:-a>0)).mpr tendsto_id)); convert! he using 1; ext t; simp [amount_mint] -- defeq reduce estate.
lemma pos_exp {a:ℝ}(p:Poly)(y:ℝ)(h:0<a): Tendsto (fun t:ℝ=> amount (a:ℂ) t*((p.eval (y+t:ℝ):ℝ):ℂ)) atBot (𝓝 0):= by
    obtain he:= Complex.continuous_ofReal.continuousAt.tendsto.comp (flare (a:= -a) (by linarith) p y ((tendsto_const_mul_atTop_of_neg (by linarith:-a<0)).mpr tendsto_id)); convert! he using 1; ext t; simp [amount_mint]
lemma wood_rot (p:Poly)(y:ℝ)(h:kPrice F)(n:ℕ): Wind (fun t=> ((p.eval (y+t:ℝ):ℝ):ℂ) • wood (n+1) (-(n:ℂ)) t F) atBot 0:= by
    let z:= -(n:ℂ)-(( (1/2:ℝ):ℝ):ℂ); let x:ℝ:=1/2; have hx:x>0:= by unfold x; norm_num
    obtain hv:= pos_exp p y hx; have hk(t:ℝ): wood (n+1) (-(n:ℂ)) t F=amount (x:ℂ) t • wood (n+1) z t F:= by unfold wood; rw [show -(n:ℂ)= z+(x:ℂ) from Eq.symm (sub_add_cancel (-(n:ℂ)) _), shift] -- may rewrite inside z unfolded?
    simp_rw [hk,smul_comm (p.eval _:ℂ) (amount (x:ℂ) _),← mul_smul]; intro m w; have H0 : 0< z.re+(↑(n+1:ℕ):ℝ):= by unfold z; push_cast; simp; linarith
    convert (hv.smul ( wood_lim h H0 m w )) using 1; rfl; simp -- lint
lemma sumT {E:Type} (S:Finset E){u:E→ Mob G}(hv:∀ i∈S,kPrice (u i))(k:ℕ): Tad (∑ i∈S,u i) k=∑ i∈ S,Tad (u i) k:= by
   classical
   induction S using Finset.induction with
   | empty=> simp only [Finset.sum_empty,tad0]
   | insert i s hi ih=>
       have hp (j:E)(hj:j∈s): kPrice (u j):= hv j (Finset.mem_insert_of_mem hj); rw [Finset.sum_insert hi,Finset.sum_insert hi,t_plus (hv i (by simp)) ( fall_sum s (f:=fun i _=> u i) (fun i hi=>hp i hi) (fun _=>zero_le_one)), ih hp]
lemma reality (c:ℝ)(F:Mob G): (c:ℂ) • F=c•F:= by ext; simp [Complex.real_smul]
lemma cost_k (h:kPrice F)(x:ℂ): kPrice (x • F):= by convert! fall_scale (U:=fun _:Unit=>x) h (const_sc ..) using 1; ext; simp
variable {N:ℕ}(X:ℝ→ Mob G)(hL:X ∈ interest N (Mob G))(hP:∀ y,kPrice (X y)) (hv:∀ t y, plow (-(h:ℂ)) t (X (y+t))=X y)
include hL hP
lemma tad_chart (n:ℕ)(y:ℝ): Tad (X y) n=∑ i∈Finset.range N, (↑((plate N i).eval (y:ℝ)):ℂ) • Tad (X i) n:= by
   obtain hp:= interpret hL y; unfold Logarithm.evaluate at hp; simp_rw [← reality] at hp; rw [hp,sumT _ (fun i _=>cost_k (hP _) _)]; simp_rw [t_pose]; -- maybe nontermination W
lemma clear_chart (n:ℕ)(y:ℝ): Hem.clear n (X y)=∑ i∈Finset.range N,(↑((plate N i).eval (y:ℝ)):ℂ) • Hem.clear n (X i):= by
   unfold Hem.clear haze; simp_rw [show ∀ n,Tad (X y) n= _ from fun n=>tad_chart X hL hP n y, Finset.sum_comm (s:=Finset.range n) (t:=Finset.range N)]; simp_rw [smul_sub,Finset.smul_sum]; rw [ Finset.sum_sub_distrib]; obtain hx:=interpret hL y; unfold Logarithm.evaluate at hx; simp_rw [← reality] at hx; rw [hx]
include hv
lemma eq_wipe (s:ℝ): Hem.clear (h+1) (X s)=0:= by
   let Y:= Hem.clear (h+1) ( X s); have hu(k:ℕ)(t:ℝ): haze k (plow (-(h:ℂ)) t (X (s+t))) = plower (-(h:ℂ)) t (haze k (X (s+t))):= by unfold haze; simp_rw [Tad_scale (hP _),map_sum, cert,move_tad (hP _)]
   have hp (t:ℝ): wood (h+1) ( -(h:ℂ)) t ( X (s+t)) = Y := by unfold wood Y Hem.clear; rw [← cert,map_sub, ← hu,cert,hv]
   suffices H: Wind (fun t=> wood (h+1) (-(h:ℂ)) t (X (s+t))) atBot 0 by rw [funext hp] at H; exact Wind.unique ( F:=Y) (fun _ _=> tendsto_const_nhds) H
   unfold wood; simp_rw [show ∀ t:ℝ, Hem.clear (h+1) (X (s+t))= _ from fun t=>clear_chart X hL hP _ _,← cert,map_sum,map_smul]; intro m l; simp_rw [Finset.sum_apply]; convert (tendsto_finsetSum (Finset.range N) (fun i _=> wood_rot (plate N i) s (hP i) h m l)) using 1; rfl; simp
end YM.MS.Pearl
