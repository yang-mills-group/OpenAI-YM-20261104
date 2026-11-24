import YM.MSbar.Atlas.Apex
/-! Pricing index increases only after these demands.Ever fixed X.Tail germ. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath.Stock
open Lattice Wilson RG Function Filter MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{c f:Side}{S:StepData c f}
open Precision Tree Pressure Push Push.AbsoluteSums ConnectedActivityE6 Push.Uniform
open Heath Bulk
-- scale r cost arm measured chart. Fine-hat.L
variable (P: Patch)(K : KernelChoices)(J:Voice G)
set_option quotPrecheck false
local notation "L"=> P.L
-- threshold width d.root.Blog score.Y
variable (s:Palisade) (Y : Stage)
-- true scale.envelops independent.Charge.Depends G implicit use G arg.
def distance (x:ℝ):= x ^ (-(1/2:ℝ))* Real.log x
def skies (x:ℝ):= distance x * Real.log x
def increments (x:ℝ) := x^(-(6/5:ℝ))
def ceiling (x:ℝ):= x^(-(49/100:ℝ))
def arch (x:ℝ):= x^(-(48/100:ℝ))
def base (J:Voice G)(x:ℝ):= 8*J.C*shade G*skies x
def unit (G:Gauge)(s:Palisade):= 1+shade G*|ice s.coords s.gap s.a s.density|
def steps (G:Gauge)(s:Palisade)(x:ℝ):= unit G s * increments x
def stockMove (G:Gauge)(s:Palisade)(x:ℝ):= 2*steps G s x
def winch (x:ℝ):=increments x*x^(-(2/5:ℝ))
local notation "Ξ"=> tip G L
lemma wi (G:Gauge)(s:Palisade):0<unit G s:=by unfold unit; have hv:= shade_pos G; positivity
lemma met:Rate G L (-(1/2)) (distance ∘ Ξ):=by simpa only [distance,Function.comp_def,add_zero] using! ((Rate.power (G:=G) («L»:=L) (a:= -(1/2))).mul ((Beam.logfine G L).tick))
lemma flog: Rate G L (-(1/2)) (skies∘Ξ):=by simpa only [skies, Function.comp_def,add_zero] using! ((met P (G:=G)).mul ((Beam.logfine G L).tick))
lemma line (g : Clear G J)(u:ℝ)(hx:0<u) : ∀ᶠ x in atTop, 0<ceiling (Ξ x) ∧ 0< increments (Ξ x) ∧ 0<arch (Ξ x)∧0<base J (Ξ x)∧ steps G s (Ξ x)≤arch (Ξ x)∧J.C*(ceiling (Ξ x)+base J (Ξ x)/4) ≤ arch (Ξ x)∧ arch (Ξ x)≤ J.r ∧ J.C*steps G s (Ξ x)+(ceiling (Ξ x)+base J (Ξ x)/4) ≤ J.δ ∧ max (skies (Ξ x)) (arch (Ξ x))+stockMove G s (Ξ x)<u:=by
   let A:= -(49/100:ℝ); let B:=-(48/100:ℝ); let t:=-(6/5:ℝ); let F:= base J∘Ξ
   have hg:Rate G L t (steps G s∘Ξ):=Rate.power.mul_left _; have he:Rate G L A (ceiling∘Ξ):=Rate.power
   have hF:Rate G L (-(1/2)) F:=(flog P (G:=G)).mul_left _; let D x:=ceiling (Ξ x)+F x*(4:ℝ)⁻¹
   have ht : Rate G L A D:= he.add ((hF.mul_right _).weaken (by norm_num [A])); have hd:Rate G L B (arch∘Ξ):=Rate.power
   have hzk : A<B:=by norm_num [A,B]
   have hz:t<A:=by norm_num [t,A]
   have hy:B <0:=by norm_num [B]
   have hv:=g.cost
   have hh:0<J.C:=zero_lt_one.trans_le g.cost
   have hk:u/3>0:=by positivity
   let q:= stockMove G s
   have hq:Rate G L t (q∘Ξ):= hg.mul_left 2
   filter_upwards [(Work.E09.betaF_growth G L).eventually_gt_atTop 1,hg B (hz.trans hzk),ht.mul_left J.C B hzk,
      hd.below hy _ g.depth,(((hg.mul_left J.C).weaken hz.le).add ht).below (hzk.trans hy) _ g.dist,(flog P (G:=G)).below (by norm_num) _ hk,hd.below hy _ hk, hq.below (hz.trans (hzk.trans hy)) _ hk] with x hx' hA hB he hg hS hz hQ
   let X:= Ξ x; have hm:0<X:=zero_lt_one.trans hx'; have hv:0<skies X:=by unfold skies distance; have h:=Real.log_pos (show 1<X from hx'); positivity
   refine ⟨Real.rpow_pos_of_pos hm _,Real.rpow_pos_of_pos hm _,Real.rpow_pos_of_pos hm _,?_ ,(le_abs_self _).trans hA,?_,(le_abs_self _).trans he,?_,?_⟩
   · unfold base; have hx:=shade_pos G; change 0<_*skies X; positivity
   · rw [div_eq_mul_inv]; exact (le_abs_self _).trans hB
   · rw [div_eq_mul_inv]; exact (le_abs_self _).trans hg
   refine lt_of_le_of_lt (add_le_add (max_le ?_ ?_) (show _≤ u/3 from (le_abs_self _).trans hQ)) (show u/3+u/3 <u by linarith)
   exact (le_abs_self _).trans hS; exact (le_abs_self _).trans hz
lemma torch (g : Clear G J)(hm:0<s.gap)(hs:0<s.a)(hp:0<s.density): ∀ᶠ x in atTop, ∀ t:ℝ, |t|=increments (Ξ x) → Floss s J t (steps G s (Ξ x)) (arch (Ξ x)) (winch (Ξ x)) (base J (Ξ x)) (ceiling (Ξ x)) (skies (Ξ x)) (stockMove G s (Ξ x)) (2*winch (Ξ x)) (radiusB (Ξ x)):=by
   let a:= tiltWidth s.coords (s.gap/2) s.a s.density /2; let k:=ice s.coords s.gap s.a s.density; have hx:0<a:=half_pos (tiltWidth_pos _ (half_pos hm) hs hp.le); have he:0≤k:= by unfold k ice; have hC:= count_pos hx; unfold a at hC; positivity
   let D x:=Real.exp (-a* radiusB (Ξ x)); have hd:Pole G L D:=Pole.cape L G hx
   let e:= -(2/5:ℝ); filter_upwards [(hd (e-1)|>.mul_right k) e (by linarith only), Rate.power.below (G:=G) («L»:=L) (show e<0 by norm_num [e]) _ zero_lt_one,line P J s g _ s.first, shiftedLog G L] with x hz hf h hv t ht
   let y:=Ξ x; have H:= wi G s; have hS:= shade_pos G; have hT: shade G*k≤unit G s:=le_trans (mul_le_mul_of_nonneg_left (le_abs_self _) hS.le) (le_add_of_nonneg_left zero_le_one); have hh:k≤ unit G s:= (le_mul_of_one_le_left he (shade_one _)).trans hT; obtain ⟨ha,hB,hD,hb,hQ,hc,hW,hA,hL⟩:=h
   refine ⟨ha.le,hb,?_,mul_nonneg H.le hB.le,hQ,hc,hW,hA,hL,?_,?_⟩
   · rw [ht, mul_left_comm, mul_comm]; exact (mul_le_mul_of_nonneg_right hT hB.le)
   · have hx: winch y≤ steps G s y:=by unfold winch steps; rw [mul_comm (increments _)]; exact mul_le_mul_of_nonneg_right (((le_abs_self _).trans hf).trans (show 1≤unit G s from le_add_of_nonneg_right (mul_nonneg hS.le (abs_nonneg _)))) hB.le
     rw [ht, stockMove]; linarith only [hx, (show increments y*k ≤ steps G s y from (mul_comm (increments _) _).trans_le (mul_le_mul_of_nonneg_right hh hB.le))] -- normalize.Ix
   rw [ht]; have hp := (show Real.exp (-a*radiusB (Ξ x))*k ≤ (Ξ x)^e from (le_abs_self _).trans hz); linarith only [show increments y*(Real.exp (-a*(radiusB y:ℝ))*k) ≤ winch y from mul_le_mul_of_nonneg_left hp hB.le]
end YM.MSbar.Heath.Stock
