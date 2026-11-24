import YM.X.Charting.Sell
import YM.X.Clear.Rafter
import YM.PertExtension.PlaneCovariance
/-!
# A typical image kills all powers on required compact regime. Bulk normal-ordered self CT covariance.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Hinge
open Function Filter Set Metric MeasureTheory Lattice Wilson PertExtension PertExtension.Series PertExtension.Series.Radial
open Source ProjectorNext.Calibration Gauss Next.Rank Normal MvPolynomial Finsupp
open Feyn Gauge LatticePT PertExtension.Orb Chart Stems PertExtension.Series.Tested Finset Interval Size Asymptotics
open Pert.Orb (formElem covar image takeDiv gZ positiveLinks wilson Potential form formL curL dLin bridgeEquiv)
open scoped Topology ContDiff BigOperators Classical RealInnerProductSpace
variable {G:Gauge} {n:Side} {q:ℕ+}(hq:1<q.val)
local notation "E"=> Potential G n
local notation "r"=> (atTop:Filter ℕ)
variable (x y:Beam q) (i j:Hair G)
variable (a b :Atom G)
local notation "J" n=> Jam n G

include hq
lemma typical : ∃ c> (0:ℝ), ∀ᶠ k:ℕ in atTop,∀ v:Site (side q k), |green v| ≤ c/(1+pdist v:ℝ)^2:= by
   obtain ⟨C,hC,H⟩ := torus_rate (paths hq) []; refine ⟨max C 1, lt_max_of_lt_right (by norm_num),H.mono (fun k hk v => ?_)⟩; exact (hk v).trans (div_le_div_of_nonneg_right (le_max_left C _) (by positivity))

variable (V W:(i:ℕ)→Jam (side q i) G)
lemma bounded_sells : Ripe q (fun i=>(sale.cov (V i) (W i))) 0:= by
   obtain ⟨C,hC,H⟩:=typical hq; apply Ripe.costed (a:=C); filter_upwards [H] with i hi; unfold sale dev; simp only [RCLike.norm_ofReal,Complex.norm_real]; split
   next u=> exact (hi _).trans (div_le_self hC.le (one_le_pow₀ (by simp)))
   exact le_trans (norm_zero ..).le hC.le
lemma sells_far (h : Away (q:=q) (fun i=>(V i).1.1) (fun i=>(W i).1.1)): Vanished q (fun i=>(sale.cov (V i) (W i))) := by
   obtain ⟨C,hC,H⟩:= typical hq; obtain ⟨c,hc,W'⟩:= h.circ; let f(k):= ((side q k).val:ℝ)⁻¹
   refine Vanished.previous (IsBigO.of_bound (C/c) ?_) (show Vanished q f from Vanished.side_small hq)
   filter_upwards [W',H] with k hk h; let i:=V k;let j:= W k;let p:= pdist (j.1.1-i.1.1);let F:ℝ:= (side q k).val; have hF:0<F:=by unfold F; positivity
   change _ ≤ C/c * ‖f k‖; change c*F≤(p:ℝ) at hk
   unfold sale dev; simp only [Complex.norm_real]; rw [Real.norm_of_nonneg (show 0≤f k from (inv_pos_of_pos hF).le)]; split
   next u=> apply (h _).trans; change C/(1+p:ℝ)^2≤C/c * F⁻¹; rw [← div_eq_mul_inv,div_div]; apply div_le_div_of_nonneg_left hC.le (by positivity) _; nlinarith only [hk,hc,hF,Nat.cast_nonneg (α:=ℝ) p, sq_nonneg (p:ℝ)]
   rw [norm_zero]; unfold f; positivity
lemma minus_fee {O:Beam q} (hw:Away O (-O)) (hx:Near O x)(hy:Near O y):Vanished q (fun k=> thermal water (x k) (y k) i j-thermal sale (x k) (y k) i j):= by
   let v(k):=place (x k) i; let w(k):=place (y k) j
   have H: Away (-O) (fun k=>(w k).1.1):=(hw.smaller hq (Near.onward hy (Near.tours j.1.1))).circ
   let U(k):= reverseK (v k)
   have hU : Near (-O) (fun i=>(U i).1.1):= by
      let z:= -i.1.1-step i.1.2; have hv: (fun k=>(U k).1.1)=(fun k=>(wrap (side q k) z)+(-x) k):= by unfold U v; funext k; change -(wrap (side q k) i.1.1 + x k)-step i.1.2= _; simp only [z,map_sub,map_neg,wrap_step,Pi.neg_apply]; abel
      rw [hv]; exact Near.onward hx.negative (Near.tours z)
   have hD : Vanished q (fun k=>sale.cov (U k) (w k)):= sells_far hq _ _ (H.smaller hq hU)
   refine Eq.mp ?_ hD.neg; congr 1; ext1 k; rw [thermal,thermal,water_dev]; change -((dev (U k) (w k):ℝ):ℂ)= ↑(dev (v k) (w k)- dev (U k) (w k))- ((dev (v k) (w k):ℝ):ℂ); rw [Complex.ofReal_sub]; ring
lemma water_sale {O} (hw:Away O (-O))(hx:Near O x): Vanished q (fun k=> (via water (x k)).cov a b-(via sale (x k)).cov a b):= by
   have H (i j:Hair G):Vanished q (fun k=> (scopedK water (x k)).cov i j-(scopedK sale (x k)).cov i j) := by simp_rw [← self_thermal]; exact minus_fee hq x x i j hw hx hx
   let d:= com (iris a);let e:= com (iris b); let t(Q:Symmetric (Hair G)) u v := e v*(d u * Q.cov u v)
   let F(k)(Q : Symmetric (Jam (side q k) G)):= (scopedK Q (x k)); have ht(k)(Q):(via Q (x k)).cov a b=∑ v∈e.support,∑ u∈d.support,t (F k Q) u v:= by unfold via scope treats; simp only [Function.comp_apply,F,t,d,e,linearCombination_apply,Finsupp.sum, Finset.sum_apply,Pi.smul_apply,smul_eq_mul, Finset.mul_sum]
   simp_rw [ht,← Finset.sum_sub_distrib,t,←mul_sub]; apply Eq.mp ?_ (Vanished.finSum (s:=e.support) (f:=fun v=>∑ u∈d.support,(fun k=>e v*(d u*((F k water).cov u v-(F k sale).cov u v)))) fun i _=>Vanished.finSum fun j _=> Vanished.right (Charged.constant (e i)) (Vanished.right (Charged.constant (d j)) (H j i))); congr 1; funext k; simp [Finset.sum_apply]
lemma actual_self (i j:Atom G): Vanished q (fun k=> (via sale (0:Site (side q k))).cov i j - (covarianceSymbol G).cov i j):= by
   choose x hx using fun k=> hasOrigin q k
   let o:= Screens.positiveLift x; let O:= stared (q:=q) o; have hO:Screens.Placement q o:= Screens.placement q x hx
   let A k := (via sale (0:Site (side q k))).cov i j; let B k := (via water (O k)).cov i j
   have he : Vanished q (B-A):= by
      have ht:= water_sale (G:=G) hq (O) i j (stares o hO) (Near.around _)
      simp_rw [via,sale_self] at ht -- via unfolds aq inside? 
      exact ht
   have hb : Vanished q (B - fun _ => (covarianceSymbol G).cov i j):= by
      let p (v :Fin 1):ℕ→Cover:=0
      apply Vanished.all; intro d
      have hy:= image_zone (G:=G) (x:= (0:Points 1)) (U:=p) hq hO (fun v=> ?hh) i j d 0
      case hh => simp_rw [p,Pi.zero_apply,show CellsInt.mapZ 0= (0:E4) from PiLp.ext (fun i=> by simp [CellsInt.mapZ]),smul_zero]; exact tendsto_const_nhds
      apply Ripe.eventual (B:=1)
      filter_upwards [hy.norm.eventually (ge_mem_nhds (show ‖(0:ℂ)‖<(1:ℝ) from by norm_num))] with k hk; rw [norm_smul , Real.norm_of_nonneg (show 0≤magnify q k^d from (pow_pos (amp_pos q k) d).le)] at hk -- inspect
      change ‖B k-_‖≤_; rw [ticket_neg,one_mul,eps_eq,inv_pow]; unfold B O stared; rw [agrees (G:=G) (side_even q k)]; simp [p,Screens.withOrigin] at hk -- preserve
      field_simp; linarith
   exact (show Vanished q (A-fun _=>(covarianceSymbol G).cov i j) from (show A-(fun _=>(covarianceSymbol G).cov i j)= (B-(fun _=>(covarianceSymbol G).cov i j))-(B-A) from (by abel)) ▸ hb.sub he) -- ▸ direction
end YM.PositionX.Hinge
