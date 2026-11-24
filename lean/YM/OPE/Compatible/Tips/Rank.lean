import YM.OPE.Compatible.Tips.Stroll
import YM.OPE.Compatible.Rave.Orb
import YM.OPE.Compatible.Karls.Jay
import YM.OPE.Compatible.Hike.Piece
import YM.OPE.Compatible.Karls.Bent
import YM.OPE.Compatible.Karls.York
/-!
# H.Launch supplies.Born.Cumul integrations at Mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit.Jac
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P:Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
variable {v v' b:ℝ} {A:Alps K T i v}{D:Alps K T j v'}{U:Boxes G P K.K}
local notation "Zc!"=> solar G d τ
local notation "T!"=> Tracts G d τ
open PriceZ
local notation "L!"=> Tower (Shade G) d τ
local notation "D!"=> Shade G
local notation "Cy"=> solar G d τ
open JetS
open Finset
open PriceZ Hark
open Hark Nestle StageLight Shrew Balsam
variable {a b K F s t:ℝ}{x y:ℕ→ℝ}{D:Gloam}
lemma Swift (D:Gloam)(i:ℕ) : D.h i=D.h 0*(D.q')⁻¹^i:=by
    induction i with | zero=>simp |succ i ih=> rw [D.h_succ, ih,pow_succ]; ring
lemma dive_j (hx:i≠0): Tendsto (fun j=>dye j* D.h j^i) atTop (𝓝 0):=by
     let Q:= D.q'; have ht:= D.qsub; have he:1<Q:=D.qsub; let t:=Q⁻¹^i; have hp:0≤t:=by unfold t; positivity
     have hv:t<1:=pow_lt_one₀ (inv_nonneg.mpr (by linarith)) (inv_lt_one_of_one_lt₀ he) hx; have hf : Tendsto (fun j:ℕ=>dye j*t^j) atTop (𝓝 0):=by
          have h₀:Tendsto (fun j:ℕ=>(j:ℝ)*t^j) atTop (𝓝 0):= by simpa only [pow_one] using! tendsto_pow_const_mul_const_pow_of_lt_one 1 hp hv
          have h₁:=h₀.add (tendsto_pow_atTop_nhds_zero_of_lt_one hp hv); simp only [zero_add] at h₁; exact Tendsto.congr (fun i=>by unfold dye; ring) h₁ -- possible API
     have hx':= hf.const_mul (D.h 0^i); rw [mul_zero] at hx'; apply Tendsto.congr _ hx'; intro j; rw [Swift D j,mul_pow,← pow_mul,mul_comm i j,pow_mul]; unfold Q; ring
lemma Fruit_charge (hp:Bose D k (billX D x k) a):a=0:=by induction k generalizing x with
     | zero=>
       apply tendsto_nhds_unique (a:=a) (b:=(0:ℝ)) hp; unfold booze; rw [show (fun i=>_)=fun _:ℕ=> (0:ℝ) from funext fun i=>by simp [billX]]; exact tendsto_const_nhds
     | succ k ih=>
       have he(i:ℕ):0< dye i:=by unfold dye; positivity
       have hx:Tendsto (billX D x (k+1)) atTop (𝓝 0):=by
           have hy:= hp.mul (dive_j (i:=k+1) (D:=D) (by omega)); rw [mul_zero] at hy; apply hy.congr; intro i; unfold booze; exact div_mul_cancel₀ _ (ne_of_gt (mul_pos (he _) (pow_pos (D.h_pos _) _)))
       have ht:x 0=0:= tendsto_nhds_unique (van x) hx; let p:=fun i:ℕ=>x (i+1); apply ih (x:=p); refine hp.congr (fun i=>?_) -- maybe reversed
       unfold booze billX; simp only [sum_range_succ',ht,coral,smul_eq_mul, p]; simp only [mul_zero,add_zero]; simp only [pow_succ']; simp_rw [mul_assoc (D.h i),← mul_sum]; have hx:= D.h_pos i; have ht:=he i; field_simp
lemma tickle_b (h:Fruit D k x 0)(hp:Bose D k x a):a=0:=by
    obtain ⟨b,H⟩:=h; let f:=billX D b k; apply Fruit_charge (D:=D) (k:=k) (x:=b); change Tendsto _ _ _; have he:= hp.sub H; rw [sub_zero] at he; exact Tendsto.congr (fun z=>by unfold booze; rw [←sub_div,Pi.sub_apply,sub_sub_cancel]) he
lemma Skrew (h:0 < s)(hp: Thick s x): Tendsto (fun i=> s⁻¹^i*x i) atTop (𝓝 0):=by
    obtain ⟨⟨q,hq,hv,c,H⟩⟩:=hp; let t:=s⁻¹*q; have ht:= (tendsto_pow_atTop_nhds_zero_of_lt_one (mul_nonneg (inv_nonneg.mpr h.le) hq) (show s⁻¹*q<1 from by rw [←div_eq_inv_mul,div_lt_one h];exact hv)).const_mul c; rw [mul_zero] at ht; refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun i=>norm_nonneg _) ?_ ht)
    intro i; simp only[norm_mul]; rw [Real.norm_of_nonneg (by positivity :0 ≤ s⁻¹^i),mul_pow]; exact (mul_le_mul_of_nonneg_left (H i) (by positivity)).trans_eq (by ring)
lemma timbrePart {x:ℕ→ℝ}{t r a:ℝ}(h:0<t)(hp:∀ i,D.h i ^ k = D.h 0^k*t^i)(hw:Thick t (fun i=>x i-t^i*(r+(i:ℝ)*a))) (hv: Fruit D k x 0):a=0:=by
    have he:=tickle_b hv (a:=a/(D.h 0^k)) -- yields Bose→ div=0
    have hy:Tendsto (fun i:ℕ=> (r+(i:ℝ)*a)/(dye i)) atTop (𝓝 a):=by
         have hT:=(tendsto_inv_atTop_zero.comp notor).const_mul (r-a); rw [mul_zero] at hT; have ht:= hT.const_add a; rw [add_zero] at ht; apply Tendsto.congr _ ht; intro i; have hy:dye i=↑i+1:=rfl; have he:(1+(i:ℝ))≠0:=by positivity
         change a+(r-a)* (dye i)⁻¹=_; rw [hy]; field_simp; ring
    have ht:= ((Skrew h hw).mul (tendsto_inv_atTop_zero.comp notor)).add hy; simp only [mul_zero,zero_add] at ht; apply (div_eq_zero_iff.mp (he ?_)).resolve_right (ne_of_gt (pow_pos (D.h_pos _) _)); apply Tendsto.congr _ (ht.div_const (D.h 0^k)); intro i; change ( t⁻¹^i*(x i- t^i*(r+(i:ℝ)*a))*(dye i)⁻¹+ (r+_*a)/(dye i))/(D.h 0^k)=booze D k x i; unfold booze; rw [hp i]; have hb:=D.h_pos 0; have he(i:ℕ): dye i≠0:=by unfold dye; positivity
    rw [inv_pow]; have hj:=he i; field_simp; ring
end YM.OPE.Quit.Jac
