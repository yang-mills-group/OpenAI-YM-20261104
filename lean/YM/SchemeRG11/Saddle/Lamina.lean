import YM.Pert.Lattice.Series
import YM.SchemeRG11.Saddle.Peat
/-! Formal moment adapter. Unnormalized times real density tracked. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.SchemeRG11.Sway.Lam
open Function Filter Set MeasureTheory Metric PertExtension.Series Radial Tested
open scoped Classical ContDiff Topology BigOperators NNReal PowerSeries
open Pert.Orb Local
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
local notation "coeff" => PowerSeries.coeff (R:=ℂ)
def raise : ℝ⟦X⟧ →+* ℂ⟦X⟧:= PowerSeries.map Complex.ofRealHom
lemma raise_inv{u:ℝ⟦X⟧}(h:PowerSeries.constantCoeff u≠0): raise u⁻¹=(raise u)⁻¹:=by
 have hv: PowerSeries.constantCoeff (raise u)≠0:=by unfold raise; rw [←PowerSeries.coeff_zero_eq_constantCoeff,PowerSeries.coeff_map,PowerSeries.coeff_zero_eq_constantCoeff]; exact Complex.ofReal_ne_zero.mpr h
 refine ((PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hv)).mul_right_inj).mp ?_
 rw [← map_mul, PowerSeries.mul_inv_cancel _ h,map_one,PowerSeries.mul_inv_cancel _ hv]

def ChartC (f:E→ℂ)(x:E):ℂ⟦X⟧:=PowerSeries.mk fun i=>(i.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ i f 0 (fun _=>x)
lemma chart_line {f:E→ℝ}(h:ContDiffAt ℝ ∞ f 0)(x:E): ChartC (fun y=>(f y:ℂ)) x= raise (PowerSeries.mk fun i=>jet f i x):=by
 ext i; unfold ChartC raise; rw [PowerSeries.coeff_map,PowerSeries.coeff_mk,PowerSeries.coeff_mk]; change _= (↑(jet f i x):ℂ)
 let L:= Complex.ofRealCLM
 rw [show iteratedFDeriv ℝ i (fun y=>(f y:ℂ)) 0= L.compContinuousMultilinearMap (iteratedFDeriv ℝ i f 0) from L.iteratedFDeriv_comp_left h (Local.order_le_smooth i)]
 rw [jet]; exact (map_smul L ..).symm
lemma chart_ready(f:E→ℂ): Ready (ChartC f):= by
 exact Ready.maker (fun i=> (Tame.jet (ContinuousLinearMap.id ℝ E) (iteratedFDeriv ℝ i f 0)).scalar_const ((i.factorial:ℝ)⁻¹))
lemma chart_ray {f:E→ℂ}(h:ContDiffAt ℝ ∞ f 0)(x:E)(n): coeff n (ChartC f x)=(n.factorial:ℝ)⁻¹ • iteratedDeriv n (fun t:ℝ=>f (t • x)) 0:=by
 -- prove by projecting scalar components, no complex differentiability assumptions
 let L(k:ℕ):=(n.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ k f 0 (fun _=>x)
 let g(t:ℝ):=f (t • x)
 have hg:ContDiffAt ℝ ∞ g 0:= by
    let L:= ContinuousLinearMap.toSpanSingleton ℝ x
    exact ContDiffAt.comp (f:=L) 0 (by rw [map_zero]; exact h) L.contDiff.contDiffAt
 have he(P:ℂ→L[ℝ]ℝ): P (coeff n (ChartC f x))= P ((n.factorial:ℝ)⁻¹ • iteratedDeriv n g 0):=by
    have ha : jet (P ∘ f) n x= P (coeff n (ChartC f x)):= by
       unfold jet ChartC; rw [P.iteratedFDeriv_comp_left h (order_le_smooth n),PowerSeries.coeff_mk,map_smul]; rfl
    rw [← ha,homogeneous_derivative _ _ _ ((P.contDiff.contDiffAt.comp (f:=f) 0 h).of_le (order_le_smooth n)),map_smul, iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv,show iteratedFDeriv ℝ n (fun t:ℝ=> (P ∘ f) (t • x)) 0=P.compContinuousMultilinearMap (iteratedFDeriv ℝ n g 0) from P.iteratedFDeriv_comp_left hg (order_le_smooth n)]; rfl
 exact Complex.ext (he Complex.reCLM) (he Complex.imCLM)
lemma chart_add {f g:E→ℂ}(h:ContDiffAt ℝ ∞ f 0)(H:ContDiffAt ℝ ∞ g 0): ChartC (fun u=>f u+ g u)=ChartC f+ ChartC g:=by
 ext1 x; ext i
 simp only [Pi.add_apply,map_add,ChartC, PowerSeries.coeff_mk]; rw [show iteratedFDeriv ℝ i (fun u=> f u+g u) 0  = _ from iteratedFDeriv_add_apply (h.of_le (order_le_smooth i)) (H.of_le (order_le_smooth i)),add_apply,smul_add]
lemma chart_mul {f g:E→ℂ}(h:ContDiffAt ℝ ∞ f 0)(H:ContDiffAt ℝ ∞ g 0): ChartC (fun u=>f u*g u)=ChartC f * ChartC g:=by
 ext1 x; ext i; rw [chart_ray (f:=fun u=>f u*g u) (h.mul H), Pi.mul_apply, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k l => coeff k (ChartC f x)* coeff l (ChartC g x)) i]
 let L:= ContinuousLinearMap.toSpanSingleton ℝ x
 let F:= f ∘ L; let J:=g ∘ L
 have hf: ContDiffAt ℝ ∞ F 0:=ContDiffAt.comp (f:=L) 0 (by rw [map_zero]; exact h) L.contDiff.contDiffAt
 have hg: ContDiffAt ℝ ∞ J 0:=ContDiffAt.comp (f:=L) 0 (by rw [map_zero]; exact H) L.contDiff.contDiffAt
 rw [show (fun t:ℝ=>f (t • x)*g (t • x))=F*J from rfl, iteratedDeriv_mul (hf.of_le (order_le_smooth i)) (hg.of_le (order_le_smooth i)),Finset.smul_sum]
 refine Finset.sum_congr rfl fun j hj=>?_; rw [chart_ray h,chart_ray H]
 have ht : j≤ i:= Nat.le_of_lt_succ (Finset.mem_range.mp hj)
 have hne(k:ℕ): (k.factorial:ℂ) ≠0:= by exact_mod_cast Nat.factorial_ne_zero k
 have hv : (i.choose j:ℂ) * (j.factorial:ℂ) * ((i-j).factorial:ℂ) = (i.factorial:ℂ):= by exact_mod_cast Nat.choose_mul_factorial_mul_factorial ht
 simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_natCast]
 change _=(_*iteratedDeriv j F 0)*(_ * iteratedDeriv (i-j) J 0)
 rw [show (i.choose j:ℂ)=(i.factorial:ℂ)*(j.factorial:ℂ)⁻¹*((i-j).factorial:ℂ)⁻¹ from by rw [← hv]; field_simp [hne]]
 field_simp [hne]
lemma chart_const (c:ℂ): ChartC (fun _:E=>c)=fun _=>PowerSeries.C c:=by
 ext1 x; ext k; cases k with
 | zero=> simp [ChartC]
 | succ k=> rw [chart_ray contDiffAt_const]; simp [iteratedDeriv_const]

/-- Vertices beyond gaussian. Same raw exponential rule as baseline. -/
def baseR (S:E→ℝ)(x:E):ℂ⟦X⟧:= raise (PowerSeries.mk fun i=>layers S i x)
def fitR (K:E→ℝ)(x:E):ℂ⟦X⟧:= raise (PowerSeries.mk fun i=>jet K i x)
def fibers(S K:E→ℝ):=expR (baseR S)*fitR K
lemma cscale(P:ℝ⟦X⟧)(i:ℕ): coeff i (raise P)=(↑(PowerSeries.coeff i P):ℂ):= PowerSeries.coeff_map ..
lemma factorR(K f:E→ℝ)(x:E)(i:ℕ): coeff i (fibers f K x)=(↑(integrandSeries f K i x):ℂ):=by
 have he (k j:ℕ): coeff k (baseR f x ^ j) = ((Zone.TaylorPow (layers f) j k x:ℝ) :ℂ):=by
    induction j generalizing k with
    | zero=> by_cases h:k=0 <;> simp [Zone.TaylorPow,h,PowerSeries.coeff_one]
    | succ j ih=> simp only [Zone.TaylorPow,Zone.mul,pow_succ,PowerSeries.coeff_mul,Complex.ofReal_sum]; exact Finset.sum_congr rfl fun i _=>by rw [ih,baseR,cscale, Complex.ofReal_mul,PowerSeries.coeff_mk]
 have hx(j:ℕ): coeff j (expR (baseR f) x) = (↑(expsum (layers f) j j x):ℂ):=by unfold expR expsum; rw [PowerSeries.coeff_mk,Complex.ofReal_sum]; apply Finset.sum_congr rfl; intro l _; rw [he]; push_cast; rfl
 rw [fibers,mul_comm,Pi.mul_apply,PowerSeries.coeff_mul,integrandSeries,Zone.mul, Complex.ofReal_sum]
 exact Finset.sum_congr rfl fun j _=> by rw [Complex.ofReal_mul,fitR,cscale,PowerSeries.coeff_mk,hx]
lemma factor_ready(S K:E→ℝ): Ready (fibers S K):=by
 have hf(P:E→ℝ)(k):Tame (jet P k):= (Tame.jet (ContinuousLinearMap.id ℝ E) (iteratedFDeriv ℝ k P 0)).scalar_const _
 have hu: Ready (fitR K):=by
   intro k; simp_rw [fitR,cscale,PowerSeries.coeff_mk]; exact (hf K k).ofReal
 apply Ready.mul (Ready.exp ?_) hu
 intro k; simp_rw [baseR,cscale,PowerSeries.coeff_mk]; apply Tame.ofReal
 by_cases hk:k=0
 · rw [hk,show layers S 0=(fun _=>0) by funext; simp [layers]]; exact Tame.constant (0:ℝ)
 rw [show layers S k=(-1:ℝ) • (jet S (k+2)) by funext; simp [layers,hk]]; exact (hf S _).scalar_const (-1)
end YM.SchemeRG11.Sway.Lam
