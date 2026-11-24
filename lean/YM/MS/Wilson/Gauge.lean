import YangMills.WilsonProof.NativeSupport.YM.MS.Wilson.LieWords
import YM.MS.Bare.Divergence

/-!
# Gauge acts on all links of finite full torus

Also for alias tests with arbitrary shifts. All positions and oriented symbols
 kept at the root in stencils later. From identity component. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Native.Chart
open Function Filter Finset Set Plane Koszul Cylinder Taylor Lattice Landau Bare Focus
open scoped Topology Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge} {P:Type} [AddCommGroup P]
abbrev City (G:Gauge)(P:Type):= Lot G (Edge P)
abbrev Rail (P:Type):= Axis→P
def endRail (d:Rail P) (x:Edge P): P:=x.1+d x.2
variable (d: Rail P)
def route (x:Edge P) : Lot G P →ₗ[ℝ] Maurer.Ends G:= (LinearMap.proj x.1).prod (LinearMap.proj (endRail d x))
lemma routed (x:Edge P)(U:Lot G P): route d x U=(U x.1,U (endRail d x)):= rfl
-- analytic generator on any frame

def roam (d:Rail P)(a:City G P): Lot G P→ₗ[ℝ] City G P:= LinearMap.pi fun e:Edge P=> (Maurer.voltage (a e)).comp (route d e)
variable [DecidableEq P]
def loco (d:Rail P)(u:Eyes G P)(a:City G P) := roam d a (priv u)
lemma consulted (u:Eyes G P)(a:City G P)(i:Edge P): loco d u a i= Maurer.volts (route d i (priv u)) (a i):= rfl

variable [Fintype P]
lemma ride (u:Eyes G P): germ (loco d u):= contDiffAt_pi.mpr (fun i=> (show germ (Maurer.volts (route d i (priv u))) from Maurer.home _).comp (f:=fun a:City G P=> a i) 0 (contDiff_apply ..|>.contDiffAt)) -- inspect
lemma car_d {u:Eyes G P}{a b: City G P} (h: DifferentiableAt ℝ (loco d u) a)(x:Edge P) (he: DifferentiableAt ℝ (Maurer.volts (route d x (priv u))) (a x)): fderiv ℝ (loco d u) a b x=fderiv ℝ (Maurer.volts (route d x (priv u))) (a x) (b x):= by
    let X: City G P→L[ℝ] G.Color:= ContinuousLinearMap.proj x; let V:=Maurer.volts (route d x (priv u)); have hv : X ∘ loco d u= V ∘ X :=rfl
    have ht:= fderiv_comp a X.differentiableAt h; rw [hv,fderiv_comp a (show DifferentiableAt ℝ V (X a) from he) X.differentiableAt,X.fderiv,X.fderiv] at ht
    exact DFunLike.congr_fun ht.symm b
lemma costs (i j:Eyes G P) : ∀ᶠ a in 𝓝 0, fderiv ℝ (loco d j) a (loco d i a) - fderiv ℝ (loco d i) a (loco d j a)=∑ k:Eyes G P,colorTerm G P i j k • loco d k a:= by
    obtain ⟨r,hr,H⟩:=LocalH.geom_patch G
    filter_upwards [eventually_all.mpr (fun e:Edge P=> (show ∀ᶠ a:City G P in 𝓝 0,a e∈ Metric.ball 0 r from (continuous_apply (A:=fun _:Edge P=>G.Color) e|>.tendsto (0:City G P)).eventually (Metric.ball_mem_nhds _ hr))), (ride d i).eventually (by simp), (ride d j).eventually (by simp)] with a ha hI hJ
    have he : ∑ k,colorTerm G P i j k • loco d k a=roam d a (Native.braid (priv i) (priv j)):= by rw [← crowd,map_sum]; simp only [map_smul,loco]
    rw [he]; funext x; simp only [Pi.sub_apply,(car_d d (u:=i) (hI.differentiableAt (by simp)) x ((Maurer.analytic_volts _ (H r (le_refl r)) (ha x)).differentiableAt (by simp))),car_d d (u:=j) (hJ.differentiableAt (by simp)) x ((Maurer.analytic_volts _ (H r (le_refl r)) (ha x)).differentiableAt (by simp)),consulted]
    exact Maurer.storm _ _ (H r (le_refl r)) (ha x)
lemma vibes : Vibes (colorTerm G P) (loco d):= ⟨cartan ..,ride d,costs d⟩

-- divergence. receive Haar sum.
def totalH (a:City G P) :=∑ i:Edge P,Maurer.lac (a i)
omit [AddCommGroup P] [DecidableEq P] in
lemma nice_totalH : germ (totalH (G:=G) (P:=P)):= ContDiffAt.sum (fun i _=> (Maurer.hlog G).comp (f:=fun a:City G P=>a i) (0:City G P) (contDiff_apply ..|>.contDiffAt))
omit [AddCommGroup P][DecidableEq P] in
lemma e_total {a v: City G P}(h:∀ i:Edge P,DifferentiableAt ℝ (Maurer.lac (G:=G)) (a i)): fderiv ℝ (totalH (G:=G) (P:=P)) a v=∑ i: Edge P, fderiv ℝ Maurer.lac (a i) (v i):= by
    let T i : City G P→L[ℝ] G.Color:= ContinuousLinearMap.proj i
    have hh i:= (h i).hasFDerivAt.comp (f:=⇑(T i)) a (T i).hasFDerivAt; rw [show fderiv ℝ totalH a=_ from (HasFDerivAt.fun_sum fun i _=> hh i).fderiv]; simp; rfl

lemma welcome (k:Eyes G P) : ∀ᶠ a:City G P in 𝓝 0, Focus.index_div (glow G P) (loco d k) a=∑ i:Edge P,Maurer.divs (Maurer.volts (route d i (priv k))) (a i):=by
    let V (x:Edge P) := Maurer.volts (route d x (priv k))
    filter_upwards [(ride d k).eventually (by simp),eventually_all.mpr (fun x:Edge P=> (continuous_apply x|>.tendsto (0:City G P)).eventually ((Maurer.home (route d x (priv k))).eventually (by simp)))] with a ha he
    unfold Focus.index_div; rw [Finset.sum_apply,Fintype.sum_prod_type]; refine Finset.sum_congr rfl (fun i _=>?_)
    rw [Maurer.by_row]; apply Finset.sum_congr rfl; intro j _; have hv : DifferentiableAt ℝ (loco d k) a:= ha.differentiableAt (by simp)
    change fderiv ℝ (projector (i,j)∘loco d k) _ (priv (i,j))=fderiv ℝ (V i) (a i) (baseC j) j
    rw [fderiv_comp a (projector (i,j)).differentiableAt hv,(projector (i,j)).fderiv,ContinuousLinearMap.comp_apply,projector_k]; rw [car_d d hv i (he i|>.differentiableAt (by simp))]; simp [priv,V]
lemma adequacy : Focus.Bills (glow G P) (loco d) (totalH (G:=G) (P:=P)):= by
    intro k; filter_upwards [welcome d k,eventually_all.mpr (fun x:Edge P=> (continuous_apply x|>.tendsto (0:City G P)).eventually ((Maurer.wind_div (route d x (priv k))).and ((Maurer.hlog G).eventually (by simp))))] with a ha h
    change index_div _ _ a+ fderiv ℝ totalH a (loco d k a)=0
    rw [ha, e_total (fun i=> (h i).2.differentiableAt (by simp)),← Finset.sum_add_distrib]; exact Finset.sum_eq_zero fun i _=> (h i).1
end YM.MS.Native.Chart
