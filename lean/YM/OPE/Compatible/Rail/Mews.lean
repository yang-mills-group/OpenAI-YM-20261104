import YM.OPE.Compatible.Rail.Grab
/-! # Stations tilt and quota -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Tree Exterior Asymptotics Work.F05 Stationary
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type*} {G:Gauge}{c f:Side}{S:StepData c f} {p q:Clip}{R T:PathData G} {F:Tree.Forest S.ratio}
namespace Virgin
local notation "C" => (Bid.Dir G c)
local notation "P"=>AxisChart G F
variable {N:ChartRatio G}
def Paths (t:S.Choices)(Y:C→P):Prop:=Y 0=0∧ContDiffAt ℝ ω Y 0 ∧ ContDiffAt ℝ ω (uncurry (score F t p R)) 0∧ ∀ᶠ x in 𝓝 0,fderiv ℝ (score F t p R x) (Y x)=0
abbrev cabin (g:C→P)(x:C):P := slog F x (g x)
lemma solvedPath {g:C→P}(h:Critical F p R g)(t:S.Choices) : Paths (p:=p) (R:=R) t (cabin g):=by
    let v:=cabin g; have hx:v 0=0:=by unfold v cabin; rw [h.1,slog_zero]
    have he: ContDiffAt ℝ ω v 0:=by let A(x:C):=(x,g x); have hh:A 0= (0:C×P):=Prod.ext rfl h.1; exact (hh.symm ▸ slogmooth F|>.comp (f:=A) (0:C) (contDiffAt_id.prodMk h.2.1)) -- elaboration
    have hp: Tendsto (fun i =>(i,v i)) (𝓝 0) (𝓝 0):= tendsto_id.prodMk_nhds (hx ▸ he.continuousAt.tendsto); obtain ⟨hy,hh⟩:=h.2.2 t
    refine ⟨hx,he, ?_,?_⟩
    · let D(X:C×P):= (X.1,bog F X.1 X.2); have hv:D 0=(0:C×P):= Prod.ext rfl (bog_zero F); exact ContDiffAt.congr_of_eventuallyEq ((show ContDiffAt ℝ ω (uncurry (tested F t p R)) (D 0) from hv.symm ▸ hy).comp (f:=D) 0 (contDiffAt_fst.prodMk (bogmooth F))) (scoreB F t ..)
    filter_upwards [hp.eventually ((bogmooth F).eventually (by simp)),hh,hp.eventually (eventually_eventually_nhds.mpr (scoreB F t p R)),(crit_home h).eventually (slogRev F)] with x hB hT hr hZ
    have hz : bog F x (v x)=g x := hZ; have hv: score F t p R x=ᶠ[𝓝 (v x)] tested F t p R x ∘ bog F x:= hold_near hr; rw [hv.fderiv_eq, ((show HasFDerivAt _ 0 (bog F x (v x)) from hz.symm ▸ hT).comp _ ((hold_jet hB).differentiableAt (by simp)).hasFDerivAt).fderiv,ContinuousLinearMap.zero_comp] -- hZrw
abbrev harbor (g:C→P) (p:Clip)(R:PathData G)(t:S.Choices)(N:ChartRatio G)(x:C):= Precision.loop R (fieldF F (g x)) + 1/2 * Real.log (damage (countingBasis F G) (score F t p R x) (g x)).det - Real.log (toll F N (g x))
lemma synch {a:P}{x:C}(hq: ∀ᶠ y:P in 𝓝 a, expF F (slog F x y)=exposure F x y)(ht:LocalRatio N)(hg: ContDiffAt ℝ ω (slog F x) a)(h:a∈parcel F N)(hy:slog F x a∈ parcel F N): toll F N a=toll F N (slog F x a)*|(fderiv ℝ (slog F x) a).det|:=by
    let v:=slog F x; let Y:=saver F (v a); let T:=saver F a
    have he: T =ᶠ[𝓝 a] Y ∘ v:=by
        have ht2: expF F (v a)=exposure F x a:= hq.self_of_nhds
        filter_upwards [hq] with b hb; ext i : 1; change plogC G (buck F a b i)=plogC G (expF F (v b) i * (expF F (v a) i)⁻¹)
        change expF F (v b)=_ at hb; rw [hb, ht2,exposure,exposure]; unfold buck; congr 1; group
    rw [treasury F x N ht _ h,treasury F x N ht _ hy]; change |(fderiv ℝ T a).det| = _ ; rw [he.fderiv_eq,fderiv_comp _ ((cologne F _).differentiableAt (by simp)) (hg.differentiableAt (by simp)),← abs_mul]; congr 1; exact LinearMap.det_comp .. 
lemma pureHeat {g:C→P}{b D L Θ:ℝ}(t:S.Choices)(h:Critical F p R g)(ht:LocalRatio N)(hf:FiniteBound F R T p q b N g D L Θ):
    thermal F t p R g N=ᶠ[𝓝 0] harbor (cabin g) p R t N:=by
    let v := cabin g; let x:=(crit_home h); obtain ⟨ha,hv,hQ,he⟩:=solvedPath h t; have hy:Tendsto (fun i=>(i,v i)) (𝓝 0) (𝓝 0) := tendsto_id.prodMk_nhds (ha ▸ hv.continuousAt.tendsto)
    filter_upwards [x.eventually (eventually_eventually_nhds.mpr (expSlog F)), x.eventually (eventually_eventually_nhds.mpr (scoreS F t p R)), x.eventually ((slogmooth F).eventually (by simp)), he,hf.branch t,(h.1 ▸ h.2.1.continuousAt.tendsto : Tendsto g _ (𝓝 0)).eventually (parcel_zero F ht), (ha ▸ hv.continuousAt.tendsto : Tendsto v _ (𝓝 0)).eventually (parcel_zero F ht), hy.eventually (hQ.eventually (by simp))] with i hz hK hi hZ hc hd hX hL
    let A:= slog F i; let V:=score F t p R i; let K:= damage (countingBasis F G) V (v i); let d:=(fderiv ℝ A (g i)).det; let T:=tested F t p R i
    have hp: ContDiffAt ℝ ω A (g i):=hold_jet hi; have he: ∀ᶠ y:P in 𝓝 (g i), expF F (slog F i y)=exposure F i y:=hold_near hz
    have hr : fieldF F (v i)= lifting F (represent i) (g i):= by unfold fieldF v cabin; rw [he.self_of_nhds,drape_exposure]
    have hx:T =ᶠ[𝓝 (g i)] V ∘ A := hold_near hK; have hy : (hessian F t p R i (g i)).det= d^2 * K.det:=by
        rw [show hessian F t p R i (g i)=damage (countingBasis F G) T (g i) from hessian_eq .., damage_congr _ hx,damage_comp _ (countingBasis F G) (show ContDiffAt ℝ ω V (A (g i)) from hold_jet hL) hp hZ]
        simp only [det_mul,det_transpose,billsM, LinearMap.det_toMatrix];change d * K.det * d = d^2*K.det; ring
    rw [hy] at hc; have hh:d ≠ 0 :=by rintro ht; rw [ht] at hc; simp at hc
    have hf:0<K.det:=pos_of_mul_pos_right hc (sq_nonneg d); have hb:toll F N (v i)≠0:= (toll_pos F ht hX).ne'; change _+ _*Real.log _ - Real.log (toll F N _) = Precision.loop _ (fieldF F (v i))+ _*Real.log K.det - Real.log (toll F N (v i)); rw [hr,synch he ht hp hd hX, hy, Real.log_mul (pow_ne_zero _ hh) hf.ne',Real.log_pow,Real.log_mul hb (abs_pos.mpr hh).ne',Real.log_abs]
    push_cast; ring
end Virgin
end YM.OPE.Flume
