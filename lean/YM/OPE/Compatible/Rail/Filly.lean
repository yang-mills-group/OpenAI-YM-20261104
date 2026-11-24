import YM.OPE.Compatible.Rail.Prize
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Ratio
/-! # local loop parsing -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Tree Exterior Asymptotics Work.F05 Stationary
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type} {G:Gauge}{c f:Side}{S: StepData c f}{F:Forest S.ratio}{R T:PathData G}{s U V:ℝ}{p q:Clip}{N:ChartRatio G}
namespace Virgin
local notation "C"=>Bid.Dir G c
local notation "P"=>AxisChart G F
abbrev springF (F:Forest S.ratio)(R:PathData G)(y:AxisChart G F):= Precision.loop R (fieldF F y)
lemma spoolP (F:Forest S.ratio)(x:AxisChart G F): fieldF F x=input G f (pad F x):=by
    ext1 i; rw [input_color]; by_cases h:i∈ F.trunks
    · rw [show fieldF F x i=1 from F.on_tree _ ⟨i,h⟩, show edgeColor (pad F x) i=0 from pad_trunk F _ ⟨_,h⟩];exact G.mat_lieExp_zero.symm
    rw [show edgeColor (pad F x) i=x ⟨i,h⟩ from pad_free F x ⟨_,h⟩]; exact F.off_tree _ ⟨i,h⟩
lemma sophok (F:Forest S.ratio)(h:R.Bounds p s U V): ContDiffAt ℝ ω (springF F R) 0∧ fderiv ℝ (springF F R) 0=0:=by
    let A:=pad F (G:=G); let Y:=turnSeries R.loop (m:=f); have he:= turns_analytic _ h.width h.two (m:=f); have ht: ContDiffAt ℝ ω Y (A 0):=by rw [map_zero];exact he.contDiffAt
    rw [show springF F R=Y∘A from funext fun i=> by unfold springF; rw [spoolP]; rfl]; refine ⟨ht.comp _ A.contDiff.contDiffAt,?_⟩
    rw [fderiv_comp 0 (ht.differentiableAt (by simp)) A.differentiableAt,map_zero]; have hp:fderiv ℝ Y 0=0:=by
        have h:= (rays_jet he _).1 (turns_low _ h.width h.two) 1 (by decide); apply ContinuousLinearMap.ext; intro i; simpa [iteratedFDeriv_one_apply] using DFunLike.congr_fun h ![i]
    rw [hp, ContinuousLinearMap.zero_comp]
abbrev rake (N:ChartRatio G):G.Color→ℝ:=Real.log ∘ N.J
lemma jet_trunk (h:LocalRatio N): ContDiffAt ℝ ω (rake N) 0∧ fderiv ℝ (rake N) 0=0:=by
    have hs: ContDiffAt ℝ ω (rake N) 0:=(h.germ _ (Metric.mem_ball_self h.patch)).log (by rw [h.anchored]; exact one_ne_zero); refine ⟨hs,?_⟩; apply ContinuousLinearMap.ext; intro x
    have hf:=hs.differentiableAt (by simp); have he:= Push.side (rake N) hf x; exact he.unique (Next.SectorChange.still_even hf (Eventually.mono (p:=fun y=> y∈ Metric.ball 0 N.radius) (Metric.ball_mem_nhds 0 h.patch) (fun i hi=> congr_arg Real.log (Next.SectorChange.ratio_even h hi).symm)) x)
abbrev taxY (F:Forest S.ratio)(N:ChartRatio G)(p:AxisChart G F):= ∑ i:F.Free, rake N (p i)
lemma taxes (F:Forest S.ratio)(h:LocalRatio N): (Real.log ∘ toll F N) =ᶠ[𝓝 0] taxY F N:=by
     filter_upwards [parcel_zero F h] with x hx; change Real.log (∏ i:F.Free, N.J _) = _; exact Real.log_prod (fun i _=> (h.pos (x i) (hx i (Set.mem_univ _))).ne')
lemma accountV (F:Forest S.ratio)(h:LocalRatio N): ContDiffAt ℝ ω (taxY F N) 0 ∧ fderiv ℝ (taxY F N) 0=0 :=by
    let u(i:F.Free):AxisChart G F →L[ℝ] G.Color:=ContinuousLinearMap.proj (R:=ℝ) i
    obtain ⟨hx,hk⟩:=jet_trunk h; let A(i:F.Free):=rake N ∘ u i; have hv(i:F.Free): ContDiffAt ℝ ω (A i) 0:=(show ContDiffAt ℝ ω (rake N) (u i 0) from by rw [map_zero]; exact hx).comp 0 (u i).contDiff.contDiffAt; refine ⟨ContDiffAt.sum (fun i _=> hv i),?_⟩
    rw [show taxY F N=(fun y=> ∑ i:F.Free,A i y) from rfl,fderiv_fun_sum (fun i _=>(hv i).differentiableAt (by simp))]; exact Finset.sum_eq_zero (fun i _=> by rw [show fderiv ℝ (fun x=> A i x) 0=_ from fderiv_comp _ (show DifferentiableAt ℝ (rake N) (u i 0) from hx.differentiableAt (by simp)) (u i).differentiableAt,map_zero,hk,ContinuousLinearMap.zero_comp]) -- proj
lemma bills (F:Forest S.ratio)(h: LocalRatio N)(u v:AxisChart G F): iteratedFDeriv ℝ 2 (taxY F N) 0 ![u,v]=∑ i:F.Free,iteratedFDeriv ℝ 2 (rake N) 0 ![u i,v i]:=by
    obtain ⟨hx,hk⟩:=jet_trunk h; let X(i:F.Free):AxisChart G F→L[ℝ] G.Color:=ContinuousLinearMap.proj i; let S(i):= rake N ∘ X i; have hv(i):ContDiffAt ℝ ω (S i) 0:=(show ContDiffAt ℝ ω (rake N) (X i 0) from by rw [map_zero]; exact hx).comp 0 (X i).contDiff.contDiffAt
    rw [show taxY F N=∑ i,S i from funext fun x=> by simp only [Finset.sum_apply,taxY]; rfl, iteratedFDeriv_sum_apply (fun i _=> (hv i).of_le le_top),_root_.sum_apply]; refine Finset.sum_congr rfl (fun i _=>?_); rw [show iteratedFDeriv ℝ 2 (S i) 0 ![u,v]=_ from pay_second (F:=rake N) (H:=X i) hx (X i).contDiff.contDiffAt u v,map_zero,hk, (X i).fderiv,_root_.zero_apply,zero_add]; rfl
end Virgin
end YM.OPE.Flume
