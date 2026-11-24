import YM.FormalBulk08.Hay.Card

/-! Compare actual array determinant through conditional turns. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Hay
open Filter Set Function MeasureTheory Lattice RG Exterior Wilson Precision Tree Work.F05
open Stationary hiding shine Rays
open Reef Series Wick Jets Orb Plait
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{c f:Side}{S:StepData c f}(F:Forest S.ratio)
variable (u:S.Choices)(p:Clip)(R:PathData G)(A:ChartRatio G)
variable (Y:Bid.Dir G c→AxisChart G F)(H:Critical F p R Y)
lemma on_line (x:Link G c): pending F u p R Y ∘ together x = fun y=>tested F u p R (arm G c 1 x) (stand G F y+ Y (arm G c 1 x)) := by funext a; simp only [pending, Function.comp_apply,bankS, unites, packed, pairs_with]
include H
lemma freezing: Chilly (pending F u p R Y):= by
    let D:= pending F u p R Y; intro i;have hq:Tendsto (arm G c 1) (𝓝 0) (𝓝 0) := by simpa using (arm G c 1).continuous.tendsto 0
    have hx:Tendsto (scalpel (Pine G S F) (wire G c)) (𝓝 0) (𝓝 0):= by simpa using (scalpel (Pine G S F) (wire G c)).continuous.tendsto 0
    filter_upwards [hq.eventually ((H.2.2 u).2),hx.eventually ((pend_lit F u p R Y H).eventually (by simp))] with z hz hu; change pearlD D (.inl i) (together z 0)=_
    rw [tooth _ _ _ (hu.differentiableAt (by simp))];
    let f(x) := stand G F x+ Y (arm G c 1 z); have hp:f 0=Y (arm G c 1 z):= by simp [f]
    have hv: HasFDerivAt (tested F u p R (arm G c 1 z) ∘ f) ((0:AxisChart G F→L[ℝ]ℝ).comp ((stand G F).toContinuousLinearMap)) 0:= by
        exact (show HasFDerivAt _ _ (f 0) from hp.symm ▸ hz).comp _ ((stand G F).toContinuousLinearMap.hasFDerivAt.add_const _)
    rw [show D ∘ together z=tested F u p R (arm G c 1 z) ∘ f from on_line F u p R Y z,pearlD,hv.fderiv];rfl
-- Hessian wires aff-translated
section affine
variable {U W:Type*}[NormedAddCommGroup U][NormedAddCommGroup W][NormedSpace ℝ U][NormedSpace ℝ W]
omit H
lemma slides (L:U→L[ℝ]W)(c:W)(f:W→ℝ)(h:ContDiffAt ℝ 2 f c)(a b:U): iteratedFDeriv ℝ 2 (f ∘ fun x=>L x +c) 0 ![a,b]= iteratedFDeriv ℝ 2 f c ![L a,L b]:= by
    rw [iteratedFDeriv_two_apply,iteratedFDeriv_two_apply]; let g:=fderiv ℝ f; let q x:= L x+c; have hq:q 0=c:=by simp [q]
    have ht x:HasFDerivAt q L x:=L.hasFDerivAt.add_const _
    have hx : Tendsto q (𝓝 0) (𝓝 c):= by rw [←hq]; exact (ht 0).continuousAt.tendsto
    let P:(W→L[ℝ]ℝ)→L[ℝ](U→L[ℝ]ℝ):= (ContinuousLinearMap.compL ℝ U W ℝ).flip L -- name
    have he: fderiv ℝ (f ∘ q) =ᶠ[𝓝 0] P ∘ g ∘ q:= by filter_upwards [hx.eventually (h.eventually (by simp))] with v hv; exact ((hv.differentiableAt (by norm_num)).hasFDerivAt.comp v (ht v)).fderiv
    have hD : DifferentiableAt ℝ g (q 0):= by rw [hq]; exact (h.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)
    change fderiv ℝ (fderiv ℝ (f ∘ q)) _ a b= fderiv ℝ g c (L a) (L b);rw [Filter.EventuallyEq.fderiv_eq he,(P.hasFDerivAt.comp 0 (hD.hasFDerivAt.comp _ (ht 0))).fderiv, hq];rfl
lemma popping (i:Key F G): stand G F (dotI (pines F i))=frame F i:= by
   ext j k; change dotI (pines F i) (pines F (j,k))=(WithLp.ofLp (frame F i j)) k -- dotI
   by_cases hp:j=i.1
   · rw [hp]; simp [frame,dotI,Pi.single_apply,Prod.ext_iff] -- basis normalization
   simp [frame,dotI,hp,Prod.ext_iff]
end affine
include H
lemma strict_fee : ∀ᶠ x: Link G c in 𝓝 0, (dimR (gateP (pending F u p R Y)) x).submatrix (pines F) (pines F)= hessian F u p R (arm G c 1 x) (Y (arm G c 1 x)):= by
    let T:= pending F u p R Y
    have he(x: Key F G)(y:Key F G): ∀ᶠ v:Link G c in 𝓝 0, gateP T (pines F x) (pines F y) v=hessian F u p R (arm G c 1 v) (Y (arm G c 1 v)) x y:= by
       let J:=uncurry (tested F u p R); let Q(v: Link G c):=(arm G c 1 v, Y (arm G c 1 v))
       have hq : ContinuousAt Q 0:= ContinuousAt.prodMk (f:=arm G c 1) (x:=0) (arm G c 1).continuous.continuousAt ((show ContinuousAt Y ((arm G c 1) 0) from by rw [map_zero]; exact H.2.1.continuousAt).comp ((arm G c 1).continuous.continuousAt))
       have hh: Q 0=0:= Prod.ext (map_zero _) (by change Y _=_; rw [map_zero,H.1];rfl)
       have ht:= (pend_lit F u p R Y H).eventually (by simp)
       filter_upwards [puppy T (pend_lit F u p R Y H) (pines F x) (pines F y), (show Tendsto (scalpel (Pine G S F) (wire G c)) (𝓝 0) (𝓝 0) from by simpa using (scalpel (Pine G S F) (wire G c)).continuous.tendsto 0).eventually ht, (show Tendsto Q (𝓝 0) (𝓝 0) from hh ▸ hq.tendsto).eventually (((H.2.2 u).1).eventually (by simp))] with v hv hu hT
       rw [hv,milk _ (ContDiffAt.comp _ hu (tog_lit ..))]; have hb : ContDiffAt ℝ ω (tested F u p R (arm G c 1 v)) (Y (arm G c 1 v)):= hold_jet hT
       rw [show T∘ together v= _ from on_line F u p R Y v]; unfold hessian;rw [Matrix.of_apply,←popping F,←popping F]; exact slides (stand G F).toContinuousLinearMap _ _ (hb.of_le le_top) _ _
    filter_upwards [eventually_all.mpr fun i=>eventually_all.mpr (he i)] with v hv;ext1 i j;exact hv i j
lemma strict_thermal : thermalD (pending F u p R Y) (wambu F R A Y) =ᶠ[𝓝 0] -(thermal F u p R Y A ∘ (arm G c 1)):= by
    let J:=scalpel (Pine G S F) (wire G c); let L:= dimR (gateP (pending F u p R Y))
    filter_upwards [strict_fee F u p R Y H,(show Tendsto J (𝓝 0) (𝓝 0) from by simpa using J.continuous.tendsto 0).eventually (ferry_light F p R Y H)] with v hv ht
    change (Real.log (heatS F A Y (J v))-loopS F R Y (J v)) + _ = -(loop .. +(1/2:ℝ)*Real.log _-_)
    let x:=arm G c 1 v; have hy : packX F Y (J v)=Y x:= by rw [packed, show firstL _=0 from rfl,map_zero,zero_add]; rfl
    have hu : loopS F R Y (J v) = loop R (lifting F (represent x) (Y x)):= by rw [loopS,turnSeries,ht,hy];rfl
    rw [hu];change _ + (-(1/2:ℝ)*Real.log (L v).det) = - (loop R (lifting F (represent x) (Y x))+(1/2:ℝ)*Real.log (hessian F u p R x (Y x)).det- Real.log _)

    rw [show (hessian F u p R x (Y x)).det=(L v).det from (congr_arg Matrix.det hv.symm).trans (Matrix.det_submatrix_equiv_self ..)]
    rw [heatS, sap,show stand _ _ _= _ from hy]; unfold toll; ring
end YM.FormalBulk08.Hay
