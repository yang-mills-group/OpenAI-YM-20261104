import YM.MSbar.Symbol.Fiber

/-! Commutation of ε holomorphy and symbol jets. Compact complex averages, witnesses for products etc. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Symbol
open Function Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff BigOperators Classical
variable {E X Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {f g : ℂ×X→ℂ} {s : ℂ×X} {U : Set ℂ}
namespace AH
-- CR sufficient by real calculus
lemma from_partials (hf : Belongs U f) (hc : ∀ q:ℂ×X,q.1∈U →
    (fderiv ℝ f q) (I,0)= I*(fderiv ℝ f q) (1,0)) : AH U f := by
    refine ⟨hf,fun z x hz=> ?_⟩
    apply differentiableAt_complex_iff_differentiableAt_real.mpr
    let p : ℂ×X:= (z,x); obtain ⟨F,hF,h⟩:=hf _ hz; have he : ContDiffAt ℝ ∞ f p :=
        hF.1.contDiffAt.congr_of_eventuallyEq ((continuousAt_fst (p:=p)|>.tendsto.eventually h).mono fun b hb=>congr_fun hb b.2)
    have hD : HasFDerivAt (fun v => f (v,x)) (partialL f p) z:= (he.differentiableAt (by simp)).hasFDerivAt.comp (f:=fun y=>(y,x)) _ ((hasFDerivAt_id z).prodMk (hasFDerivAt_const x z))
    refine ⟨hD.differentiableAt,?_⟩; rw [hD.fderiv]; exact hc p hz

def diff (p : ℂ × X) (f : ℂ×X→ℂ) (x : ℂ×X) := fderiv ℝ f x p
lemma diff_smooth (hf : AH U f) (hu : IsOpen U) (a : ℂ × X) : AH U (diff a f):=by
    have h : Belongs U (diff a f):=by
        intro z hz; obtain ⟨F,hF,h⟩:=hf.uses z hz
        refine ⟨diff a F,(ContinuousLinearMap.apply ℝ ℂ a).hasTemperateGrowth.comp (tame_fderiv hF),?_⟩
        filter_upwards [eventually_eventually_nhds.mpr h] with w hw
        funext v; refine DFunLike.congr_fun (Filter.EventuallyEq.fderiv_eq (𝕜:=ℝ) ?_) a
        exact ((continuousAt_fst (p:=(w,v))).tendsto.eventually hw).mono fun b hb=> congr_fun hb b.2
    apply from_partials h; intro q hq
    have he:= hf.smooth _ hq; let y(v : ℂ):ℂ×X:= (v,0)
    let R:=((ContinuousLinearMap.mul ℝ ℂ) I)
    have hx : diff (y I) f =ᶠ[𝓝 q] fun x=> R (diff (y 1) f x):=by
        filter_upwards [(hu.preimage continuous_fst).mem_nhds (show q∈Prod.fst ⁻¹' U from hq)] with q hq
        exact hf.cr_rule hq q.2 I
    have hs:= he.isSymmSndFDerivAt (𝕜:=ℝ) (by simp; exact WithTop.coe_le_coe.mpr le_top); have hE := he.fderiv_right (by simp : (∞:WithTop ℕ∞)+1 ≤ ∞)
    have hd (v:ℂ×X) : HasFDerivAt (diff v f) ((ContinuousLinearMap.apply ℝ ℂ v).comp (fderiv ℝ (fderiv ℝ f) q)) q:=
        (ContinuousLinearMap.apply ℝ ℂ v).hasFDerivAt.comp q (hE.differentiableAt (by simp)).hasFDerivAt
    have hw := (R.hasFDerivAt.comp q (hd (y 1))).congr_of_eventuallyEq hx
    have H(r s:ℂ×X) : fderiv ℝ (diff r f) q s=fderiv ℝ (fderiv ℝ f) q r s:=by
        rw [(hd r).fderiv]; exact hs s r
    change fderiv ℝ (diff a f) q (y I)= I*fderiv ℝ (diff a f) q (y 1)
    rw [H,H,hs a (y I),hs a (y 1),← H (y I),← H (y 1),hw.fderiv,(hd _).fderiv] -- argument order
    rfl

-- partial smoothness geometric H to average variable with measure
section
variable [FiniteDimensional ℝ X] {α : Type*} [MeasurableSpace α] {μ : Measure α} {K : Set Y} {p : α → Y}
variable {w : α → ℂ} (hw : Integrable w μ) (hp : AEStronglyMeasurable p μ) (he : ∀ᵐ a ∂μ,p a∈K) (hc : IsCompact K)
variable {F : ℂ × (X × Y)→ℂ}
include hw hp he hc
-- only need holomorphy on params actually used
lemma average (hF : Belongs U F) (hH : ∀ z∈U,∀ x,∀ᵐ a ∂μ, fderiv ℝ F (z,x,p a) (I,0)= I*fderiv ℝ F (z,x,p a) (1,0)) : AH U (fun q:ℂ×X=> ∫ a,w a*F (q.1,q.2,p a) ∂μ) := by
    let b:=ContinuousLinearMap.mul ℝ ℂ
    let L:=ContinuousLinearEquiv.prodAssoc ℝ ℂ X Y
    let f(F : ℂ × (X × Y)→ℂ):=fun q:ℂ×X=> ∫ a,w a*F (q.1,q.2,p a) ∂μ
    have hh(z:ℂ) (hz:z∈U): ∃ g : ℂ×(X×Y)→ℂ,g.HasTemperateGrowth∧ curry F =ᶠ[𝓝 z] curry g ∧ curry (f F) =ᶠ[𝓝 z] curry (f g):=by
        obtain ⟨g,hg,H⟩:=hF z hz
        exact ⟨g,hg,H,H.mono fun t ht=>funext fun x=>integral_congr_ae (Eventually.of_forall fun a=> congr_arg (w a * ·) (congr_fun ht (x,p a)))⟩
    refine from_partials (f:=f F) (fun z hz=>?_) (fun q hq=>?_)
    · obtain ⟨g,hg,h,H⟩:=hh _ hz; exact ⟨_, average_growth b hp he hc hw (hg.comp L.hasTemperateGrowth),H⟩
    obtain ⟨g,hg,h,H⟩:= hh _ hq; have hk:= hg.comp L.hasTemperateGrowth;let D:= partialL (g ∘ L)
    have hQ : f F =ᶠ[𝓝 q] f g:= by exact (continuousAt_fst.tendsto.eventually H).mono fun v hv=> congr_fun hv v.2
    have hb (p:ℂ× X × Y) (h':p.1=q.1) : ∀ c:ℂ×X×Y, fderiv ℝ g p c=fderiv ℝ F p c:=by
        intro c; apply DFunLike.congr_fun
        apply Filter.EventuallyEq.fderiv_eq
        exact (((continuousAt_fst (p:=p)).tendsto.eventually (h' ▸ h)).mono fun y hy=> (congr_fun hy y.2).symm)
    have hp'(x:ℂ) (y : Y) : D (q,y) (x,0)=fderiv ℝ F (q.1,q.2,y) (x,0):= by
        unfold D partialL; rw [fderiv_comp _ (hg.1.differentiable (by simp) _) L.differentiableAt]; simp only [ContinuousLinearEquiv.fderiv]; exact hb (q.1,q.2,y) rfl _
    have hD : fderiv ℝ (f F) q= ∫ a,(b (w a)).comp (D (q,p a)) ∂μ:= hQ.fderiv_eq.trans (average_hasFDeriv b hp he hc hw hk.1 q).fderiv
    have hv : Integrable (fun a=>(b (w a)).comp (D (q,p a))) μ:= average_integrable (b.precompR (ℂ×X)) hp he hc hw (partialL_smooth hk.1).continuous q
    rw [hD,ContinuousLinearMap.integral_apply hv,ContinuousLinearMap.integral_apply hv,← integral_const_mul]; refine integral_congr_ae ?_
    filter_upwards [hH q.1 hq q.2] with a ha
    change w a*D _ _=I*(w a*D _ _); rw [hp',hp',ha,mul_left_comm]
lemma after_average (hF: AH U F): AH U (fun q:ℂ×X=> ∫ a,w a*F (q.1,q.2,p a) ∂μ) := average hw hp he hc hF.uses (fun _ hz x=> Eventually.of_forall (fun a=> hF.cr_rule hz (x,p a) I))
end
end AH
end YM.MSbar.Symbol
