import YM.SignedWilsonExpansion.F9.EulerTop
import YM.FVA2.Press.Subtraction
/-!
# Same *position-prediction* stencils in offshell point variables

Not equating the massless/ms frame with the original one. Use Survey on the
comparator prescription. Its whole Wick inverse allows a pure rank decomposition
with strictly lower rank judiciously subtracted. Top points are kept in lattice
(no a or θ) and raw physical Wilson units, and in the EXACT orientations of
point frames. The (one) regulator argument will use these same pillars.
-/
set_option autoImplicit false
set_option maxHeartbeats 760000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa.Pill
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Matrix
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos PathCost FVA2
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical ENNReal
variable {G:Gauge}{H:Hol G}{h i j k m r d n l:ℕ}{F:Frame G h}{x: Label G h}{A:XSpace.Survey G H h}
abbrev title (A:XSpace.Survey G H h)(x:Label G h): CoverConfig G→ℂ:= evaluateLabel x ∘ A.reading
section glimpses
variable (A:XSpace.Survey G H h)
lemma surveying : Maskable A.reading:= Maskable.applies Maskable.read_samples A.recover A.recover_smooth
lemma shaded (x:Label G h): Maskable (title A x):= (surveying A).applies _ (Work.G05.snap_read_smooth h x.val ω)
lemma sphere (x:Label G h): GaugeInvariant (title A x):= by
    intro g U; unfold title evaluateLabel; simp only [Function.comp_apply]; rw [A.reading_gauge,WardBin.expand_color]; exact x.property.2 ..
lemma sight₀ : A.reading 1=0:= by
    have he: Bid.mapped (G:=G) A.looks 1=0:=by
       funext i; set k:=A.looks i; change k.eval (G:=G) 1=0; unfold RG.Slot.eval; rw [show faceValue (1:CoverConfig G) (k.offset,k.plaq)=1 from Pressure.one ..,G.curvature_unit,map_zero]
    unfold XSpace.Survey.reading; rw [Function.comp_apply,he,A.recover_zero]
lemma mask_roof_smooth {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E] {v:CoverConfig G→ E} (p:Maskable v)(V: Fabrication G): ContDiff ℝ ω (v ∘ roof V):= by
    obtain ⟨S,F,h,he⟩:= p; rw [funext he]; refine h.comp (f:= (fun x=> body x S) ∘ roof V) (contDiff_pi.mpr fun i=> ?_); exact G.exp_jet.comp (contDiff_id.smul contDiff_const)
lemma glance (p:x∈Grade (n,r))(t:ℝ)(X:Snap G h): evaluateLabel x (t • X)= t^r • evaluateLabel x X:=by
    unfold evaluateLabel; rw [expand_smul,multiplied_grade t _ _ p]
lemma yearly (p:x∈Grade (n,r)): rayCap r (Complex.reCLM ∘ title A x) := by
    intro V; let f(t:ℝ):= A.reading (roof V t); let X:=deriv f 0; have heQ: ContDiff ℝ ω f:=mask_roof_smooth (surveying A) V; have hh:Tendsto (fun t:ℝ=> t⁻¹ • f t) (𝓝[>] 0) (𝓝 X):= value_scale ((heQ.differentiable (by simp)) 0|>.hasDerivAt) (show f 0=0 by unfold f; rw [show roof V 0=1 from funext fun i=> by simp [roof],sight₀]); let g(v:Snap G h):= Complex.re (evaluateLabel x v); have hg: Continuous g:= Complex.continuous_re.comp (Work.G05.snap_read_smooth h x.val ω|>.continuous) -- h shadow
    let C:=‖g X‖+1; refine ⟨C,by unfold C; positivity,?_⟩; filter_upwards [((hg.tendsto X).comp hh).norm.eventually (ge_mem_nhds (show ‖g X‖<C by unfold C; linarith)),self_mem_nhdsWithin (s:=Set.Ioi (0:ℝ))] with t he hv
    change ‖g (t⁻¹ • f t)‖≤ C at he; unfold g at he; rw [glance p,Complex.smul_re,norm_smul,inv_pow,Real.norm_of_nonneg (by have : 0<t:=hv; positivity),inv_mul_eq_div] at he; exact (div_le_iff₀ (pow_pos (show 0<t from hv) _)).mp he
noncomputable def curlP (x:Label G h)(p:x∈Grade (n,r)): Pill G:=⟨Complex.reCLM ∘ title A x,(shaded A x).applies _ Complex.reCLM.contDiff,fun g U=> congr_arg Complex.reCLM (sphere A x g U),r,yearly A p⟩
lemma through (x:Label G h)(p:x∈Grade (n,r))(X: Snap G h):
    Tensor.diagonal (Tensor.coeff (title A x ∘ curve (d:=h) H) r 0) X=evaluateLabel x X:=by
    let P: Snap G h → GaugePanel G A.size:= bring H h A.looks; let F(v:Snap G h):= A.reading (curve H v)
    have he:F= A.recover ∘ P:=rfl; have hv:P 0=0:=funext fun i=> takes_zero ..; have hc: AnalyticAt ℝ P 0:= AnalyticAt.pi fun i=> (XSpace.peg H h).shot _
    have hh : fderiv ℝ P 0 X=A.glowing X:=by
       funext i; have hp: Blurb H h (A.looks i)= _ := fderiv_apply hc.differentiableAt i; rw [XSpace.Survey.glowing,← (XSpace.peg ..).initial,hp]; rfl
    have hf: fderiv ℝ F 0 X=X:=by
       rw [he,fderiv_comp _ (A.recover_smooth.differentiable (by simp) _) hc.differentiableAt,hv,ContinuousLinearMap.comp_apply,hh]; exact A.linear_jet X
    have hm: ContDiffAt ℝ ω F 0:= A.recover_smooth.contDiffAt.comp _ hc.contDiffAt
    let V:= (Work.G05.snap_read_smooth h x.val ω); let y:ℝ→L[ℝ] Snap G h:= (ContinuousLinearMap.id ℝ ℝ).smulRight X
    let g(v:Snap G h):= evaluateLabel x (F v); have ht: ContDiffAt ℝ (r:WithTop ℕ∞) g 0:= (V.contDiffAt.comp _ hm).of_le le_top
    change Tensor.diagonal (Tensor.coeff g r 0) X= _; rw [← leading_tensor X _ ht]; apply leading_of_lim (f:= g∘y) ((show ContDiffAt ℝ r g (y 0) from by rw [map_zero]; exact ht).comp _ y.contDiff.contDiffAt)
    let f(t:ℝ):= F (y t); have hy: Tendsto (fun t:ℝ=> t⁻¹ • f t) (𝓝[>]0) (𝓝 X):= by
       have hv': HasDerivAt f (fderiv ℝ F 0 X) 0:= (hm.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 (show HasDerivAt y X 0 from by apply y.hasFDerivAt.hasDerivAt.congr_deriv; change (1:ℝ) • X = X; exact one_smul ℝ X) (map_zero y).symm
       rw [hf] at hv'; exact value_scale hv' (show f 0=0 by unfold f; rw [map_zero,he,Function.comp_apply,hv,A.recover_zero])
    apply ((V.continuous.tendsto X).comp hy).congr'; refine Eventually.of_forall fun t=>?_ ; change evaluateLabel x (t⁻¹ • _)= _; rw [glance p,inv_pow]; rfl

lemma primary_curl (x:Label G h)(p:x∈Grade (n,r))(u:realBar x=x)(i:TagIx F r): row F ((curlP A _ p).letter.2 0 r) i= if wT F i=n then ((F.coords x) i).re else 0 := by
    let P:=curlP A x p; let W:= wT F i; let T:Label G h:=⟨seedTile (vitre h (P.letter.2 0 r)) W,fundedSeed H P.solid (F.bound i.val)⟩; have he:=seed_row H P.solid (e:=0) i
    have hc : ContDiffAt ℝ r (title A x∘curve (d:=h) H) 0:=by
       refine ((Work.G05.snap_read_smooth h x.val ω|>.contDiffAt).comp (g:=evaluateLabel x) _ (A.recover_smooth.contDiffAt.comp _ ?_)).of_le le_top -- maybe wrong if change
       exact (show AnalyticAt ℝ (bring H h A.looks) 0 from AnalyticAt.pi fun i=> (XSpace.peg H h).shot _).contDiffAt
    have hφ:T=(if W=n then x else 0):=by
       apply Subtype.ext; apply Labels.eval_ext; intro J; change Labels.read J (seedTile (vitre h (P.letter.2 0 P.rank)) W)= _; rw [P.principal_tile H J]
       let V:=title A x∘curve (d:=h) H; let D(x:ℝ):=engineered x (trunk h J)
       change Complex.ofReal (WardBin.leading W (fun t:ℝ=> Tensor.diagonal (Tensor.coeff (Complex.reCLM ∘ V) r 0) (D t)))=_; simp_rw [real_ten V _ r hc]; unfold V D; simp_rw [through A x p _,eval_eng _ _ _ p,Complex.smul_re,racts,lead_monomial]; split_ifs with h; exact (real_eval _ u J).symm; rw [Complex.ofReal_zero]; exact (map_zero _).symm
    change row F (P.letter.2 0 r) i= _; rw [he]; change ((F.coords T) i).re= if W=n then _ else _; rw [hφ]; split_ifs; rfl; rw [map_zero]; rfl
end glimpses
end YM.WilsonCoeffUV.Mer.Xa.Pill
