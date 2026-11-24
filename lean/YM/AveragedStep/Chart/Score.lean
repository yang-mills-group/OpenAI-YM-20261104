import YM.AveragedStep.Chart.Measures
/-! # Single free-edge conditional score equation

Still with the actual compact Haar integral, acting in one held gauge
coordinate. No chart boundary term, and the *actual* exponential chart
Jacobian contributes through all local orders. Require the density only be
specified on the smaller collar of support! Consumer must guard every
other touched bond for this lemma. -/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep.Cuff
open RG Lattice Filter Function Precision Set Metric MeasureTheory
open scoped Topology Matrix.Norms.Frobenius ENNReal BigOperators Classical ContDiff
variable {G:Gauge}{P:Patch}{K:KernelChoices}{A:ChartRatio G}(Q:Cuff P K A)(H:LocalRatio A)
local notation "X" => G.Color
local notation "gate" => (Q.trigger : X→ℝ)
def haarScore (u v:G.Color):ℝ:= (fderiv ℝ A.J u v)/A.J u

include H
/- apply to an entire error/test (including readout factors outside the chart),
not to normalized conditionals differentiated despite an unpriced denominator.
-/
lemma balance {M E: X → ℝ} {d:G.El→ℝ} {k:ℝ} (v:X)(B:ℝ)
    (_hd:Measurable d)
    (hv: ∀ x ∈ tsupport gate, d (G.lieExp x)=k*Real.exp (-B*E x))
    (he: ∀ x∈tsupport gate, ContDiffAt ℝ 1 E x)
    (hm: ContDiff ℝ 1 M):
    let logD (x:X) := haarScore (A:=A) x v-B*(fderiv ℝ E x) v
    let F(x:G.El) :=
      d x * (Q.incline v x * M (Q.logC x) + Q.ticket x*((fderiv ℝ M (Q.logC x)) v + M (Q.logC x)*logD (Q.logC x)))
    -- need host measurability separately? fderiv measurable Borel; no on beyond gate needed
    (Measurable F → ∫ x,F x ∂G.probHaar=0):=by
 intro L V hV
 let W(x:X):=k*Real.exp (-B*E x)*A.J x
 let f(x:X):=gate x*M x*W x
 let D(x:X):= fderiv ℝ f x v
 have hz (x:X)(hx:x∉tsupport gate): gate =ᶠ[𝓝 x] 0:= by
   filter_upwards [(isClosed_closure (s:=support gate)).isOpen_compl.mem_nhds hx] with y hy
   apply notMem_support.mp (fun h=>hy (show y∈closure (support gate) from subset_closure h))
 have hh(x:X)(hx:x∉tsupport gate): f=ᶠ[𝓝 x] 0 := by filter_upwards [hz x hx] with y hy; unfold f; rw [hy]; simp
 have hwin{x:X}(hx:x∈tsupport gate): x∈ Metric.ball 0 A.radius:= by
   have he:= Q.trigger.tsupport_eq ▸ hx; apply Q.withinH
   exact closedBall_subset_closedBall (show Q.trigger.rOut ≤ 2*Q.width by unfold trigger; dsimp only; linarith [Q.active]) (show x∈closedBall 0 Q.trigger.rOut from he)
 have hf:ContDiff ℝ 1 f := contDiff_iff_contDiffAt.mpr (fun x=>by
   by_cases h:x∈ tsupport gate
   · exact (Q.trigger.contDiffAt.mul hm.contDiffAt).mul
       ((contDiffAt_const.mul ((Real.contDiff_exp.contDiffAt).comp (f:=fun x=> (-B)*E x) x
         (contDiffAt_const.mul (he x h)))).mul ((H.germ x (hwin h)).of_le le_top))
   exact contDiffAt_const.congr_of_eventuallyEq (hh x h))
 have hd' : Continuous D:= (hf.continuous_fderiv (by simp)).clm_apply continuous_const
 have hu: support f ⊆ support gate:= by intro x hx; apply not_not.mp; intro he; exact hx (by unfold f; have he:gate x=0:= notMem_support.mp he; rw [he]; ring) -- double neg simp
 have hcomp:IsCompact (tsupport f):= IsCompact.of_isClosed_subset Q.trigger.hasCompactSupport isClosed_closure (closure_mono hu)
 have hQ: support D ⊆ tsupport f := by
   intro x ht; by_contra ha; apply ht; unfold D; rw [fderiv_of_notMem_tsupport (𝕜:=ℝ) ha]; rfl
 have hDcomp : HasCompactSupport D := hcomp.of_isClosed_subset isClosed_closure (closure_minimal hQ isClosed_closure)
 have hInt: (∫ x:X,D x)=0:=by
   have hW: Integrable f volume:= hf.continuous.integrable_of_hasCompactSupport hcomp
   have h': Integrable D volume:=hd'.integrable_of_hasCompactSupport hDcomp
   have hb:=integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v:=v) (μ:=volume) (f:=fun _:X=>(1:ℝ)) (g:=f) (by simp) (by simpa using h') (by simpa using hW) (fun _ _=> differentiableAt_const 1) (fun _ _=> hf.differentiable (by simp) _)
   simpa using hb
 have hex(x:X)(hx:x∈ tsupport gate):
    D x = A.J x * V (G.lieExp x):=by
    -- calculate carefully with positive chart factor
    have H₁:DifferentiableAt ℝ gate x:=(Q.trigger.contDiffAt (n:=1)).differentiableAt (by simp)
    have h2:= hm.differentiable (by simp) x
    have h3: DifferentiableAt ℝ A.J x:=(H.germ x (hwin hx)).differentiableAt (by simp)
    let g:=fun x=> (-B)*E x
    have hg:HasFDerivAt (fun x=>Real.exp (g x)) ((Real.exp (g x)) • ((-B) • (fderiv ℝ E x))) x:=
       (Real.hasDerivAt_exp (g x)).comp_hasFDerivAt x (((he x hx).differentiableAt (by simp)).hasFDerivAt.const_mul (-B))
    have hd:= ((H₁.hasFDerivAt.mul h2.hasFDerivAt).mul ((hg.const_mul k).mul h3.hasFDerivAt)).fderiv
    change fderiv ℝ f x=_ at hd; unfold D; rw [hd]
    have hj : x∈Q.horizon := by rw [Q.trigger.tsupport_eq] at hx; exact closedBall_subset_closedBall (show Q.trigger.rOut≤2*Q.width by unfold trigger; dsimp only; linarith [Q.active]) hx
    obtain ⟨hT,hI⟩:=Q.tickets hj v
    unfold V; rw [hv x hx,hT,hI,Q.wind_id (show ‖x‖ ≤ 2*Q.width by simpa [horizon] using hj)]
    have hs : A.J x≠0:=(H.pos _ (hwin hx)).ne'
    simp only [add_apply,smul_apply,Pi.mul_apply,smul_eq_mul,L, g,haarScore]
    field_simp; ring -- maybe derivative w.r.t x log factors need J
 rw [Q.reduction H hV (f:=V) (by intro x he; unfold V ticket incline; simp only [if_neg he]; ring),
    setIntegral_congr_fun (s:=Q.horizon) (f:=fun x=> V (G.lieExp x)*A.J x) measurableSet_closedBall (g:=D)]
 · rw [setIntegral_eq_integral_of_forall_compl_eq_zero (by
      intro x hx; apply notMem_support.mp; intro H'; apply hx
      have Hf:= (hQ.trans (closure_mono hu)) H'; change x∈tsupport gate at Hf; rw [Q.trigger.tsupport_eq] at Hf; exact closedBall_subset_closedBall (show Q.trigger.rOut≤2*Q.width by unfold trigger; dsimp only; linarith [Q.active]) Hf),hInt,mul_zero]
 intro x hx
 by_cases ha:x∈tsupport gate; · rw [hex x ha,mul_comm]
 unfold V; dsimp only
 have hg : gate x=0:=(hz x ha).eq_of_nhds
 have ht:fderiv ℝ (gate) x=0:=fderiv_of_notMem_tsupport (𝕜:=ℝ) ha
 rw [(Q.tickets hx v).1,(Q.tickets hx v).2,ht,zero_apply,hg, zero_mul,zero_mul,add_zero,mul_zero,zero_mul]
 unfold D; rw [(hh x ha).fderiv_eq]; simp
end YM.AveragedStep.Cuff
