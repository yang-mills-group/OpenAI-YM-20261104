import YM.SchemeRG11.Saddle.Matter
import YM.SchemeRG11.Saddle.Node
/-!
# Full inner PS versus Landau on the inversion torus. Exact coefficient conjugacies (no rates).

Landau path concretely specified: `chosen` Haar in `Land G n` from additive vectors, positive
K from Jacob and projected Mean FP in SAME role as Wilson, weight without quadratic, `expect`
measure via whole stationary Gaussian over Land with `wilson` Hessian only.
No offshell mST here. Doesn't assert anything on the continuum limit. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.SchemeRG11.Sway
open Lam
open scoped Classical ContDiff Topology Matrix.Norms.Frobenius PowerSeries NNReal ENNReal
open Function Filter Lattice Pert.Orb PertExtension.Orb LocalH MeasureTheory Precision Push.Loops
open PertExtension.Series Local Radial Tested PertExtension.Chart Next.SectorChange.Gaussian
variable {G:Gauge}{n:Side}
abbrev blue (G:Gauge)(n:Side): Coords G n≃L[ℝ] Potential G n:= (expand G n).toContinuousLinearEquiv
def baseV(G:Gauge)(n:Side):Measure (Potential G n):=(volume:Measure (Coords G n)).map (blue G n)
instance base_haar:Measure.IsAddHaarMeasure (baseV G n):= (blue G n).isAddHaarMeasure_map _
def Film (G:Gauge)(n:Side):= fibers (Pert.Orb.action G n) priceAll
lemma expand_color: weight G n= Film G n ∘ blue G n:=by
 have hk : actionR G n= Lam.baseR (Pert.Orb.action G n) ∘ blue G n:=by
    ext1 x; ext k; simp only [actionR, PowerSeries.coeff_mk, Function.comp_apply,Lam.baseR,cscale]; split_ifs with hi
    · subst hi; simp [Radial.layers]
    simp only [Radial.layers,if_neg hi,add_zero]; rfl
 have hu: unmarked G n= fitR priceAll ∘ blue G n:=by ext1 x; ext k; rw [unmarked,comp_apply,PowerSeries.coeff_mk,fitR,cscale,PowerSeries.coeff_mk];rfl
 funext x; rw [weight,hk,hu];rfl
local notation "coef"=>PowerSeries.coeff (R:=ℂ)
def Fentry (X:JetArray (Potential G n)):= normalize (X∘blue G n)
lemma temp_fan{P:JetArray (Potential G n)}(h:Ready P):Ready (P ∘ blue G n):=by
 intro k; let f:=blue G n
 obtain ⟨hc,C,hC,N,H⟩:= h k
 let D := ‖f.toContinuousLinearMap‖+1
 have he:1≤D:=by exact (by unfold D; linarith [show 0≤‖f.toContinuousLinearMap‖ from by exact norm_nonneg (E:=Coords G n →L[ℝ] Potential G n) f.toContinuousLinearMap])
 refine ⟨hc.comp f.continuous,C*D^N,by positivity,N,fun x=>?_⟩
 apply (H (f x)).trans
 rw [mul_assoc,← mul_pow]; gcongr; calc
    _ ≤ 1 + D * ‖x‖ := add_le_add (le_refl _) ((show ‖f x‖≤‖f.toContinuousLinearMap‖ *‖x‖ from f.toContinuousLinearMap.le_opNorm x).trans (mul_le_mul_of_nonneg_right (by unfold D; linarith) (norm_nonneg _)))
    _ ≤ _:=by rw [mul_add,mul_one]; linarith
lemma shine{P:JetArray (Potential G n)}(h:Ready P): expect (P ∘ blue G n)=PowerSeries.C ((↑(coat (covarianceM G n)):ℂ)⁻¹) * heart (baseV G n) (Pert.Orb.action G n) P:=by
 let f:= blue G n
 let S:= Pert.Orb.action G n; let c:= coat (covarianceM G n)
 have hc: 0<c:= coat_pos (covarianceM_pos ..)
 have hz: data G n= volume.withDensity (fun x:Coords G n=> ENNReal.ofReal (c⁻¹*Radial.kernel S (f x))):=by
    rw [densityFormula]; congr 2; funext x; rw [Radial.kernel,VF_heavy, neg_div]; rfl
 have hm:Measurable (fun x:Coords G n=> (c⁻¹ * Radial.kernel S (f x))) := measurable_const.mul ((Real.continuous_exp.comp (Smooth.continuousJet S 2).neg).measurable.comp f.continuous.measurable)
 ext k; rw [expect,heart, PowerSeries.coeff_C_mul,PowerSeries.coeff_mk,PowerSeries.coeff_mk, hz,integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal (Eventually.of_forall fun _=> ENNReal.ofReal_lt_top),baseV,integral_map f.continuous.measurable.aemeasurable (cost_pay (baseV G n) VF_weight h k).aestronglyMeasurable, ← integral_const_mul]
 apply integral_congr_ae; filter_upwards with x; rw [ENNReal.toReal_ofReal (show 0≤c⁻¹*Radial.kernel S (f x) from mul_nonneg (inv_pos.mpr hc).le kernel_pos.le)]
 change (c⁻¹*Radial.kernel S (f x)) • coef k (P (f x))= (↑c:ℂ)⁻¹ * (↑(Radial.kernel S (f x))*_); simp [Complex.real_smul,mul_assoc]
lemma aged{P:JetArray (Potential G n)}(h:Ready P): Fentry P= choir (baseV G n) (Pert.Orb.action G n) priceAll P:=by
 unfold Fentry Pert.Orb.normalize vacuum; rw [expand_color,show (Film G n ∘ blue G n)*(P ∘ blue G n)=(Film G n * P) ∘ blue G n from rfl]; have H:Ready (Film G n):=factor_ready (Pert.Orb.action G n) priceAll
 rw [shine (H.mul h), shine H,taxa]
 · rfl
 · exact bowl_pos (baseV G n) VF_weight (K:=priceAll) (by simp only [priceAll,jacobian_flat, FP_flat,mul_one];exact one_pos)
 exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (coat_pos (covarianceM_pos G n)).ne')
lemma entry_add{P Q:JetArray (Potential G n)}(h:Ready P)(H:Ready Q): Fentry (P+Q)=Fentry P+ Fentry Q:=by rw [aged (h.add H),aged h, aged H,choir_add (baseV G n) VF_weight h H]
lemma entry_scale{P:JetArray (Potential G n)}(h:Ready P)(t:ℂ⟦X⟧): Fentry ((fun _=>t)*P)= t*Fentry P:=by rw [aged ((Ready.constant _).mul h),aged h,choir_scale (baseV G n) VF_weight h]

/-- Landau hard projections. No gaussian integration over ghosts needed here,
determinant included. Gets trace through FP reset in OTHER modules. -/
def LAND (a:Land G n):= wilson a.val
def LANDweight (a:Land G n):= Jacob a.val * ((paneLap G n).symm.toContinuousLinearMap ∘L paneGhost G n a).det
lemma LAND_eq: LAND (G:=G) (n:=n)= Pert.Orb.action G n ∘ g0 G n:= funext fun i=>(fixing_at i).symm
lemma LAND_go: Goal (LAND (G:=G) (n:=n)):=by rw [LAND_eq];exact VL_weight
lemma LANDweight_eq: LANDweight (G:=G) (n:=n) =ᶠ[𝓝 0] priceAll ∘ g0 G n:=pane_agrees.mono fun i hi=> congrArg (Jacob i.val*·) hi.symm

def chosen(G:Gauge)(n:Side):Measure (Land G n) := Measure.addHaar
instance chosen_haar(G:Gauge)(n:Side): Measure.IsAddHaarMeasure (chosen G n):=by unfold chosen;infer_instance
def Lentry (X:JetArray (Land G n)):= choir (chosen G n) LAND LANDweight X
lemma LAND_entry(X:JetArray (Land G n)): Lentry X= choir (chosen G n) (Pert.Orb.action G n ∘ g0 G n) (priceAll ∘ g0 G n) X:=by
 unfold Lentry choir; rw [LAND_eq]; unfold fibers fitR; rw [regrows LANDweight_eq]
lemma Lentry_add{P Q:JetArray (Land G n)}(h:Ready P)(H:Ready Q): Lentry (P+Q)=Lentry P+ Lentry Q:=choir_add (chosen G n) LAND_go h H
lemma Lentry_scale{P:JetArray (Land G n)}(h:Ready P)(t:ℂ⟦X⟧): Lentry ((fun _=>t)*P)= t*Lentry P:=choir_scale (chosen G n) LAND_go h t

structure WatchC(O: Wilson.Config G n→ℂ): Prop where
 gauge: ∀ t: Site n→G.El,(∀ x,t (-x)=t x)→ ∀ v, O (Lattice.gauge t v)=O v
 tame: ContDiffAt ℝ (⊤: ℕ∞) (O ∘ positiveLinks) 0
lemma rigidFl(hn:Admissible n){O:Wilson.Config G n→ℂ}(h:WatchC O): Fentry (ChartC (O∘positiveLinks))=Lentry (ChartC (fun A:Land G n=>O (positiveLinks A.val))):=by
 let f:= O ∘ positiveLinks; let g:=g0 G n
 have hk:0<priceAll (0:Potential G n):=by simp [priceAll]
 rw [aged (chart_ready _),LAND_entry,choir_parts (baseV G n) VF_weight (priceAll_smooth.of_le le_top) hk h.tame]
 have hp:ContDiffAt ℝ (↑(⊤:ℕ∞):WithTop ℕ∞) (priceAll ∘ g) 0:=by
    exact ContDiffAt.comp (g:=priceAll) (f:=g) 0 (by rw [map_zero];exact priceAll_smooth.of_le le_top) (ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Land G n) (F:=Potential G n) (g0 G n)).contDiffAt
 have hl:ContDiffAt ℝ (↑(⊤:ℕ∞):WithTop ℕ∞) (fun A:Land G n=>O (positiveLinks A.val)) 0:=by
    exact ContDiffAt.comp (g:=f) (f:=g) 0 (by rw [map_zero];exact h.tame) (ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Land G n) (F:=Potential G n) (g0 G n)).contDiffAt
 rw [choir_parts (chosen G n) (S:=Pert.Orb.action G n ∘ g0 G n) VL_weight hp hk hl]
 have H(t:ℂ→L[ℝ]ℝ): PipeF (baseV G n) (t ∘ O)= PipeL (chosen G n) (t ∘ O):=by
    have ht:Watching (t ∘ O):= ⟨fun u he v=>congrArg t (h.gauge u he v), t.contDiff.contDiffAt.comp (f:=f) 0 h.tame⟩
    obtain ⟨P,R⟩:= LocalH.actual G
    rw [pipeF_color (baseV G n) P R hn ht, pipeL_color (chosen G n) P R hn ht]
 exact congrArg₂ (·+·) (congrArg raise (H Complex.reCLM)) (congrArg (fun x=> PowerSeries.C Complex.I*raise x) (H Complex.imCLM))
end YM.SchemeRG11.Sway
