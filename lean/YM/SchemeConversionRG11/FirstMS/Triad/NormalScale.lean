import YM.SchemeConversionRG11.FirstMS.Triad.Sparks

/-! True scaling before subtracting and before hat integral. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.FirstMS.Triad
open Function Set Filter MSbar MSbar.Symbol MeasureTheory Metric Complex DR Maxwell Pert.Triangle Analysis
open scoped Topology ContDiff BigOperators Classical InnerProductSpace

def owns (F:ℂ→E4→ℝ→ℂ)(N:ℂ→ℂ):Prop:= ∀ s∈neighborhood,∀ p∈region,∀ t:ℝ,0<t→F s (t • p.1) (t^2*p.2)=(t:ℂ)^(N s)*F s p.1 p.2
lemma abides : owns bridge (fun z=> -2-2*z) := by
   rintro s hs p hp t ht
   unfold bridge; rw [norm_smul, Real.norm_of_nonneg ht.le,mul_pow,←mul_add,ofReal_mul,
      mul_cpow_ofReal_nonneg (by positivity) (show 0 ≤ ‖p.1‖^2+p.2 from le_of_lt hp)] -- fix
   have he : (↑(t^2):ℂ)^(-1-s)=(↑t:ℂ)^(-2-2*s):=by
      rw [sq,ofReal_mul,mul_cpow_ofReal_nonneg ht.le ht.le,← cpow_add _ _ (ofReal_ne_zero.mpr ht.ne')]; ring_nf
   rw [he,mul_left_comm]

variable {F:ℂ→E4→ℝ→ℂ} {N:ℂ→ℂ}
lemma stays {p:Patch} (hp:p∈region){t:ℝ}(ht:0<t) : (t • p.1,t^2*p.2)∈region := by
   change 0 < ‖t • p.1‖^2+_
   rw [norm_smul,Real.norm_of_nonneg ht.le, mul_pow]; change 0 < _+t^2*p.2
   rw [←mul_add]; exact mul_pos (sq_pos_of_pos ht) hp

lemma owns.next (h : owns F N) (hf:Off F) (a:Axis) : owns (axisStep a F) (fun z=> N z-1) := by
   rintro s hs ⟨v,u⟩ hp t ht
   have hr := stays hp ht; have hc : (↑t:ℂ) ≠ 0:=ofReal_ne_zero.mpr ht.ne'
   let L:= fun x:E4=> (s,x,t^2*u)
   have hA : DifferentiableAt ℝ (fun v=>F s v (t^2*u)) (t • v) := ((hf.smooth s hs _ hr).differentiableAt (by simp)).comp (f:=L) (t • v) (by unfold L; fun_prop)
   have hB : DifferentiableAt ℝ (fun v=>F s v u) v := ((hf.smooth s hs (v,u) hp).differentiableAt (by simp)).comp (f:=fun v => (s,v,u)) v (by fun_prop)
   let E := ContinuousLinearMap.id ℝ E4; let c := N s; let A : E4→ℂ:= fun v=> F s v (t^2*u); let D:= (fderiv ℝ A (t • v)); let B:= fun v=> F s v u
   let Z:= fun v=> (↑t:ℂ)^c*B v
   have he : Z =ᶠ[𝓝 v] A ∘ (fun x:E4=> t • x) := by
      filter_upwards [((reg_open.preimage (continuous_id'.prodMk continuous_const)).mem_nhds (show v∈(fun v=>(v,u)) ⁻¹' region from hp))] with x hx
      exact (h s hs (x,u) hx t ht).symm
   have hy := he.fderiv_eq (𝕜:=ℝ)
   have hw : HasFDerivAt (fun x:E4=>t • x) (t • E) v:= (t • E).hasFDerivAt
   let Y := (ContinuousLinearMap.mul ℝ ℂ) ((↑t:ℂ)^c)
   have hh : fderiv ℝ Z v= Y.comp (fderiv ℝ B v):= (Y.hasFDerivAt.comp v hB.hasFDerivAt).fderiv
   rw [hh,(hA.hasFDerivAt.comp v hw).fderiv] at hy
   have hQ:= DFunLike.congr_fun hy (basis a)
   change (↑t:ℂ)^c*axisStep a F s v u = D (t • basis a) at hQ
   rw [map_smul,Complex.real_smul] at hQ
   change D (basis a)=(t:ℂ)^(c-1)*_
   rw [cpow_sub _ _ hc,cpow_one]; field_simp; rw [hQ,mul_comm] -- fix

lemma owns_lane (b:Bool)(i:Fin 3)(μ:Axis) : owns (fun z=>lane z b i μ) (fun z=> -3-2*z) := by
   rintro s hs v hv t ht; change lane s b i μ _ _ = (↑t:ℂ)^(-3-2*s)*_
   unfold lane; rw [Finset.mul_sum]
   refine Finset.sum_congr rfl fun j _=> ?_
   have he := (abides.next off_bridge j) s hs v hv t ht
   change _* (- axisStep j bridge s _ _)=_*(_*(-axisStep j bridge s _ _))
   rw [he]; dsimp only; rw [show -2-2*s-1=-3-2*s by ring]; ring

lemma owns_bar (b:Bool)(i:Fin 3)(a μ:Axis): owns (fun z=>bar z b i a μ) (fun z=>-4-2*z) := by
   intro s hs p hp t ht
   change bar s b i a μ (t • p.1) (t^2*p.2)=(t:ℂ)^(-4-2*s)*_
   rw [show -4-2*s=-3-2*s-1 by ring]; exact ((owns_lane b i μ).next (off_lane b i μ) a) s hs p hp t ht
end YM.SchemeConversionRG11.FirstMS.Triad
