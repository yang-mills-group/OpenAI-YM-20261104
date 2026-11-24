import YM.MS.Arc.Carl
/-!
# Compare holomorphic parts by Streak costs

Costs Town Growth, extract all positive integers equality. Grammar path composed externally. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arc
open Function Filter Set Finset MeasureTheory Real Metric
open scoped Topology ContDiff Interval
variable {F:Type}[NormedAddCommGroup F][NormedSpace ℂ F][CompleteSpace F]{z:ℂ}{f g:ℂ→F}
lemma Town.right : right0 ⊆ Town := fun x hx=> by have hm:0<x.re:= hx; show 0<2*x.re+1; linarith
lemma joined : IsPreconnected Town:= by
   refine Convex.isPreconnected ?_; intro x hx y hy u v hu hv h; change 0<2*Complex.re (u • x+ v • y)+1; simp only [Complex.add_re,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul, sub_zero]; change 0< 2*x.re+1 at hx; change 0<2*y.re+1 at hy; rcases eq_or_lt_of_le hu with hu|hu <;> nlinarith

def Glow (f:ℂ→F)(A:ℝ): Prop:=∃ C:ℝ,0<C∧∃ b:ℕ,∀ i∈Town,‖f i‖≤ C*(1+‖i‖)^b*LogMass A i
structure Clearing (f:ℂ→F): Prop where
    moss: Forest Town f
    pay:∃ A:ℝ,1≤A∧ Glow f A
lemma Gl {z:ℂ}(hx:z∈right0): 1≤‖z+1‖∧‖z‖≤‖z+1‖:= by
    have ht:=Ynum z; have he:= Ynum (z+1); simp only [Complex.add_re,Complex.one_re,Complex.add_im,Complex.one_im,add_zero] at he; have h : 0<z.re:=hx; constructor <;> nlinarith [norm_nonneg z,norm_nonneg (z+1)]
lemma town_stop (h:Forest Town f)(hp:∀ x:ℝ,1≤x→ f x=0): Set.EqOn f 0 Town:= by
    let Z:=𝓝[>] (1:ℝ); have he : ∃ᶠ i in 𝓝[≠] (1:ℂ), f i=0:= by
        have hx: Tendsto Complex.ofReal Z (𝓝[≠] (1:ℂ)):= by
            refine tendsto_nhdsWithin_iff.mpr ⟨?_,?_⟩; · exact Complex.ofReal_one ▸ (Complex.continuous_ofReal.continuousAt.continuousWithinAt : ContinuousWithinAt Complex.ofReal (Ioi (1:ℝ)) 1)
            exact (show ∀ᶠ t in Z,t∈Ioi (1:ℝ) from self_mem_nhdsWithin).mono (fun k h=> by have h : (1:ℝ)<k:=h; rw [Set.mem_compl_iff,Set.mem_singleton_iff]; exact_mod_cast h.ne')
        exact hx.frequently (Filter.Eventually.frequently ((show ∀ᶠ t in Z,t∈Ioi (1:ℝ) from self_mem_nhdsWithin).mono fun k h=> hp k ((show 1<k from h).le)))
    have hQ : DifferentiableOn ℂ f Town := fun i hi=> (h i hi).differentiableWithinAt; exact (hQ.analyticOnNhd way).eqOn_zero_of_preconnected_of_frequently_eq_zero joined (by norm_num [Town,ups]) he -- inspect
lemma flourishing (h:Clearing f)(hf:∀ᶠ n:ℕ in atTop, f n=0): Set.EqOn f 0 Town := by
    obtain ⟨A,hA,C,hC,b,hb⟩:= h.pay; let X(z:ℂ):= cloud z A; have hm:A>0:=zero_lt_one.trans_le hA; have hn z: X z≠0:= by (exact norm_pos_iff.mp ((cloud_weight (z:=z) hm).symm ▸ rpow_pos_of_pos hm _))
    let u(z:ℂ):= X z * (z+1)^b; have ht z (hp:z∈right0): u z≠0:= by unfold u; have he:= Gl hp; refine mul_ne_zero (hn z) (pow_ne_zero _ (norm_pos_iff.mp ?_)); linarith only [he.1]
    let G z := (u z)⁻¹ • f z; have H : Forest right0 G:= fun z hz=> ((((( (cloud_hol A hm z).mul (show DifferentiableAt ℂ (fun z:ℂ=> (z+1)^b) z by fun_prop)).inv (ht z hz)).smul (h.moss z (Town.right hz))) )) -- parentheses
    have hh z (hz:z∈right0) : ‖G z‖≤ C*2^b:= by
        unfold G; rw [norm_smul,norm_inv, ← div_eq_inv_mul,div_le_iff₀ (norm_pos_iff.mpr (ht z hz))]; apply (hb z (Town.right hz)).trans; obtain ⟨h1,h2⟩:= Gl hz; have hh : 1+‖z‖≤ 2* ‖z+1‖:= by linarith
        have ht:0<LogMass A z:= rpow_pos_of_pos hm _; unfold u X; rw [norm_mul,norm_pow,cloud_weight hm]; change _≤ C*_ * (LogMass A z * _); calc
          _ ≤ C*(2*‖z+1‖)^b*LogMass A z:= by gcongr
          _ = _ := by rw [mul_pow]; ring
    refine town_stop h.moss ?_; intro r hr; have he := clears H hh (show ∀ᶠ n:ℕ in atTop, G n=0 from ?_) hr
    swap; · refine hf.mono (fun i hi=>?_); unfold G; rw [hi]; simp
    exact (smul_eq_zero.mp (show (u r)⁻¹ • f (r:ℂ)=0 from he)).resolve_left (inv_ne_zero (ht _ (right_float (by linarith : 0<r))))
end YM.MS.Arc
