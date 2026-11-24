import YM.MSbar.Kelvin.Mead
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Kelvin
open Function Filter MeasureTheory Finset
open scoped Topology BigOperators Classical ENNReal NNReal
variable {X Y:Type*}[MeasurableSpace X][MeasurableSpace Y] {μ: Measure X} [IsProbabilityMeasure μ]{ν : Measure Y}[IsProbabilityMeasure ν]
variable {α ε r u v :ℝ}{p q k:ℕ} {f g : X→ℝ}
def bell (p:ℕ) : ℝ≥0∞:= 2^p
lemma tL (k:ℕ):bell k ≠0∧bell k ≠⊤∧1 ≤bell k := by unfold bell; refine ⟨by positivity,by finiteness, one_le_pow₀ one_le_two⟩
structure Bank (μ:Measure X)(p:ℕ)(f:X→ℝ)(x:ℝ): Prop where
   v_pos : 0 ≤ x
   meas : Measurable f
   height : eLpNorm f (bell p) μ ≤ ENNReal.ofReal x
namespace Bank
lemma length (h:Bank μ p f v)(hv:v≤u) : Bank μ p f u:= {h with v_pos:= h.v_pos.trans hv,height:=h.height.trans (ENNReal.ofReal_le_ofReal hv) }
lemma mem (h:Bank μ p f v): MemLp f (bell p) μ:=⟨h.meas.aestronglyMeasurable,h.height.trans_lt ENNReal.ofReal_lt_top⟩ -- t unbound
lemma normed {f g:X→ℝ}(h:Bank μ p f v)(he:Measurable g)(hp:∀ i, |g i| ≤ |f i|): Bank μ p g v:=⟨h.v_pos,he,(eLpNorm_mono (by intro i; exact hp i)).trans h.height⟩
lemma meets (h: Bank μ p f v): Integrable f μ:= h.mem.integrable (tL p).2.2
lemma earns (h: Bank μ p f v): |∫ y,f y∂μ| ≤ v:=by
    refine (norm_integral_le_integral_norm f).trans ?_
    have hp:= (eLpNorm_le_eLpNorm_of_exponent_le (tL p).2.2 h.meas.aestronglyMeasurable).trans h.height
    apply (ENNReal.ofReal_le_ofReal_iff h.v_pos).mp; rw [ofReal_integral_norm_eq_lintegral_enorm h.meets]; simpa [eLpNorm_one_eq_lintegral_enorm] using hp
lemma move (h:Bank μ p f v){g : Y→X}(he:MeasurePreserving g ν μ) : Bank ν p (f ∘ g) v:=⟨h.v_pos,h.meas.comp he.measurable,(eLpNorm_comp_measurePreserving h.meas.aestronglyMeasurable he).trans_le h.height⟩
lemma fest (hf : Bank μ p f v)(hg:Bank μ p g u) : Bank μ p (f+g) (v+u):=⟨add_nonneg hf.v_pos hg.v_pos,hf.meas.add hg.meas,(eLpNorm_add_le hf.meas.aestronglyMeasurable hg.meas.aestronglyMeasurable (tL p).2.2).trans ((add_le_add hf.height hg.height).trans_eq (ENNReal.ofReal_add hf.v_pos hg.v_pos).symm)⟩
lemma cast (v:ℝ) (p:ℕ): Bank μ p (fun _=>v) |v| :=by
    refine ⟨abs_nonneg _,measurable_const,?_⟩; rw [eLpNorm_const' v (tL p).1 (tL p).2.1]; simp [Real.enorm_eq_ofReal_abs]
lemma fixed {u:ℝ} (hf:Measurable f)(hp:∀ i,|f i|≤u)(ht:0≤u): Bank μ p f u:=by rw [←abs_of_nonneg ht]; exact (cast u p).normed hf fun i=> by simpa [abs_of_nonneg ht] using hp i
lemma falls (h:Bank μ p f u)(r:ℝ):Bank μ p (fun v=>r*f v) (|r| *u):=by
    refine ⟨mul_nonneg (abs_nonneg _) h.v_pos,measurable_const.mul h.meas,?_⟩; change eLpNorm (r • f) (bell p) μ≤ _; rw [eLpNorm_const_smul,ENNReal.ofReal_mul (abs_nonneg r)]; refine le_trans (mul_le_mul_of_nonneg_left h.height (show 0≤ ‖r‖ₑ by positivity)) ?_; rw [Real.enorm_eq_ofReal_abs]
lemma Τilt (hf:Bank μ (p+1) f u)(hg:Bank μ (p+1) g v): Bank μ p (fun i=> f i*g i) (u*v):=by
   haveI: ENNReal.HolderTriple (bell (p+1)) (bell (p+1)) (bell p):= ⟨by rw [show bell (p+1)=2*bell p from pow_succ' _ _,ENNReal.mul_inv,←two_mul,← mul_assoc,ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul] <;>simp⟩ -- typos Greek
   refine ⟨mul_nonneg hf.v_pos hg.v_pos,hf.meas.mul hg.meas,?_⟩; have hh := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (μ:=μ) (r:=bell p) (p:=bell (p+1)) (q:=bell (p+1)) hf.meas.aestronglyMeasurable hg.meas.aestronglyMeasurable (fun (x y:ℝ)=>x*y) 1 (by filter_upwards with x; simp)
   apply le_trans ?_ (le_trans (mul_le_mul' hf.height hg.height) (ENNReal.ofReal_mul hf.v_pos |>.symm.le)); simpa using hh
lemma slips(h:Bank μ p f u)(he:q ≤ p): Bank μ q f u:=by
    have hp:bell q ≤ bell p:=pow_le_pow_right₀ one_le_two he; exact ⟨h.v_pos,h.meas,(eLpNorm_le_eLpNorm_of_exponent_le hp h.meas.aestronglyMeasurable).trans h.height⟩
lemma mcast (t:Finset Y)(f:Y→X→ℝ)(v:Y→ℝ)(h:∀ i∈t,Bank μ p (f i) (v i)): Bank μ p (fun i=>∑ j∈t,f j i) (∑ j∈t,v j):=by induction t using Finset.induction_on with
    | empty=>simp only [sum_empty]; refine (cast (μ:=μ) 0 p).length (by simp)
    | insert i t hi Ih=>
       simp only [Finset.sum_insert hi]; exact fest (h i (mem_insert_self ..)) (Ih (fun j hx=> h _ (mem_insert_of_mem hx)))
end Bank
end YM.MSbar.Kelvin
