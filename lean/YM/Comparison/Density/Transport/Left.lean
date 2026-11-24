import YM.Comparison.Density.Transport.Tube
/-! # Converting back to the actual group-field norm

Ordered left derivatives: don't impose symmetry of these derivatives in
noncommuting directions. Includes full germ at health boundaries.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Transport
open Function Lattice RG Wilson MeasureTheory Filter WardBin.Lies
open AnalyticBridge.SectorAffine.Offset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical

variable {G : Gauge} {n : Side} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (f : Config G n→E) (L : LinkTube G) (w : ℝ)

def quote (L : LinkTube G) (l : ℕ) := Push.Uniform.composeCost l 1 (1+L.grade l)

def groupPrice (L : LinkTube G) (p : ℕ) := ∑ i ∈ Finset.range (p+1), quote L i

lemma quote_nonneg (l : ℕ) : 0≤ quote L l := by
  unfold quote Push.Uniform.composeCost; have hk:= L.tall l; positivity
lemma price_nonneg (l : ℕ) : 0≤ groupPrice L l := Finset.sum_nonneg fun i _=> quote_nonneg L i

variable (U : Config G n) (hU : ∀ i, G.chord (U i)<L.radius) (hw : 0<w) (hw' : w≤1) (hx : ‖logField U‖≤w)
include hU

/-- Smoothness for the chug identities is known even off full good if
the unmasked function has been defined by this germ on link logs. -/
lemma germ_smooth (l : ℕ) (h : ContDiffAt ℝ l (f ∘ increment 1) (logField U)) : Germ l f U := by
  let H:= increment U
  have he:= Work.G07.at_zero_increment U
  have hb : Continuous H:= by unfold H RG.increment; fun_prop
  have hp : ContDiffAt ℝ l (logField ∘ H) 0 := by
    refine contDiffAt_pi.mpr fun i=>?_
    have hf : ContDiffAt ℝ l (fun X : Directions G n=> G.mat (H X i)) 0 := by
      unfold H increment; simp only [G.mat_mul]
      exact ((G.exp_jet.of_le le_top|>.contDiffAt).comp _ (contDiffAt_apply ..)).mul contDiffAt_const
    apply ContDiffAt.comp (𝕜:=ℝ) (g:=G.plog) (f:=fun X=> G.mat (H X i)) 0 ?_ hf
    exact (show G.mat (U i) = G.mat (H 0 i) by rw [show H 0=U from he]) ▸ (L.smooth _ (hU i)).of_le le_top
  refine ((show ContDiffAt ℝ l (f ∘ increment 1) ((logField ∘ H) 0) by rw [Function.comp_apply,show H 0=U from he]; exact h).comp _ hp).congr_of_eventuallyEq ?_
  have ht : Tendsto H (𝓝 0) (𝓝 U):= he ▸ hb.tendsto 0
  filter_upwards [ht.eventually (recover_link L U hU)] with i hi
  exact congr_arg f hi.symm

include hw hw' hx
private lemma single_price (m s : ℕ) (d e : ℝ)
    (hm : s≤m) (hd : 0≤d) (he : 0≤e)
    (ha : ∀ A : Directions G n, ‖A‖≤w → Through m (f ∘ increment 1) A d)
    (hk : ∀ j<s, ‖iteratedFDeriv ℝ j (f ∘ increment 1) 0‖ ≤ e)
    (l : ℕ) (hl : l≤m) (X : Slab G n l) (h : ∀ i,‖X i‖≤w) :
    ‖leftDerivs f (List.ofFn X) U‖ ≤ quote L l*(s*e+d*w^s) := by
  let T:= f ∘ increment (1:Config G n)
  let A:= normLog U l w
  have hf : ‖A 0‖≤1 := by
    unfold A; rw [normLog_zero,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hw|>.le)]
    exact (inv_mul_le_iff₀ hw).2 (by simpa using hx)
  have hG := germ_smooth f L U hU l (through_le (ha (logField U) hx) hl).smooth
  have hg:= through_le (Transport.rescale s m w d e T hw.le hw' hd he hm ha hk (A 0) hf) hl
  let V := dilation (Slab G n l) w
  have hr : Through l ((f ∘ chug l U) ∘ V) 0 (Push.Uniform.composeCost l (s*e+d*w^s) (1+L.grade l)) := by
    apply Through.germ (hg.comp (log_tilt L U hU hw hw' hx l)) (show _=ᶠ[_]_ from ?_)
    have ht : Tendsto (chug l U ∘ V) (𝓝 0) (𝓝 U) := by
      convert ((chug_cont U l).comp V.continuous).tendsto (0:Slab G n l) using 2; simp [chug_zero]
    filter_upwards [ht.eventually (recover_link L U hU)] with j hj
    exact congr_arg f (by
      change increment 1 (w • (w⁻¹ • _)) = _
      simp only [← mul_smul,mul_inv_cancel₀ hw.ne',one_smul]
      exact hj)
  let B i := Pi.single (M:=fun _:Fin l=>Directions G n) i (w⁻¹ • X i)
  have hb i : ‖B i‖ ≤ 1 := by
    rw [show ‖B i‖= ‖w⁻¹ • X i‖ from Pi.norm_single _,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hw|>.le)]
    exact (inv_mul_le_iff₀ hw).2 (by simpa using h i)
  have hv i : V (B i)=Pi.single i (X i) := by
    funext j; by_cases he:j=i
    · subst j; change w • ((B i) i)= _; simp only [B,Pi.single_eq_same,←mul_smul,mul_inv_cancel₀ hw.ne',one_smul]
    change w • ((B i) j)= _; simp [B,he]
  have hX : leftDerivs f (List.ofFn X) U = iteratedFDeriv ℝ l ((f ∘ chug l U) ∘ V) 0 B := by
    rw [hG.takes X le_rfl,mixed_eval,liner V (by rw [map_zero]; exact chug_diff hG _),map_zero,
        ContinuousMultilinearMap.compContinuousLinearMap_apply]; simp only [hv]
  rw [hX]; apply le_trans ((mul_le_of_le_one_right (a:=‖iteratedFDeriv ℝ l ((f ∘ chug l U) ∘ V) 0‖)
    (b:= ∏ i, ‖B i‖) (norm_nonneg _) (Finset.prod_le_one (fun _ _=> norm_nonneg _) (fun i _=>hb i))) |> le_trans ((iteratedFDeriv ℝ l ((f ∘ chug l U) ∘ V) 0).le_opNorm B))
  apply (hr.pay l le_rfl).trans_eq; unfold Transport.quote Push.Uniform.composeCost; ring

/-- Norm statement at this configuration for directions in the plain ball.
Local/reanchored directions at arbitrary supports will be handled outside.
-/
lemma transport (m q s : ℕ) (d e : ℝ)
    (hm : s ≤ m) (hq : q≤m) (hd : 0≤d) (he : 0≤e)
    (ha : ∀ A : Directions G n, ‖A‖ ≤ w → Through m (f ∘ increment 1) A d)
    (hk : ∀ j<s, ‖iteratedFDeriv ℝ j (f ∘ increment 1) 0‖ ≤ e)
    (l : List (Directions G n)) (hl : l.length≤q) (h : ∀ i∈l,‖i‖≤w) :
    ‖leftDerivs f l U‖ ≤ groupPrice L q*(s*e+d*w^s) := by
  have hh i : ‖l.get i‖ ≤ w:= h _ (List.get_mem ..)
  have hs := single_price f L w U hU hw hw' hx m s d e hm hd he ha hk l.length (hl.trans hq) l.get hh
  rw [List.ofFn_get] at hs
  exact hs.trans (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _ => quote_nonneg L i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))) (by positivity))
end YM.Comparison.Density.Transport
