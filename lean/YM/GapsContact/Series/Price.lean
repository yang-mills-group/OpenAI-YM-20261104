import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Propagation currency. Fixed-power descent vs growing powers.

Run on differences (both of interacting amplitudes and of Lagrange panel extractors).
Any loss powers are independent of truncation/extractor order through fixed families
as specified. No assumption on complex germ comparisons yet, or analytic extensions of the
answers; those eventually have to be earned along the same corridors. A strip mechanism handles
both dilation-along-single-complex-lines and crawling off the Euclidean slice.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Pattern
open Function Filter Set Metric
open scoped Topology BigOperators Classical
variable {Ω ι J E H : Type*}
variable [NormedAddCommGroup H]
-- ι already notation binder reserved? replace
variable {f:Filter Ω}

def TagPrice (f:Filter Ω)(F:Ω→ J→ H)(K:Set J)(w:Ω→ℝ):= ∃ C:ℝ, 0≤C ∧ ∀ᶠ i in f,∀ x∈ K, ‖F i x‖ ≤ C*w i

abbrev Scoped (f:Filter Ω)(F:Ω→ J→ H)[TopologicalSpace J](U:Set J)(w:Ω→ℝ):= ∀ K:Set J,IsCompact K→ K⊆U → TagPrice f F K w

variable {A B:Ω→J→H}{R T U:Set J}{w w':Ω→ℝ}
lemma TagPrice.mono (h:TagPrice f A R w)(hx:T⊆R)(hp:∀ᶠ i in f,w i≤ w' i): TagPrice f A T w':=by
  obtain ⟨C,hC,h⟩:=h; exact ⟨C,hC,(h.and hp).mono fun i hh x hx'=> (hh.1 x (hx hx')).trans (mul_le_mul_of_nonneg_left hh.2 hC)⟩
lemma TagPrice.parent (h:TagPrice f A R w)(hx:T⊆R):TagPrice f A T w:=h.mono hx (Eventually.of_forall fun _=>le_rfl)
lemma TagPrice.up (h:TagPrice f A R w)(hq:∀ᶠ i in f,w i ≤ w' i):TagPrice f A R w' :=h.mono (Set.Subset.refl R) hq
lemma TagPrice.union (h:TagPrice f A R w)(hx:TagPrice f A T w)(hq:∀ᶠ i in f,0≤w i):TagPrice f A (R∪T) w:=by
  obtain ⟨C,hC,h⟩:=h; obtain ⟨D,hD,h'⟩:=hx; refine ⟨max C D,hC.trans (le_max_left ..),?_⟩
  filter_upwards [h,h',hq] with i hi hq ht x hX
  rcases hX with hx|hx; exact (hi x hx).trans (mul_le_mul_of_nonneg_right (le_max_left ..) ht)
  exact (hq x hx).trans (mul_le_mul_of_nonneg_right (le_max_right ..) ht)
lemma TagPrice.congr (h:TagPrice f A R w)(hx:∀ᶠ i in f,EqOn (A i) (B i) R): TagPrice f B R w:=by
  obtain ⟨C,hC,h⟩:=h; exact ⟨C,hC,(h.and hx).mono fun i h x hx=> h.2 hx ▸ h.1 x hx⟩ -- direction?
lemma TagPrice.add (h:TagPrice f A R w)(hx:TagPrice f B R w): TagPrice f (fun i x=> A i x + B i x) R w:=by
  obtain ⟨C,hC,h⟩:=h; obtain ⟨D,hD,h'⟩:=hx; refine ⟨C+D, by positivity,?_⟩
  filter_upwards [h,h'] with i hi ht x hx
  rw [add_mul]; exact norm_add_le_of_le (hi x hx) (ht x hx)
lemma TagPrice.sub (h:TagPrice f A R w)(hx:TagPrice f B R w): TagPrice f (fun i x=> A i x - B i x) R w:=by
  obtain ⟨C,hC,h⟩:=h; obtain ⟨D,hD,h'⟩:=hx; refine ⟨C+D, by positivity,?_⟩
  filter_upwards [h,h'] with i hi ht x hx
  rw [add_mul]; exact norm_sub_le_of_le (hi x hx) (ht x hx)
lemma TagPrice.tends (h:TagPrice f A R w)(hw:Tendsto w f (𝓝 0)) (x:J)(hx:x∈R) : Tendsto (fun i=> A i x) f (𝓝 0) :=by
   obtain ⟨C,hC,ht⟩:=h; apply tendsto_zero_iff_norm_tendsto_zero.mpr
   exact squeeze_zero' (Eventually.of_forall fun _=> norm_nonneg _) (ht.mono fun _ h=> h x hx) (by simpa using hw.const_mul C)

section plate
open Complex HadamardThreeLines
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℂ H]
variable {A B:Ω→E→H}{S T U K:Set E}{R: Set E}{u w:Ω→ℝ}
abbrev band := verticalClosedStrip 0 1
lemma handle (C D:ℝ)(h: ℂ→H) (hc: 0 ≤ C)(hd:0≤D)(he:AnalyticOnNhd ℂ h band)(hA:∀ z∈ band, ‖h z‖ ≤ D) (hB:∀ z:ℂ,z.re=0 → ‖h z‖ ≤ C) : ‖h (1/2:ℂ)‖^2 ≤ C*D:=by
   let z:ℂ:= (↑(1/2:ℝ)); have hz:z∈ band:=by change z.re∈ Icc (0:ℝ) 1; simp [z]; norm_num
   have hh: ‖h z‖ ≤ C^(1-z.re)*D^z.re:= by
      refine norm_le_interp_of_mem_verticalClosedStrip₀₁' h hz ?_ ⟨D,?_⟩ hB ?_
      · refine ⟨he.differentiableOn.mono (preimage_mono Ioo_subset_Icc_self),he.continuousOn.mono ?_⟩
        change closure _⊆ re ⁻¹' Icc (0:ℝ) 1; exact closure_minimal (preimage_mono Ioo_subset_Icc_self) (isClosed_Icc.preimage continuous_re)
      · rintro t ⟨s,hs,rfl⟩; exact hA s hs
      intro t ht; apply hA t; rw [band,verticalClosedStrip, Set.mem_preimage,show t.re=1 from ht]; simp
   have hC: ‖h z‖^2 ≤ _ := pow_le_pow_left₀ (norm_nonneg _) hh 2; rw [mul_pow] at hC; simp_rw [show 1-z.re=(1/2:ℝ) by norm_num [z],show z.re=1/2 by norm_num [z],← Real.sqrt_eq_rpow,Real.sq_sqrt hc,Real.sq_sqrt hd] at hC; simpa only [z, ofReal_div, ofReal_one,ofReal_ofNat] using hC

-- supporting a band for any endpoint (may use SAME h or different maps)
def Covered (S R T:Set E) := ∀ x∈T, ∃ g:ℂ→E, g (1/2)=x ∧ AnalyticOnNhd ℂ g band ∧ MapsTo g band R ∧ ∀ z:ℂ,z.re=0→g z∈S
lemma TagPrice.handle {b p:ℕ}(hu:∀ᶠ i in f, 0<u i)(h:Covered S R T) (hh:∀ᶠ i in f,AnalyticOnNhd ℂ (A i) R) (hl:TagPrice f A S (fun i=> u i^(2*p+b))) (hx:TagPrice f A R (fun i=> (u i)⁻¹^b)): TagPrice f A T (fun i=> u i^p):=by
    obtain ⟨C,hC,hU⟩:=hl; obtain ⟨D,hD,hV⟩:=hx
    refine ⟨Real.sqrt (C*D),Real.sqrt_nonneg _,?_⟩; filter_upwards [hu,hU,hV,hh] with i hi hL hP H x hx
    obtain ⟨g,rfl,hg,hR,hS⟩:=h x hx
    apply le_of_sq_le_sq _ (by positivity)
    refine (Pattern.handle _ _ (A i ∘ g) (by positivity) (by positivity) (H.comp hg hR) (fun x h=>hP _ (hR h)) (fun z hz=> hL _ (hS _ hz))).trans_eq ?_
    rw [mul_pow (Real.sqrt ..), Real.sq_sqrt (by positivity), pow_add, inv_pow, mul_comm 2 p,pow_mul]; field_simp

lemma dilate (r:ℝ)(hr:0<r) (x:E): Covered (closedBall x r) (closedBall x (4*r)) (closedBall x (2*r)):=by
   intro y hy; let p(z:ℂ):= Complex.exp ((Real.log 2:ℝ)*(2*z-1)); let g(z:ℂ):=x+p z • (y-x)
   have hP:Differentiable ℂ p:=by unfold p; fun_prop
   have he (z:ℂ): ‖p z‖=Real.exp (Real.log 2*(2*z.re-1)):=by unfold p; rw [Complex.norm_exp,re_ofReal_mul]; norm_num
   have hp(z:ℂ): dist (g z) x ≤ ‖p z‖*(2*r):=by simp only [g,dist_eq_norm,add_sub_cancel_left,norm_smul]; exact mul_le_mul_of_nonneg_left (dist_eq_norm y x ▸ (Metric.mem_closedBall.mp hy)) (norm_nonneg _)
   refine ⟨g,?_,fun z hz=> analyticAt_const.add (?_),fun z hz=> ?_,fun z hz=> ?_⟩
   · simp only [p,g,mul_one_div_cancel (show (2:ℂ)≠0 by norm_num),sub_self,mul_zero,Complex.exp_zero,one_smul]; abel
   · exact ((hP.analyticAt _).smul analyticAt_const)
   · have ht:z.re≤1:=(show z.re∈Icc (0:ℝ) 1 from hz).2
     have h₀:0≤Real.log 2:=Real.log_nonneg (by norm_num)
     have hx: ‖p z‖ ≤ 2:= (he z).le.trans ((Real.exp_le_exp.mpr (show _≤Real.log 2 by nlinarith)).trans_eq (Real.exp_log (by norm_num)))
     exact (hp z).trans (by nlinarith)
   have ha: ‖p z‖ = 2⁻¹:=by rw [he,hz]; norm_num [Real.exp_neg]; rw [Real.exp_log (by norm_num)]; ring
   exact (hp z).trans (by rw [ha]; apply le_of_eq; ring)
end plate
end YM.GapsContact.Pattern
