import YM.RG12.Strike.Stock
import Mathlib.MeasureTheory.Integral.Asymptotics
/-!
# One-vertex separated double-frost calculation. Absolute pay even when subtraction balls overlap!

At each endpoint Taylor subtract the *opened* exterior layers after collecting local
curvature derivatives and at most one opened action-vertex derivative into the exterior
factor. Thus engineering-weight criterion is simply spatial Taylor degree
< the integer singular exponent minus THREE (dimension four). Proof of this rule
for our full tested arrays separately. Intended for two distinct marked UV fields only
(other spectator wires don't see the integration position). See `Sol` for exact local jet
clean conditions. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Strike
open Function Set Filter Metric MeasureTheory Real Finset
open scoped Topology InnerProductSpace ContDiff BigOperators Classical
variable (χ:R→ℂ)(f g:R→ℂ)(x:R)(a b:ℕ)
def reach (χ f:R→ℂ)(a:ℕ)(v y:R):ℂ:=χ y * rainJet (a-3) f v y
def flakes (χ f g:R→ℂ)(a b:ℕ)(x:R)(y:R):ℂ:= f y*(g (y-x)-reach χ g a (-x) y) - g (y-x)* reach χ f b x (y-x)
def frosted (χ f g:R→ℂ)(a b:ℕ)(x:R):ℂ:=∫ y:R,flakes χ f g a b x y
variable {χ f g a b}
lemma flakes_span {p:R} : flakes χ f g a b x p=flakes χ g f b a (-x) (p-x):=by unfold flakes; simp only [neg_neg, sub_neg_eq_add,sub_add_cancel]; ring
variable (hχ : Base χ) (hf: Garden f a)(hg:Garden g b)
include hχ hf hg
omit hf hg in
lemma reach_cont : Continuous (reach χ f a x):= hχ.continu.mul (chart_cont ..)
lemma frost_me : Measurable (flakes χ f g a b x) := by
   have h: Measurable (fun y:R=>y-x) := measurable_id.sub_const x
   unfold flakes; exact (hf.me.mul ((hg.me.comp h).sub (reach_cont _ hχ).measurable)).sub ((hg.me.comp h).mul ((reach_cont _ hχ).measurable.comp h))
lemma frost_cont {p:R}(hp:p≠0)(hx:p≠x): ContinuousAt (flakes χ f g a b x) p:=by
   have h : ContinuousAt (fun y:R=>y-x) p:=continuousAt_id.sub continuousAt_const
   have H:=ContinuousAt.comp (f:=fun y:R=>y-x) (g:=g) ((hg.openSite (p-x) (sub_ne_zero.mpr hx)).continuousAt) h
   unfold flakes; exact ((hf.openSite p hp).continuousAt.mul (H.sub (reach_cont _ hχ).continuousAt)).sub (H.mul ((reach_cont _ hχ).continuousAt.comp h))
-- price at singular sites; no claims of log integrability exactly crit!
lemma thawZero (hx:x≠0)(ha:3 ≤ a) : ∃ C:ℝ,0 ≤ C ∧ ∀ᶠ y:R in 𝓝 0, y≠0 → ‖flakes χ f g a b x y‖ ≤ C/‖y‖^3:=by
    let A(y:R):= g (y-x)*reach χ f b x (y-x)
    have h:ContinuousAt (fun y:R=>y-x) 0:= continuousAt_id.sub continuousAt_const
    have H:= ContinuousAt.comp (f:=fun y:R=>y-x) (g:=g) ((hg.openSite (_:R) (show 0-x≠0 from sub_ne_zero.mpr hx.symm)).continuousAt) h
    obtain ⟨B,hB,he⟩:= hg.zone (-x) (a-3) (neg_ne_zero.mpr hx) -- argument order
    obtain ⟨D,hD,hW⟩:= hf.prix
    let T:=‖A 0‖+1
    have ht : 0 ≤ T:=by unfold T; positivity
    have he' : ∀ᶠ y:R in 𝓝 0,‖A y‖ ≤ T := (H.mul ((reach_cont x hχ).continuousAt.comp h)).norm.eventually (ge_mem_nhds (by change ‖A 0‖ < ‖A 0‖+1; linarith only [zero_lt_one (α:=ℝ)]))
    refine ⟨D*B+T,by positivity,?_⟩
    filter_upwards [he, he',hχ.head, Metric.ball_mem_nhds (0:R) (show (0:ℝ)<1 by norm_num)] with y hy hY hy1 hyz
    intro hy2; have hq:=norm_pos_iff.mpr hy2
    unfold flakes
    change ‖f y*(g (y-x)-reach χ g a (-x) y)-A y‖ ≤ _
    grw [norm_sub_le,norm_mul,hW y hy2,hY]
    rw [reach,hy1,one_mul,show y-x=y+ -x from sub_eq_add_neg ..]
    grw [hy]; rw [show ‖y‖^a= ‖y‖^(a-3)*‖y‖^3 from by rw [← pow_add,Nat.sub_add_cancel ha]]
    have hu : ‖y‖ ≤ 1:= (by simpa only [mem_ball,dist_zero_right] using! (show y∈Metric.ball (0:R) 1 from hyz) : ‖y‖ < 1).le
    have ht' : ‖y‖^ (3:ℕ) ≤ 1 := pow_le_one₀ (norm_nonneg _) hu
    field_simp
    nlinarith -- check
lemma thawAt (hx:x≠0)(hb:3 ≤ b) : ∃ C:ℝ,0 ≤ C ∧ ∀ᶠ y:R in 𝓝 x,y ≠ x → ‖flakes χ f g a b x y‖ ≤ C/‖y-x‖^3:=by
    obtain ⟨C,hC,he⟩:= thawZero (-x) hχ hg hf (neg_ne_zero.mpr hx) hb
    have h : Tendsto (fun y:R=>y-x) (𝓝 x) (𝓝 0):=by rw [← sub_self x]; exact (continuousAt_id.sub continuousAt_const)
    refine ⟨C,hC,(h.eventually he).mono fun y hy h'=>?_⟩
    rw [flakes_span]; exact hy (sub_ne_zero.mpr h')
-- pay from any such frost book and a continuous rim.
omit hχ hf hg
lemma snow (x:R)(C:ℝ)(hC:0≤C):LocallyIntegrable (fun y:R=>C/‖y-x‖^3):=by
   let F(y:R):=C/‖y‖^3
   have hm: AEStronglyMeasurable F volume:= (measurable_const.div (continuous_norm.measurable.pow_const 3)).aestronglyMeasurable -- type?
   have hi: LocallyIntegrable F:=by
     refine locallyIntegrable_of_norm_le_rpow (C:=C) (α:=((3:ℕ):ℝ)) ?_ ?_ ?_ hm
     · simp
     · norm_num
     apply ae_of_all; intro y
     unfold F; rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg_natCast,zpow_neg,zpow_natCast]; exact le_of_eq (div_eq_mul_inv ..)
   let e:=Homeomorph.addRight (-x)
   have he:Measure.map e (volume:Measure R)=volume:=map_add_right_eq_self volume (-x)
   rw [← he,locallyIntegrable_map_homeomorph] at hi
   rw [show (fun y:R=>C/‖y-x‖^3)=F ∘ e from funext fun y=>by unfold F; simp [e, sub_eq_add_neg]]
   exact hi
lemma hearth (p:R)(F:R→ℂ)(hf:Measurable F){C:ℝ}(hc:0 ≤ C)(he:∀ᶠ y:R in 𝓝 p,y≠p → ‖F y‖ ≤ C / ‖y-p‖^3):IntegrableAtFilter F (𝓝 p) volume:=by
   let V:=({y:R| ‖F y‖ ≤ C / ‖y-p‖^3} ∪ {p}:Set R)
   obtain ⟨U,hU,h⟩:= snow p C hc p
   have hM:MeasurableSet V:= (measurableSet_le hf.norm (by fun_prop)).union (measurableSet_singleton _)
   have hv:V ∈ 𝓝 p:= he.mono fun y hy=> Classical.or_iff_not_imp_right.mpr fun hu: y ∉ ({p}:Set R)=> hy hu -- theorem?
   refine ⟨U∩V,inter_mem hU hv, Integrable.mono' (h.mono_set (show U∩V ⊆ U from inter_subset_left)) hf.aestronglyMeasurable.restrict ?_⟩
   let K(y:R):= C / ‖y-p‖^3
   have hh : ∀ᵐ y:R ∂(volume.restrict V), y∈V∧y≠p:=(ae_restrict_mem hM).and (ae_restrict_of_ae (volume.ae_ne p))
   have hr := hh.mono (fun y hy=> show ‖F y‖ ≤ K y from Or.resolve_right hy.1 hy.2)
   exact hr.filter_mono (ae_mono (Measure.restrict_mono (show U∩V ⊆ V from inter_subset_right) le_rfl)) -- names
include hχ hf hg
lemma warms (hx:x≠0)(ha:3≤a)(hb:3≤b): LocallyIntegrable (flakes χ f g a b x) := by
    intro p; have he:= frost_me x hχ hf hg
    by_cases hp:p=0
    · subst p; obtain ⟨C,hC,h⟩:= thawZero x hχ hf hg hx ha
      exact hearth 0 _ he hC (h.mono (fun x hx hx'=>by simpa only [sub_zero] using hx hx'))
    by_cases hv:p=x
    · subst p; obtain ⟨C,hC,h⟩:= thawAt x hχ hf hg hx hb; exact hearth x _ he hC h
    -- pick small compact
    have hm(x:R)(hx:p≠x):({x}:Set R)ᶜ ∈ 𝓝 p := isOpen_compl_singleton.mem_nhds hx
    obtain ⟨r,hr,h⟩:= Metric.mem_nhds_iff.mp (inter_mem (hm _ hp) (hm _ hv))
    refine ⟨Metric.closedBall p (r/2),Metric.closedBall_mem_nhds _ (by linarith), ContinuousOn.integrableOn_compact (isCompact_closedBall ..) ?_⟩ -- order
    intro y hy; have hh:= h (Metric.closedBall_subset_ball (by linarith:r/2<r) hy)
    exact (frost_cont _ hχ hf hg (p:=y) hh.1 hh.2).continuousWithinAt
lemma liquid (ha:3≤a)(hb:3≤b): ∃ C:ℝ,0 ≤ C∧ ∀ᶠ y:R in cocompact R, ‖flakes χ f g a b x y‖ ≤ C* ((1+‖y‖)^6)⁻¹:=by
   obtain ⟨K,hK,h1⟩:= hf.outer 0
   obtain ⟨B,hB,h2⟩:= hg.outer x
   simp_rw [sub_zero] at h1
   have h3:χ =ᶠ[cocompact R] (0:R→ℂ) := Filter.coclosedCompact_eq_cocompact.subst (motive:=fun j=> χ =ᶠ[j] 0) (hasCompactSupport_iff_eventuallyEq.mp hχ.compact)
   let e:=Homeomorph.addRight (-x)
   have he : HasCompactSupport (fun y:R=>χ (y-x)) := by convert hχ.compact.comp_homeomorph e using 1; ext1 l; simp [e,sub_eq_add_neg]
   rw [hasCompactSupport_iff_eventuallyEq,Filter.coclosedCompact_eq_cocompact] at he
   refine ⟨K*B,mul_nonneg hK.le hB.le,?_⟩
   filter_upwards [h1,h2,h3,he] with y hy hy' hv hq
   unfold flakes reach; change χ y=0 at hv; change χ (y-x)=0 at hq
   rw [hv,hq,zero_mul,zero_mul,mul_zero,sub_zero,sub_zero,norm_mul]
   let d:=1+‖y‖; have hd:1≤d:=by unfold d; linarith only [norm_nonneg y]
   have hd':0<d:=zero_lt_one.trans_le hd
   grw [hy,hy']; rw [div_mul_div_comm,← pow_add,← div_eq_mul_inv]
   gcongr; omega -- chooses pow monotonic?
-- outer cost integrated via theorem
lemma lively (hx:x≠0)(ha:3≤a)(hb:3≤b): Integrable (flakes χ f g a b x):=by
   obtain ⟨C,hC,h⟩:= liquid x hχ hf hg ha hb
   let A(z:R):=((1+‖z‖)^6)⁻¹
   refine (warms x hχ hf hg hx ha hb).integrable_of_isBigO_cocompact (g:=A) (Asymptotics.isBigO_iff.mpr ⟨C,h.mono fun z hz => ?_⟩) (Integrable.integrableAtFilter ?_ _)
   · change _ ≤ C* ‖A z‖; rw [Real.norm_of_nonneg (by unfold A; positivity)]; exact hz
   have hi : Integrable (fun w:R=> (1+‖w‖)^(-((6:ℕ):ℝ))) :=integrable_one_add_norm (by norm_num)
   simp_rw [Real.rpow_neg_natCast,zpow_neg,zpow_natCast] at hi; exact hi
end YM.RG12.Strike
