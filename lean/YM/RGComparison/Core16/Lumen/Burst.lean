import YM.RGComparison.Core16.Lumen.Fable

/-!
# Taylor profiles at whole Law, uniform ADMITTED geometry

Don't drop tails conditioned on other markers. Link-slot payment respects persistence off-flag
and keeps same term everywhere. Local slot event aperture after L at each mom. Norms curvature
alphabet center. Back-panel price remains post-L & post finite horizon (not post-volume).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lumen
open Function Filter Lattice RG Tree Wilson MeasureTheory Pressure Metric Push.Uniform Forge
open Planet Finset
open PertExtension PertExtension.Series Tested Radial
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge}{S:Side}{L ι k T A D:Type}[Fintype ι][Fintype L]
variable {X:Shelf G A D} {P:Planet X S ι k T}

def bundle (w:Rail G ι): Finset ι:= (w.map Prod.fst).toFinset
omit [Fintype ι] in lemma bundle_cap (w:Rail G ι): (bundle w).card ≤ w.length:=by simpa [bundle] using List.toFinset_card_le (l:=w.map Prod.fst)
omit [Fintype ι] in
lemma ceiling (u:Wire G ι)(x:Sky G ι)(W g:ℝ)(hg:0<g)(h:G.chord (x u.1)≤g*W):|tally g u x| ≤ W := by
    unfold tally; rw [abs_div,abs_of_pos hg,div_le_iff₀ hg]; exact (mono_cone _ _).trans ((G.curvature_norm _).trans (h.trans_eq (mul_comm ..)))
omit [Fintype ι] in
lemma sing_area (w:Rail G ι)(x:Sky G ι)(n:ℕ){g m:ℝ}(hn:w.length≤n)(hm:1≤m)(hh:∀i∈w,|tally g i x| ≤ m): |sing w g x| ≤ m^n:= by
    refine le_trans (?_ : _ ≤ m^w.length) (by gcongr); induction w generalizing n with
    | nil=>simp [sing]
    | cons a w ih=>rw [sing_cons,abs_mul,List.length_cons,pow_succ']; exact mul_le_mul (hh a (List.mem_cons_self ..)) (ih n (by simp at hn; omega) (fun i hi=> hh i (List.mem_cons_of_mem _ hi))) (abs_nonneg _) (zero_le_one.trans hm)
omit [Fintype ι] in
lemma sing_price (x:Sky G ι){g:ℝ}(hg:0<g)(hu:g≤1){w:Rail G ι}{n:ℕ}(hb:w.length ≤ n):|sing w g x| ≤ (2/g)^n:=by
    apply sing_area w x _ hb ?_; intro i _; apply ceiling i x _ g hg; convert G.chord_le_two (x i.1) using 1; field_simp
    rw [le_div_iff₀ hg,one_mul]; linarith
omit [Fintype ι] in
lemma height {f: Melody G ι}{n:ℕ}{c g:ℝ}(H:Offers n c f)(hg:0<g)(hu:g≤1)(x:Sky G ι):|f g x| ≤ c*(2/g)^n:=by
    induction H with
    | words w hw=> rw [one_mul]; exact sing_price x hg hu hw
    | add _ _ hp hq=> rw [add_mul]; exact (abs_add_le ..).trans (add_le_add hp hq)
    | scale a _ hp=> simp only [Pi.smul_apply,smul_eq_mul,abs_mul]; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hp (abs_nonneg _)
    | raise _ _ hx=> apply hx.trans; gcongr

lemma dollar_falls : Tendsto dollar atTop (𝓝 0):= Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
lemma willing [Fintype D](Y:Good X): ∀ᶠ s:ℝ in atTop, amen X (dollar s):= dollar_falls.eventually (gt_mem_nhds Y.thick.2.1)|>.mono fun i h=> ⟨(dollar_pos i).le,le_of_lt h⟩
lemma fare_falls : Tendsto Forge.fare atTop (𝓝 0):= (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).congr' (Eventually.of_forall fun _=> mul_comm ..)
lemma ruin_below (n:ℕ): ∀ᶠ s:ℝ in atTop, ruin s ≤ (dollar s)^n := by
    filter_upwards [eventually_ge_atTop (n:ℝ),eventually_ge_atTop (1:ℝ)] with x he hx; unfold ruin dollar; rw [←Real.exp_nat_mul,Real.exp_le_exp]; have hv:= mul_le_mul_of_nonneg_right he (zero_le_one.trans hx); nlinarith only [hv, show x^2 ≤ x^6 by gcongr; norm_num]

omit [Fintype ι] in
lemma dock {J:Finset ι}{p:Stuff G ι L}(hp:celery p J X.Q) {x :Sky G ι} {s:ℝ}(h:X.Q≤s^4)(he:crisp (fare s) J x):‖book p (dollar s) x‖ ≤ s^4:=by
    rw [pi_norm_le_iff_of_nonneg (by positivity : (0:ℝ)≤s^4)]; intro i; unfold book; rcases ht:p i with j|y <;> (have hh:=hp i; rw [ht] at hh)
    · change ‖_⁻¹ • G.curvature (x j)‖ ≤ _; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr (dollar_pos _)).le, inv_mul_le_iff₀ (dollar_pos _ )]; exact (G.curvature_norm _).trans ((he _ hh).le)
    exact (show ‖y‖ ≤ _ from hh).trans h

-- probe stamp anchored in a finite flat atom; `I` includes stencil AND all non-local checks kept
-- in real value identity for estimate, when all other arguments not assumed good!
structure Visible (X:Shelf G A D) (ψ:(L→G.Color)→ℝ)(f: Melody G ι)(p:Stuff G ι L)(N:ℕ)(c:ℝ):Prop where
     env g : amen X g→ Envelope (f g)
     price g : amen X g→∀x,|f g x| ≤ c
     stamp : ∃ J : Finset ι,J.card≤N ∧ celery p J X.Q ∧ ∀ g:ℝ, amen X g→ 0<g →∀ x: Sky G ι, crisp (X.δ/2) J x → f g x=ψ (g • book p g x)
namespace Visible
variable {ψ : (L→G.Color)→ℝ}{f : Melody G ι}{p: Stuff G ι L}{c g:ℝ}{N:ℕ}(H:Visible X ψ f p N c)
variable [Fintype k] [Fintype T] [Fintype D]
include H
omit [Fintype ι] in
lemma uses (Y:Good X)(j:ℕ): Offers j (presence ψ X.Q j) (tale p ψ j):= story (S:= _) H.stamp.choose_spec.2.1 _ Y.thick.1.le j
omit [Fintype ι] in
lemma dispenses (Y:Good X){g:ℝ}(hg:0<g)(he:g≤1)(x : Sky G ι) (j:ℕ): |g^j * tale p ψ j g x| ≤ presence ψ X.Q j*2^j:=by
   rw [abs_mul,abs_of_nonneg (by positivity : 0≤g^j)]
   exact (mul_le_mul_of_nonneg_left (height (H.uses Y j) hg he x) (by positivity : 0≤g^j)).trans_eq (by rw [div_pow]; field_simp)

def capΨ (ψ: (L→G.Color)→ℝ)(q:ℝ)(r:ℕ):=∑ j∈range r,presence ψ q j*2^j
omit [Fintype ι] in
lemma cash (Y:Good X){r:ℕ}(h:amen X g)(hg:0<g)(he:g≤1)(x:Sky G ι) : |f g x-untilB (fun j=>tale p ψ j g x) r g| ≤ c+capΨ ψ X.Q r:=by
   refine (abs_sub ..).trans ?_; apply add_le_add (H.price g h x) ?_; exact (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum fun i _=> H.dispenses Y hg he x i)
omit H [Fintype ι] [Fintype D] in lemma cap_nn (ψ:(L→G.Color)→ℝ)(q:ℝ)(r:ℕ)(h:0≤q):0≤capΨ ψ q r:=by unfold capΨ presence; positivity
end Visible
end YM.RGComparison.Core16.Lumen
