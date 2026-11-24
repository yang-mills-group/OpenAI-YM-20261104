import YM.Frontier6.Bouquet.Carnival.Emergence

/-!
# At the positive-regulator boundary

Defn locations outside sincerity assertions are simply totalizations of
 linear-evaluation inputs. No claims of linearity/convergence without support
 and clearance conditions. (On separated charts we'll also recover the readings
 from smaller local groups independently.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Garland
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains Prescription Metric Audit Submodule Fareway Atelier
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {I J L Y: Type}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable [NormedAddCommGroup Y][NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y][CompleteSpace Y]
variable (K:Final C F S)(d:Slot→ ℕ)(v:(j:Slot)→ S.Field (d j)){P Q:Ensemble}(x:Seats P)(H:Patron S P Y)(s a:ℝ)(f:Full (fiber P))
-- Beverin. Actual fixed-memory reader
abbrev Fly :Filter ℝ:=𝓝[>] (0:ℝ)
lemma fly_pos :∀ᶠ a:ℝ in Fly,0<a:= self_mem_nhdsWithin
instance fly_ne_bot: Fly.NeBot:= inferInstanceAs ((𝓝[>] (0:ℝ)).NeBot)
def bouquet (s:ℝ)(P:Ensemble) (x:Seats P)(H:Patron S P Y)(f:Full (fiber P)): Y:= limUnder Fly (fun a=>uKernel K d v s a P x H f)
def Greeted (s:ℝ)(P:Ensemble)(x: Seats P)(H:Patron S P Y)(f:Full (fiber P)):Prop:=Tendsto (fun a=>uKernel K d v s a P x H f) Fly (𝓝 (bouquet K d v s P x H f))
lemma Greeted.senses {y:Y}(h:Tendsto (fun a=>uKernel K d v s a P x H f) Fly (𝓝 y)) : Greeted K d v s P x H f ∧ bouquet K d v s P x H f=y:= ⟨(tendsto_nhds_limUnder ⟨_,h⟩), h.limUnder_eq⟩ -- target ▸
variable (M:Pod→ℝ)(R: Air (S:=S) P I L Y){B C' ε D:ℝ}{n:ℕ}
-- witnessed limits for all legitimate fixed-terrain dealings. Pass regulators
-- with explicit error to allow integrations.
lemma Air.respite (j:I): Tendsto (R.delta j) Fly (𝓝 0):=by
   let f(a:ℝ):=(a/R.route.floor j)^(1/4:ℝ); have hf:Continuous f:= by exact (continuous_id.div_const _).rpow_const fun _=> Or.inr (by norm_num) -- syntax
   have hh:f 0=0:= by unfold f; rw [zero_div, Real.zero_rpow (by norm_num: (1/4:ℝ)≠0)];
   exact hh ▸ hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
section
variable {M R K d v s a}
lemma costs_cauchy {Z:ℝ→ Y}{Q:ℝ→ℝ}(h:Tendsto Q Fly (𝓝 0))(hv:∀ a b:ℝ,0<a→a ≤ b→‖Z a-Z b‖≤Q b): Cauchy (map Z Fly):=by
   refine Metric.cauchy_iff.mpr ⟨inferInstance,fun ε hε=>?_⟩; let X:= {x:ℝ|0<x∧ Q x<ε}; have hx:X∈ Fly:= fly_pos.and (h.eventually (gt_mem_nhds hε)); refine ⟨Z '' X, image_mem_map hx,?_⟩; rintro u ⟨a,h,rfl⟩ v ⟨b,hh,rfl⟩; rw [dist_eq_norm]; rcases le_total a b with hh'|hh'; exact (hv _ _ h.1 hh').trans_lt hh.2; rw [norm_sub_rev]; exact (hv _ _ hh.1 hh').trans_lt h.2
variable (h:Endows K d v P M R n B C' ε D) {x:I}{f:Full (fiber P)} (hh:Length P M s)(ht:R.suitable x C' s){U:ℝ}(hf:Fellow P (R.lengths x) (R.region x) B f n U)
include h hh ht hf
lemma earns : Greeted K d v s P (R.region x).center (R.sky x) f:=by
    let W(a:ℝ):= D*U* R.freight d x ε* R.delta x a; have hw:Tendsto W Fly (𝓝 0):= by unfold W; simpa only [mul_zero] using ((Air.respite R x).const_mul (D*U*R.freight d x ε))
    exact tendsto_nhds_limUnder (cauchy_iff_exists_le_nhds.mp (costs_cauchy hw fun a b ha hb=> h.paired ha hb hh ht hf)) -- inference map
lemma earned : ‖bouquet K d v s P (R.region x).center (R.sky x) f‖≤ D* U*R.freight d x ε:= le_of_tendsto (earns h hh ht hf).norm (fly_pos.mono (fun j hj=> h.unit hj hh ht hf))
lemma refunded (ha:0<a): ‖bouquet K d v s P (R.region x).center (R.sky x) f-launch K d v (R.region x) (R.sky x) s a f‖≤ D*U*R.freight d x ε*R.delta x a:=by
   refine le_of_tendsto (((show Greeted .. from earns h hh ht hf).sub (tendsto_const_nhds (x:= launch K d v (R.region x) (R.sky x) s a f))).norm) (?_); exact (fly_pos.and (show ∀ᶠ b in Fly,b≤a from mem_nhdsWithin_of_mem_nhds (ge_mem_nhds ha))).mono fun j hj=>h.paired hj.1 hj.2 hh ht hf
end
-- Estimate toll is affordable even for unnormalized f. Could use compact support.
lemma book {M:Pod→ℝ}(he:Dais K d P M)(hh:R.Welkin M)(x:I)(hf:Fair f (R.region x).foot (R.region x).center){a:ℝ}(ha:1 ≤ a*R.route.floor x) : lodge P (R.lengths x) f a := by
    intro i y hy; have hb:0<a:=pos_of_mul_pos_left (zero_lt_one.trans_le ha) (R.route.footing x|>.le)
    exact mem_closedBall_zero_iff.mpr (show ‖rune i y‖ ≤ a * _ from (pricesR i y (hh.safe x) f hf hy).trans ((he.zenith _ (stage_in i.property)).trans (ha.trans (mul_le_mul_of_nonneg_left (R.route.covered .. |>.1) hb.le))))
section
variable {K d v s} {M:Pod→ℝ} (he:Dais K d P M)(hw:R.Welkin M){x:I}{f:Full (fiber P)}
variable (hf: Fair f (R.region x).foot (R.region x).center)
include he hw hf
lemma staged (j:ℕ){b:ℝ}(hf':Charge j 1 f b): Fellow P (R.lengths x) (R.region x) ((R.route.floor x)⁻¹) f j b:= ⟨hf,book K d f R he hw x hf (inv_mul_cancel₀ (R.route.footing _).ne'|>.ge),charges_path f j zero_le_one hf' (fun y hy=> paths_cost _ _ (R.length_cap _) hy)⟩
lemma funded (n:ℕ){s:ℝ}(hh:Length P M s) : ∃ B C A: ℝ,1 ≤ B∧1 ≤ C∧R.suitable x C s ∧ Fellow P (R.lengths x) (R.region x) B f n A:=by
    obtain ⟨P,h⟩:= exists_charge n f 1 zero_le_one; let c:=max 1 (1/s); refine ⟨ _,c,P,?_,le_max_left ..,fun j=>?_,staged R he hw hf n h⟩
    · rw [← one_div]; exact (one_le_div (R.route.footing _)).mpr (R.route.ground _|>.2)
    apply (R.length_cap x j).trans; exact (((div_le_iff₀ hh.pos).mp (le_max_right 1 (1/s)))) -- check
lemma certifies (v:(j:Slot)→ S.Field (d j))(hp: Air.Hosts K R) (hl:Length P M s):Greeted K d v s P (R.region x).center (R.sky x) f:= by
    obtain ⟨n,h⟩:= sails K d v P; obtain ⟨b,c,w,hb,hc,H,hL⟩:= funded R he hw hf n hl; exact earns (h he hw hp b c 1 hb hc zero_lt_one).choose_spec hl H hL
end
end YM.Frontier6.Bouquet.Garland
