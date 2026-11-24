import YM.Frontier6.Bouquet.Carnival.Tempo

/-! The nonzero programs all book at shared memory s. No limit or pointwise
 positivity invoked. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Atelier
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains Prescription Metric Audit Submodule Fareway
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {I J L Y: Type}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable [NormedAddCommGroup Y][NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y][CompleteSpace Y]
variable (K:Final C F S){P Q:Ensemble}{d:Slot →ℕ}(i:P) (M:Pod→ℝ) (p:Part d i) (R: Air (S:=S) P I L Y)(B C':ℝ)
variable {x:P→ℝ}{f:Full (fiber P)}
section
variable {r s:ℝ} {B C'} (he: Length P M s)
lemma sprinkles (hr:0<r): Flare i (supplements i p s r f) r:=by rw [supplement]; exact gizmo_flare i _ hr -- implicit hr??
lemma fellows_support (hs:0<s)(hf:lodge P x f B){j:P}(h:j≠i):tsupport (demands i s p f) ⊆ cylindrical _ _ (Metric.closedBall (0:normal j.val) (B*x j)):=by
   cases p; exact hf j; rename_i w; intro y hy; rcases tsupport_sub f (atBook i d s w f) hy with ht|ht; · exact hf j ht
   obtain ⟨hz,hx⟩:= sky_support (home_sub i.property) f s (i.val.track d w) hs ht; change rune j y ∈ Metric.closedBall (0:normal j.val) (B*x j); exact centerless_unchanged i y h ▸ (show rune j (centerless (home_sub i.property) y)∈ Metric.closedBall _ _ from hf j hx) -- matches target?
lemma fellow_local (hs:0<s)(hr:0<r)(hf:lodge P x f B)(ht:∀ i,0<x i): lodge P (update x i r) (supplements i p s r f) (max B 2):=by
   intro j y hy; by_cases hp:j=i; · subst j; rw [update_self]; change rune i y∈ Metric.closedBall (0:normal i.val) (max B 2*r); exact mem_closedBall_zero_iff.mpr ((show ‖rune i y‖≤2*r from (sprinkles i p hr hy).2).trans (mul_le_mul_of_nonneg_right (le_max_right ..) hr.le))
   rw [update_of_ne hp]; rw [supplement] at hy; change rune j y ∈ Metric.closedBall (0:normal j.val) (max B 2*x j); have hh:y∈tsupport (demands i s p f):= slaloms i _ _ hy; have he:rune j y∈ Metric.closedBall (0:normal j.val) (B*x j):= fellows_support i p hs hf hp hh; exact Metric.closedBall_subset_closedBall (mul_le_mul_of_nonneg_right (le_max_left ..) (ht j).le) he -- .. syntax?
lemma fellow_fair {X: Aura P} (he: Length P M s)(hx:X.Cozy M)(hr:0<r)(hf:Fair f X.foot X.center): Fair (supplements i p s r f) (ruffle i (shift i p X M) r).foot X.center := by
   intro y hy j a ha; have ht: Flare i _ r:= sprinkles i p hr (f:=f) (s:=s); have hh: r/2 ≤ ‖rune i y‖ ∧ ‖rune i y‖ ≤ 2*r:= ht hy; rw [supplement] at hy; have hv:= escort i p hx he hf _ (slaloms i _ _ hy) j a ha; by_cases H:j=i; swap; rw [ruffles i _ H]; exact hv
   subst j; rw [ruffled,shifts]; refine ⟨hv,?_⟩; rw [mem_closedBall,dist_eq_norm,actual,add_sub_cancel_right,begins i y a ha]; exact (norm_house a _).trans hh.2
end
set_option quotPrecheck false
local notation "🌈" => landscape K i M p R B
lemma teams (he: R.Welkin M)(n:ℕ)(hB:1≤B)(hC:1 ≤ C'):∃ D:ℝ,0 ≤ D∧∀ (z:Swing i p R B)(f:Full (fiber P))(s A:ℝ), Length P M s→ R.suitable z.here C' s→ Fellow P (R.lengths z.here) (R.region z.here) B f (n+toil i p n) A→Fellow P ((🌈).lengths z) ((🌈).region z) (max B 2) (supplements i p s z.radius f) n (D*A*Tempo i p (z.radius/R.lengths z.here i)):=by
   obtain ⟨E,hE,h⟩:= spread_cost i p n B C' hB hC; refine ⟨E,hE,fun z f s A hl ht hh=>?_⟩; rw [techno]; refine ⟨?_,fellow_local i p hl.pos z.pos hh.local_ (R.length_pos _), h _ f s z.radius A hl.pos z.pos (R.length_pos ..) (ht i) (hh.local_ i) hh.costs⟩; rw [land_center K i M p]; exact fellow_fair i M p hl (he.safe _) z.pos hh.fair -- args inspect
-- active tests
abbrev widened (B C:ℝ) : ℝ:= max C (max (2*B*C) 4)
lemma accepted (f:Full (fiber P)){t r:ℝ}(x:I)(hB:1≤B) (hs:0<t)(hr:0<r)(ht:r ≤1)(h:R.suitable x C' t)(he:lodge P (R.lengths x) f B)(hy:supplements i p t r f≠0): ∃ z:Swing i p R B,z.here=x∧z.radius=r∧ (🌈).suitable z (widened B C') t:=by
   rw [supplement] at hy; let F':= gizmo i r (demands i t p f); obtain ⟨y,hz⟩: (tsupport F').Nonempty:= Set.nonempty_iff_ne_empty.mpr (fun hp=> hy (TestFunction.ext (fun z=> congr_fun (tsupport_eq_empty_iff.mp hp) z))); have he': r/2 ≤ ‖rune i y‖:= (gizmo_flare i _ hr hz).1; have hh:y∈ tsupport (demands i t p f):= slaloms _ _ _ hz; have hx':y∈tsupport f→ r≤ 2*B*(R.lengths x i):= fun hp=> by linarith only [he', (show ‖rune i y‖ ≤ B*R.lengths x i from mem_closedBall_zero_iff.mp (he i hp))];
   have hw:r≤ widened B C'* t:=by
       have hw: y∈ tsupport f ∨ ‖rune i y‖≤2*t:=by
         cases p <;> clear hz hy
         · exact Or.inl hh
         rename_i w; rcases tsupport_sub f (atBook i d t w f) hh with ha|ha; exacts [Or.inl ha,Or.inr (mem_closedBall_zero_iff.mp ((sky_support (home_sub i.property) f t _ hs ha).1))]
       rcases hw with hh'|hh'
       · refine (hx' hh').trans ((mul_le_mul_of_nonneg_left (h i) (mul_nonneg zero_le_two (zero_le_one.trans hB))).trans ?_); rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right ((le_max_left ..).trans (le_max_right ..)) hs.le
       apply le_trans (b:= (4:ℝ)*t) ?_ (mul_le_mul_of_nonneg_right ((le_max_right ..).trans (le_max_right ..)) hs.le); linarith
   let z : Swing i p R B:= ⟨x,r,hr,ht,fun hp=>by subst p; exact hx' hh⟩; refine ⟨z,rfl,rfl,fun j=>?_⟩; rw [techno]; by_cases h':j=i; subst j; rw [Function.update_self]; exact hw; rw [Function.update_of_ne h']; exact (h j).trans (mul_le_mul_of_nonneg_right (le_max_left ..) hs.le)
end YM.Frontier6.Bouquet.Atelier
