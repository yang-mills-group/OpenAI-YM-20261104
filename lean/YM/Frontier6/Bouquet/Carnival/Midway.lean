import YM.Frontier6.Bouquet.Carnival.Trophy

/-! UV-root regularizer vanishes on the ending of the sector telescope. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Atelier
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains Prescription Metric Audit Submodule Fareway
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {I J L Y: Type}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable [NormedAddCommGroup Y][NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y][CompleteSpace Y]
variable (K:Final C F S){P Q:Ensemble}{d:Slot →ℕ}(i:P)(H: Patron S P Y)(x: Seats P)(A:Teller S) (T:Veins)
variable (f:Full (fiber P))(g:Full (normal i.val)) {r:ℝ}
def beyond (i:P)(g:Full (fiber P)):Prop :=∀ x∈tsupport g,rune i x≠0
lemma Flare.beyond (he: Flare i f r)(h:0<r): beyond i f:=fun x hx hz=>by have he' : r/2≤ ‖rune i x‖:= (he (show x∈tsupport f from hx)).1; rw [hz,norm_zero] at he'; linarith
lemma alone_cut (he: beyond i f): regulator K A T x H f=pollen K A T i x H f:=by
   rw [splitting K A T i, show marble K A T i x H f=0 from ?_,add_zero]; unfold marble select; refine Finset.sum_eq_zero (fun q hq=>?_); have hz:i.val∈ q.val.choose:= (Finset.mem_filter.mp hq).2; unfold branch; refine Finset.sum_eq_zero (fun u hu=>?_); unfold essay; rw [show (fun z:Margin P q.val=> ink K A T q.property x H u f z)=fun _=>0 from funext fun z=>?_]; exacts [integral_zero _ _, ink_absent K A T _ _ _ (fun hx=>he _ hx (on_blank (orthogonal_le (home_sub hz) (loft_orth z.property))))]
lemma gap_in (he:tsupport f⊆ cylindrical _ _ (Metric.ball (0:normal i.val) (T.range i.val))): pollen K A T i x H f=0:=by
   unfold pollen select; refine Finset.sum_eq_zero (fun q hq=>?_); have hz:i.val∈ scars P q.val:=by apply Finset.mem_sdiff.mpr; refine ⟨stage_in i.property, fun h=>?_⟩; obtain ⟨p,hp,hv⟩:= encloses.mp h; exact (Finset.mem_filter.mp hq).2 ((le_antisymm hv (not_cross q.property hp i.property (hv i.val.here_mem) i.val.here_mem)) ▸ hp)
   unfold branch; refine Finset.sum_eq_zero (fun u hu=>?_); unfold essay ink; rw [show T.film P q.val f=0 from ?_] -- ink contains, might fail
   · simp
   ext1 y; apply image_eq_zero_of_notMem_tsupport; intro hx; exact ((mem_ball_zero_iff.mp (he (T.film_support _ _ _ hx)))).not_ge (T.cutter_tale hz (T.film_support' _ f hx))

abbrev slalom (i:P)(g: Full (normal i.val)) := paneM (Q:=fiber P) g g.contDiff
lemma slaloms : tsupport (slalom i g f)⊆tsupport f:= screen_subset ..
lemma slalom_fell : tsupport (slalom i g f) ⊆ cylindrical _ _ (tsupport g):= tsupport_mul_subset_left.trans (tsupport_comp_subset_preimage (f:=rune i) g (rune i).continuous)

abbrev gizmo (r:ℝ): Full (fiber P) →ₗ[ℂ] Full (fiber P):= slalom i (Normal.strip _ r)
lemma gizmo_flare (h:0<r): Flare i (gizmo i r f) r:= (slalom_fell i f _).trans (Set.preimage_mono (Normal.strip_ring h)) -- name
lemma midway (n:ℕ): gizmo i (Normal.pitch n) f= slalom i (Normal.shrink _ (Normal.pitch n)) f-slalom i (Normal.shrink _ (Normal.pitch (n+1))) f:=by
   ext1 y; rw [pitch_even]; change (_ - _)*f y=_*_ - _*_; exact sub_mul ..
abbrev uphold (i:P)(f:Full (fiber P)) : Prop:= tsupport f ⊆ cylindrical _ _ (Metric.closedBall (0:normal i.val) 1)
lemma holds_mid (he:uphold i f):slalom i (Normal.shrink _ (Normal.pitch 0)) f=f:=by
   ext1 a; let r:= rune i a; change Normal.shrink (normal i.val) (Normal.pitch 0) r*f a= f a; by_cases h:a∈tsupport f; · rw [shrink_home (pitches _) r (by simpa only [Normal.pitch,pow_zero,r,rune] using mem_closedBall_zero_iff.mp (he h)),one_mul]; -- defeq
   rw [image_eq_zero_of_notMem_tsupport h,mul_zero]
lemma attends (hh:Welcomes H x f)(he:uphold i f):
    pollen K A T i x H f=∑' n:ℕ,regulator K A T x H (gizmo i (Normal.pitch n) f):=by
   obtain ⟨U,hU,h⟩:= hh; let f'(g:Full (normal i.val)):= slalom i g f; let F(g:Full (fiber P)):= pollen K A T i x H g; let Z(n:ℕ):= slalom i (Normal.shrink _ (Normal.pitch n)) f
   have hA (g:Full (normal i.val)): Appointed K A T x H (f' g):= Welcomes.appointed K A T x H _ ⟨U,hU,h.narrower (slaloms ..)⟩
   have ht(n:ℕ): regulator K A T x H (gizmo i (Normal.pitch n) f)= F (Z n)-F (Z (n+1)):=by
       rw [alone_cut K i H x A T _ (Flare.beyond i _ (gizmo_flare i f (pitches n)) (pitches n)),midway]; exact select_subtract K A T x H _ (proper P i.val) _ (hA _) (hA _)
   have he':∀ᶠ n:ℕ in atTop,F (Z n)=0:=by
       filter_upwards [pitch_down.eventually (gt_mem_nhds (half_pos (T.pos i.val)))] with n hn -- gt or ge
       refine gap_in K i H x A T _ (subset_trans (slalom_fell i f (Normal.shrink _ (Normal.pitch n))) (?_)); exact Set.preimage_mono ((shrink_fits (pitches n)).trans (Metric.closedBall_subset_ball (by linarith)))
   obtain ⟨N,hN⟩:= eventually_atTop.mp he'; rw [tsum_congr ((show ∀ n:ℕ, _ from ht)),tsum_eq_sum (s:=Finset.range N) (_), Finset.sum_range_sub', hN N le_rfl,sub_zero] -- lemma? goal
   · rw [show Z 0=f from holds_mid i f he]
   intro n hn; have he : N ≤ n:=by simpa using hn
   rw [hN n he,hN _ (by omega),sub_zero]
end YM.Frontier6.Bouquet.Atelier
