import YM.Frontier6.Bouquet.Market.Ride

/-! Apertures for projection at the parent. For a projected leg, use bigger
 Ball (test T^s may go all the way there), operation reports inside the
 original aperture. Rejection stays in the original. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Atelier
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains Prescription Metric Audit Submodule Fareway
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {I L Y: Type}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable [NormedAddCommGroup Y][NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y]
variable {P Q:Ensemble}{d:Slot →ℕ} (K:Final C F S) (i:P) (A:Aura P) (H: Patron S P Y) (M:Pod→ℝ)
abbrev Part (d:Slot→ℕ)(i:P):= Option (i.val.Horizon d)
variable (p:Part d i)
def shift (p:Part d i)(A:Aura P) (M:Pod→ℝ) : Aura P:= match p with
 | none=> A
 | some _=> ⟨A.center, update A.foot i (closedBall (A.center i) (M i.val))⟩
lemma shifts : (shift i p A M).center=A.center:= by cases p <;> rfl
lemma shifted_unchanged {j:P}(h:j≠i): (shift i p A M).foot j = A.foot j:= by cases p;simp [shift]; unfold shift; apply update_of_ne h
variable {M A}
lemma shifting (h:A.Cozy M): A.foot ≤ (shift i p A M).foot:= fun j=>by
    by_cases hv:j=i; swap; rw [shifted_unchanged i A M p hv]
    subst j; cases p; exact le_rfl; unfold shift; dsimp only; rw [update_self]; intro x hx; rw [mem_closedBall,dist_eq_norm]; exact h.prices _ _ hx
lemma shift_cozy (h:A.Cozy M) : Aura.Cozy (shift i p A M) M:= by
    refine ⟨fun j=>?_,fun j=>?_,fun j z hz=> ?_⟩
    · rw [shifts]; exact shifting i p h j (h.around j)
    · by_cases hv:j=i; swap; rw [shifted_unchanged i A M p hv]; exact h.solid j
      subst j; cases p; exact h.solid _; unfold shift; dsimp only; rw [update_self]; exact convex_closedBall ..
    by_cases hv:j=i; swap; rw [shifted_unchanged i A M p _] at hz; rw [shifts]; exact h.prices _ _ hz; exact hv
    subst j; cases p; exact h.prices _ _ hz; unfold shift at hz ⊢; simpa only [update_self, mem_closedBall, dist_eq_norm] using hz
-- transaction
variable (A M)
def movedBy (p:Part d i)(x:E4): Spelling S→ₗ[ℂ] Spelling S:= match p with
 | none=> advance K x (i.val.horizon d)
 | some w=> stagePart K x w
-- called with x=A.center; supplies on shift i p
abbrev moves (x:Seats P) : Patron S P Y := transaction H i (movedBy K i p (x i))
def demands (s:ℝ)(p:Part d i)(f:Full (fiber P)): Full (fiber P):= match p with
 | none=> f
 | some w=> overBook i d s w f
section
variable {H M A K}
variable (hC:Dais K d P M)(hc:A.Cozy M)
include hC hc
lemma appear_projection {w:i.val.Horizon d} [TopologicalSpace I]{x:I}{V:Art S I}(he: Appears ((shift i p A M).foot i) x V): Appears (A.foot i) x (fun k=> stagePart K (A.center i) w (V k)):=by
    let a:=A.center i; refine Appears.suit K continuousAt_const (hc.around _) ((weight K w).continuous.continuousAt.comp (Appears.purchased K w he (y:=fun _=>a) (r:= 2*M i.val) ?_ continuousAt_const ((hC.safe i.val (stage_in i.property)).down K w.isLt.le le_rfl)))
    intro z hz; apply lt_of_le_of_lt ?_ (show M i.val < 2*M i.val from by linarith only [hC.pos _ (stage_in i.property)]); unfold a; rw [←shifts i A M p]; exact (shift_cozy i p hc).prices _ _ hz -- param order?
lemma appear_moves {X:Type} [TopologicalSpace X]{x:X}{V:Art S X}(he:Appears ((shift i p A M).foot i) x V): Appears (A.foot i) x (fun k=> movedBy K i p (A.center i) (V k)):=by
   cases p; swap; exact appear_projection i _ hC hc he; -- none
   unfold movedBy; simp_rw [advance_value]; exact he.pays (Appears.sum Finset.univ (fun j _=> appear_projection i none hC hc he))
lemma unflag (he:Gentle H A.foot) : Gentle (moves K i H p A.center) (shift i p A M).foot:=by
    apply he.modify; intro j I _ x v hV; by_cases hh:j=i; · subst j; rw [if_pos rfl]; exact appear_moves i p hC hc hV
    rw [if_neg hh]; rw [shifted_unchanged i A M p hh] at hV; exact hV
omit hC
variable {f:Full (fiber P)}{s:ℝ}
lemma page_escort (h: Length P M s)(he: Fair f A.foot A.center)(w:i.val.Horizon d) : Fair (atBook i d s w f) (shift i (some w) A M).foot A.center:=by
   intro x hx j b hb; obtain ⟨hy,hz⟩ := sky_support (home_sub i.property) f s _ h.pos hx; by_cases hv:j=i; swap; rw [shifted_unchanged i A M _ hv]; unfold actual; rw [← coordinate_unchanged i x hv b hb]; exact he _ hz j b hb
   subst j; unfold shift; dsimp only; rw [update_self,mem_closedBall, dist_eq_norm,actual,add_sub_cancel_right,begins i x b hb]; exact (norm_house b (rune i x).val).trans ((mem_closedBall_zero_iff.mp hy).trans (h.top i.val (stage_in i.property))) -- hy membership
lemma escort (hs:Length P M s)(he:Fair f A.foot A.center) : Fair (demands i s p f) (shift i p A M).foot A.center:=by
    cases p with
    | none=> exact he
    | some w => intro x hx; rcases tsupport_sub (f:fiber P→ℂ) (atBook i d s w f) hx with hi|hi; exacts [he.broad (shifting i _ hc) x hi,page_escort i hc hs he w x hi]
include hC
lemma auditions (h:Length P M s)(he: Fair f A.foot A.center)(hw:Gentle H A.foot): Partakes K d i s A.center H f:= ⟨⟨_,hw,he⟩, ⟨_,unflag i none hC hc hw,he⟩,(fun w=>⟨_,unflag i (some w) hC hc hw,he.broad (shifting i _ hc)⟩),(fun w=> ⟨_,unflag i (some w) hC hc hw,page_escort i hc h he w⟩)⟩ -- P Universe
end
end YM.Frontier6.Bouquet.Atelier
