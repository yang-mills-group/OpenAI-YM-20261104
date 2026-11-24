import YM.FVA2.Broadcast

/-!
# Open orders across all layers

Full `course` consistent under order restrictions of *whole clock* and all
field and tag monomials (not changing S/G/fabric).
Also expose early weight `chip`: actual signed exponent with entire ratio
price w. Optional way to wire step entities. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Bk
open Filter Topology Function Finset MeasureTheory FormalOPE.RG10
open FormalOPE.RG10.MarkovChain OpenSlots
open PertExtension Precision Inherit Push.Loops PertExtension.Chart Lattice RG
    PertExtension.GaussianScore PowerSeries
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric
    Papers Warp Line Roof Router Quadratic
open scoped Classical Topology ContDiff BigOperators InnerProductSpace
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable {G:Gauge} {c f:Side} {w v:PowerSeries ℝ} {r:ℕ}

lemma through_at {A B:Ticket E}(he:Through r A B)(f:F→ₗ[ℝ] E): Through r (boost f A) (boost f B):= fun i hi=> by simp [boost,he _ hi]

variable [FiniteDimensional ℝ E] {p:E→ℝ} (he:Radial.Stationary p)
include he
lemma base_rise : Stack.rise p=X^2 * Stack.drop 2 (Stack.rise p):= by
   apply (recover ..).symm; intro i hi; unfold Stack.rise; rw [coeff_mk]; apply Subtype.ext; ext1 x; interval_cases i; exact (jet_zero ..).trans he.base0; exact he.base1 x
lemma stack_delta : Stack.drop 1 (Stack.rise p) = X * Stack.drop 2 (Stack.rise p):= by
   nth_rw 1 [base_rise he]; rw [pow_succ', pow_one, mul_assoc,← pow_one X, Stack.drop_mul, pow_one] -- rewrite nested

lemma through_w (h:Through r w v) : Through r (chip w p) (chip v p):= by
   apply Sync.exp_tracks; unfold OpenSlots.pay; rw [show term w 0=term v 0 from h 0 (Nat.zero_le _)]; refine (Through.refl _).add ?_
   rw [stack_delta he]; simp_rw [← mul_assoc]; apply Through.mul _ (Through.refl _);
   intro i hi; rw [mul_comm (carry _) X,mul_comm (carry _) X,←pow_one X,coeff_X_pow_mul',coeff_X_pow_mul']; split; swap; · rfl
   have h': 1+(i-1)=i:=by omega
   simp only [carry,PowerSeries.coeff_map, Tracks.shadow,Tracks.deduct,map_neg,coeff_mk,h']; rw [show term w i=term v i from h i hi]

-- exposes exponent sign; coarse square price *not* counted in ray polynomial (caller of Update handles it)
lemma tally_w (w:PowerSeries ℝ): pay w p -(roll (term w 0))* PowerSeries.C (coeff 2 (Stack.rise p))= -carry w * Stack.drop 2 (Stack.rise p):= by
   have hx : carry (Tracks.shadow w) * X = -(carry (E:=E) w) + roll (term w 0):= by
      change PowerSeries.map _ _ * X= _; rw [mul_comm _ X,←pow_one X]; apply PowerSeries.ext; intro i; rw [coeff_X_pow_mul',map_add,map_neg]; by_cases hu:i=0; · subst i; simp [Stack.roll,carry,term]
      have he' :1+(i-1)=i:=by omega
      simp only [if_pos (show 1 ≤ i from by omega),carry,Tracks.shadow,Tracks.deduct,roll,PowerSeries.coeff_map,map_neg,coeff_mk,coeff_C,if_neg hu,add_zero,he']; rfl
   rw [pay,stack_delta he, ← mul_assoc (carry _), hx];
   unfold advancing; rw [show Stack.drop 2 (-rise p)=-Stack.drop 2 (Stack.rise p) from PowerSeries.ext fun i=> by simp [Stack.drop]]; ring

section course
variable {S:StepData c f} {C : Fabric G c} {P:Inside S.ratio}
variable {t:S.Choices} {J:ChartRatio G} (hJ:LocalRatio J)

structure Mature (i:ℕ)(U V:Unmasked G f):Prop where
   rk: U.Q=V.Q
   weigh: Through i U.W V.W

omit he
lemma comparable (h:Through r w v): Mature (G:=G) (f:=f) r (initialFull G f w) (initialFull G f v):= by
   refine ⟨?_, through_w first_held h⟩; change (genesis w _)=genesis v _; unfold Quadratic.genesis; simp_rw [show term w 0=term v 0 from h 0 (Nat.zero_le _)]
lemma maturity0 {U V: Unmasked G f}(h:Mature r U V) (h': Through r w v): gated P U t w=gated P V t v:= by
   unfold gated genesis; simp_rw [h.rk,show term w 0=term v 0 from h' _ (Nat.zero_le _)]
lemma payee (H:S.patch.Branches S.kernel G) {U V:Unmasked G f}(h:Mature r U V)(h': Through r w v) : Through r (receipt P t J w U) (receipt P t J v V):=Through.mul ((through_at h.weigh (blankRight P)).mul (Through.refl _)) (through_w (subStill _ _ H) h')
lemma drag_update (H:S.patch.Branches S.kernel G){U V:Unmasked G f}(h:Mature r U V)(h':Through r w v)(b:(Quadratic.core (gated P U t w)).RespectsPrice)(p':(Quadratic.core (gated P V t v)).RespectsPrice) : Mature r (Update P t J w U b) (Update P t J v V p'):= by
   obtain hY:=payee (P:=P) (t:=t) (J:=J) H h h';
   obtain hH:= maturity0 (P:=P) (t:=t) h h'; unfold Update; generalize hk: gated P U t w=P₀, he: gated P V t v=P₁ at *; clear he; subst P₁; exact ⟨rfl, keepsThrough _ hY⟩

include hJ
lemma sent_out (H:S.patch.Branches S.kernel G) {U V:Unmasked G f}(h:Mature r U V)(h': Through r w v)(hx:incline U.W)(hy:incline V.W)(b:(core (gated P U t w)).RespectsPrice)(b':(core (gated P V t v)).RespectsPrice){A B:Ticket (Cross (G:=G) S P × Flats G c)}(ht:Through r A B) :
   Through r (Broadcast P t J w U b A) (Broadcast P t J v V b' B) := by
   unfold Broadcast; obtain h₁:=show incline (receipt P t J w U) from OpenSlots.along hJ w hx; obtain h₂:= show incline (receipt P t J v V) from OpenSlots.along hJ v hy;
   obtain hT:= payee (P:=P) (t:=t) (J:=J) H h h'; obtain hu:= maturity0 (P:=P) (t:=t) h h'; generalize hk: gated P U t w=P₀, he: gated P V t v=P₁ at *; clear he; subst P₁
   exact Through.mul (keepsThrough _ (hT.mul ht)) (Through.invAlready (keepsThrough _ hT) (spend_it (Quadratic.upright P₀ (tangent G (Blocking.Index S P)) b h₁)) (spend_it (Quadratic.upright P₀ (tangent G (Blocking.Index S P)) b' h₂)))
lemma passage {n:Side}{Z:Fabric G n}{w v:Z.Cost→PowerSeries ℝ} (L:Cloth Z) (U V:Unmasked G n)(R:Commission J L U w)(Q:Commission J L V v)
    (x:incline U.W)(y:incline V.W)(h:Mature (f:=n) r U V)(h':∀ i,Through r (w i) (v i)){A B:Ticket (Flats G n)}(p:Through r A B) : Through r (course L w U J A R) (course L v V J B Q):=by
  cases L with
  | floor k b Y'=>
     rw [course,course];
     let F:= Cloth.floor _ b Y'; let K:=castAt F
     let P₁ := (show (drag _ U.Q).RespectsPrice from (show (drag K U.Q).RespectsPrice from R)).inner
     let P₂ := (show (drag _ V.Q).RespectsPrice from (show (drag K V.Q).RespectsPrice from Q)).inner
     have hP:P₁=P₂:= by unfold P₁ P₂; congr 1; exact congr_arg _ h.rk
     change Through r (enjoy P₁ _ (boost K A) _) (enjoy P₂ _ (boost K B) _); rw [hP];
     have hh:=Through.mul (through_at h.weigh K) (Through.refl (tissue J F.choose.Bulk)); apply Through.mul _ (Through.invAlready (keepsThrough _ hh) (PowerSeries.mul_inv_cancel _ ?_) (PowerSeries.mul_inv_cancel _ ?_));
     · exact keepsThrough _ (hh.mul (through_at p K))
     · change constantCoeff (input P₂ _ _)≠0; rw [underBudget P₂ (tangent G _) (pool (preserve_boost K x) (awake hJ))]; exact one_ne_zero
     change constantCoeff (input P₂ _ _)≠0; rw [underBudget P₂ (tangent G _) (pool (preserve_boost K y) (awake hJ))]; exact one_ne_zero
  | @inLayer c f S H t hf Z P C=>
     rw [course,course];
     let b:= Exists.choose (show (Commission J (.inLayer P C) U w) from R); let b':=Exists.choose (show Commission J (.inLayer P C) V v from Q);
     refine passage  C (Update P t J (w none) U b) (Update P t J (v none) V b') _ _ (funded hJ _ x _) (funded hJ _ y _) (drag_update H h (h' none) _ _) (fun i=>h' (some i)) ?_;
     exact sent_out hJ H h (h' none) x y _ _ (through_at p _)
termination_by structural L
end course
end YM.FVA2.Bk
