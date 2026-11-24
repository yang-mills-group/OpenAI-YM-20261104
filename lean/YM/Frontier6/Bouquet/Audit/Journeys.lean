import YM.Frontier6.Bouquet.Audit.Heritage

/-! All fronts, all refinements. Including preserving the diameter budgets.
 Compared lengths for valuation.An availability group may be considered alone. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Audit
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains Prescription Metric Fareway Submodule Atelier
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {I L J X:Type}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}{K:Final C F S}
variable {Y:Type}[NormedAddCommGroup Y][NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y]
variable {P Q:Ensemble} (R:Air (S:=S) P I L Y)(h:Q≤P)(f:J→ I)(B:J→ Aura Q)
-- unchanged group centroids over ALL support transfers
lemma literally (x:Seats P)(z:Margin P Q) (q:Q)(he:q.val=(assign h q).val): transit h x z q=x (assign h q):=by
    unfold transit; rw [he]; exact (congr_arg (· + x (assign h q)) (centroid_empty (assign h q) ((insideCL loft_le z):fiber P))).trans (zero_add _)
lemma width_smaller (u:fiber P)(v:fiber Q)(y:Margin P Q)(hy:u=forward (plan_sub h) (insideCL loft_le y) v)(q:Q): ‖rune q v‖≤ ‖rune (assign h q) u‖:=by
    let a:= assign h q; have hx:ontoSpace (normal q.val) (rune a u).val=rune q v:=by
        rw [show ontoSpace (normal q.val) (rune a u).val=ontoSpace (normal q.val) u.val from (on_lower (normal_sub (inside h q)) u.val).symm,hy,forward_cast,map_add]; have ht:y.val∈ (normal q.val)ᗮ:= orthogonal_le (home_sub q.property) (loft_orth y.property); change ontoSpace _ y.val + _= _; rw [on_blank ht,zero_add]; rfl
    rw [← hx]; exact on_budget (P:=normal q.val)
lemma relaxed (x:Margin P Q)(f:Full (fiber P)){B:ℝ}{r:P→ℝ}(he:lodge P r f B): lodge Q (r ∘ assign h) (restrictS (plan_sub h) (insideCL loft_le x) f) B:=by
   intro i y hy; refine (mem_closedBall_zero_iff.mpr (show ‖rune i y‖≤ _ from (width_smaller h _ y x rfl i).trans ((mem_closedBall_zero_iff.mp (he (assign h i) (restrict_support _ _ f hy))))))
section
variable {M:Pod→ℝ}{u:ℝ}{d:Slot→ℕ}
lemma Aura.cozy_move {A:Aura P}(z:Margin P Q)(he:Dais K d P M)(ht:A.Cozy M){B: Balcony Q}(he':B≤ A.foot ∘ assign h)(hh:∀ q:Q, Convex ℝ (B q))(hz:∀ q,transit h A.center z q∈ B q): Aura.Cozy ⟨transit h A.center z,B⟩ M:=by
    constructor; exact hz; exact hh; intro i v hv
    let u:= assign h i; let y:= A.center u; let x:=transit h A.center z; change ‖v-x i‖≤ _; have hB:‖v-y‖ ≤ M u.val:= ht.prices u _ (he' _ hv)
    rcases (inside h i).eq_or_lt with hQ|hQ; · rw [show x i=y from literally h _ _ _ hQ,hQ]; exact hB
    calc
        _ ≤ ‖v-y‖ + ‖x i-y‖:= by rw [← dist_eq_norm,← dist_eq_norm,←dist_eq_norm, dist_comm (x i) y]; exact dist_triangle .. 
        _ ≤ _:= (add_le_add hB (ht.prices u _ (he' _ (hz i)))).trans ((two_mul _).symm.trans_le (he.swell _ (stage_in u.property) i.val hQ))
-- general Welkin
lemma heir_welkin (hx:R.Welkin M) (hc:∀ i:J,(B i).foot ≤ (R.region (f i)).foot ∘ assign h)(hy:∀ i,(B i).Cozy M) (hp:∀ i:J,∀ p:P,((dialogues h p:Set Q)).PairwiseDisjoint (B i).foot): Air.Welkin (heir R h f B) M:= ⟨hy,fun i=> Gentle.refines (hx.smooth _) h (hc i) (hp i),fun i=>hx.pos (f i)⟩
end
end YM.Frontier6.Bouquet.Audit
