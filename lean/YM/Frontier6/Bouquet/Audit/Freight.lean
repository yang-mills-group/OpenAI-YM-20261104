import YM.Frontier6.Bouquet.Atlas.Thick

/-! Normalize rho economics. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Audit
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains Prescription Metric Fareway Submodule Atelier
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {I L Y:Type}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}{P:Ensemble}
variable [NormedAddCommGroup Y][NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y]
variable (R:Air (S:=S) P I L Y) (d:Slot→ℕ)
def Air.freight (x:I)(ε:ℝ):ℝ:= R.account x* stars d P (R.lengths x)*R.route.ruin x ε
def Air.delta (x:I)(u:ℝ):ℝ:=(u/R.route.floor x)^(1/4:ℝ)
lemma Air.freight_pos {M:Pod→ℝ}(h:R.Welkin M)(x:I)(ε:ℝ):0 < R.freight d x ε :=mul_pos (mul_pos (h.pos x) (stars_pos d P _ (R.length_pos x))) (Real.rpow_pos_of_pos (R.route.footing x) _)
lemma Air.freight_up {x:I}{ε δ:ℝ} (h:ε ≤ δ){M:Pod→ℝ}(he:R.Welkin M): R.freight d x ε≤ R.freight d x δ:=by
    unfold Air.freight Audit.Ribbon.ruin; exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge (R.route.footing _) (R.route.ground _|>.2) (neg_le_neg h)) ((mul_pos (he.pos _) (stars_pos d P _ (R.length_pos _))).le) -- syntax
lemma Air.delta_pos (x:I){u:ℝ}(he:0<u): 0<R.delta x u:= Real.rpow_pos_of_pos (div_pos he (R.route.footing _)) _
abbrev launch (K:Final C F S)(d:Slot→ℕ)(v:(i:Slot)→S.Field (d i))(X:Aura P)(H:Patron S P Y)(s a:ℝ)(f:Full (fiber P)):Y:= uKernel K d v s a P X.center H f
variable {K:Final C F S}{R d}{M:Pod→ℝ}{v:(i:Slot)→S.Field (d i)}{n:ℕ}{ε D B C':ℝ}
section
variable (h:Endows K d v P M R n B C' ε D){i:I}{t a b A:ℝ} {f:Full (fiber P)}
include h
lemma Endows.unit (ha:0<a)(ht:Length P M t)(hp:R.suitable i C' t)(hf:Fellow P (R.lengths i) (R.region i) B f n A): ‖launch K d v (R.region i) (R.sky i) t a f‖≤D*A*R.freight d i ε := by simp only [Air.freight,←mul_assoc]; exact h.body _ _ _ _ _ ha ht hp hf
lemma Endows.paired (ha:0<a)(hb:a≤b)(ht:Length P M t)(hp:R.suitable i C' t)(hf:Fellow P (R.lengths i) (R.region i) B f n A): ‖launch K d v (R.region i) (R.sky i) t a f-launch K d v (R.region i) (R.sky i) t b f‖≤D*A*R.freight d i ε*R.delta i b := by simp only [Air.freight,←mul_assoc]; exact h.both _ _ _ _ _ _ ha hb ht hp hf
end
-- cover passes
lemma passings {p:P} (Z:Court p)(x:I)(z:Margin P Z.split)(hz:Z.Love R x z)(ε:ℝ) : R.freight d x ε=(Z.newWorld R).freight d ⟨(x,z),hz⟩ ε*(R.lengths x p)^dim (Margin P Z.split):=by
   let X:= Z.newWorld R; let i': Z.Volunteers R:=⟨(x,z),hz⟩; change _= R.account x*(stars d Z.split (R.lengths x ∘ assign Z.legend.le))*R.route.ruin x ε * _; unfold Air.freight; rw [star_bills Z.legend d (R.lengths x) (R.length_pos x)]; ring
lemma passingsD {p:P} (Z:Court p)(x:Z.Volunteers R)(u:ℝ): R.delta x.val.fst u=(Z.newWorld R).delta x u:=rfl
end YM.Frontier6.Bouquet.Audit
