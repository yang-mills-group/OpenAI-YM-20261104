import YM.Frontier6.Bouquet.Market.Porch

/-! Uniform estimate per representable patch and derivative demand. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Atelier
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains Prescription Metric Audit Submodule Fareway
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {I L Y:Type}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}{K:Final C F S}{P:Ensemble}{i:P}
variable [NormedAddCommGroup Y][NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y][CompleteSpace Y]
variable {R: Air (S:=S) P I L Y}
namespace Court
variable (Z:Court i)
variable {d:Slot→ℕ}{f:Full (fiber P)}{t A a b B ε C' D:ℝ}{M:Pod→ℝ}{x:I}{n:ℕ}
lemma cash_pos (T:Place)[FiniteDimensional ℝ T](h:0 ≤ B):0 ≤ cash T B:= mul_nonneg ENNReal.toReal_nonneg (pow_nonneg h _)
variable (v:(i:Slot)→ S.Field (d i))(hx:R.Welkin M)(hQ:Endows K d v Z.split M (Z.newWorld R) n B C' ε D)
set_option quotPrecheck false
-- local notation "F"=> (fun a => launch K d v t a) -- wrong parameters don't use
-- court not necessarily at ann. use exact pure estimate on any patch meeting truth
structure Asks (Z:Court i)(u:ℝ)(K:Final C F S) -- local F overwrote binder
    (d:Slot→ℕ)(v:(i:Slot)→ S.Field (d i))(M:Pod→ℝ)(R: Air (S:=S) P I L Y)(n:ℕ) (B C' ε:ℝ):Prop where
  price : ∀ (x:I)(t A a:ℝ)(f:Full (fiber P)),Length P M t→0<a→ R.suitable x C' t→ Fellow P (R.lengths x) (R.region x) B f n A→ Z.Contains (R.lengths x i) f→ ‖launch K d v (R.region x) (R.sky x) t a f‖ ≤ u*A*R.freight d x ε
  many : ∀ (x:I)(t A a b:ℝ)(f:Full (fiber P)),Length P M t→0<a→ a≤b→ R.suitable x C' t→ Fellow P (R.lengths x) (R.region x) B f n A→ Z.Contains (R.lengths x i) f→ ‖launch K d v (R.region x) (R.sky x) t a f-launch K d v (R.region x) (R.sky x) t b f‖ ≤ u*A*R.freight d x ε*R.delta x b
include hx hQ
lemma earned (h:0<B) : ∃ u:ℝ,0 ≤ u∧ Z.Asks u K d v M R (n+n) B C' ε:=by
   let c:= cash (Margin P Z.split) B; have hc:0 ≤ c:= cash_pos _ h.le; obtain ⟨T,hT,H⟩:=global_cost Z n; let y:= c*D*T; have hY : 0 ≤ y:=mul_nonneg (mul_nonneg hc hQ.pos) hT; let k:= (Z.clearance/4)^(1/4:ℝ); have hk:0 < k:=Real.rpow_pos_of_pos (div_pos Z.pos (by norm_num)) _
   obtain ⟨u,hu,h2,h3⟩:∃ u:ℝ, y ≤ u∧ c*D≤u∧(y+y)/k≤u:=⟨max y (max (c*D) ((y+y)/k)),le_max_left ..,(le_max_left ..).trans (le_max_right ..),(le_max_right ..).trans (le_max_right ..)⟩
   have hF {x:I}{t a B':ℝ} (ht: Length P M t)(hr:0<a)(hy:R.suitable x C' t)(f:Full (fiber P))(hf:Fellow P (R.lengths x) (R.region x) B f (n+n) B')(hh: Z.Contains (R.lengths x i) f): ‖launch K d v (R.region x) (R.sky x) t a f‖≤y*B'*R.freight d x ε:=by refine (Z.portrait _ v ht hy hf hh hx hQ hr h (H (R.lengths x) (R.length_pos x i) a (B*R.lengths x i) _ hr f hh (hf.local_ i) hf.costs)).trans_eq ?_; unfold y c; ring -- syntax
   refine ⟨u,hY.trans hu, fun x t A a f ht hr hy hf hh=> (hF ht hr hy f hf hh).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hu hf.costs.nonneg) (R.freight_pos d hx x ε).le),fun x t A a b f ht hr hA hy hf hh=>?_⟩
   have hv:= hf.costs.nonneg; have hm:= R.freight_pos d hx x ε; have hk':= R.delta_pos x (lt_of_lt_of_le hr hA); by_cases he: 4*b < Z.clearance*R.lengths x i
   · apply (Z.pair_cost _ v ht hy hf hh hx hQ hr hA he (by omega) h).trans
     change c*_≤_; calc
       _ = c*D*A*(R.freight d x ε)*R.delta x b:=by ring
       _ ≤ _:= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hv) hm.le) hk'.le -- check
   let S:= A* R.freight d x ε; have hD:0 ≤ S:= mul_nonneg hv hm.le; let U:=R.delta x b; have hK':k ≤ U:=by
       apply Real.rpow_le_rpow (by linarith only [Z.pos] : 0 ≤ Z.clearance/4) _ (by norm_num); apply (le_div_iff₀ (R.route.footing x)).mpr; have hD:R.route.floor x ≤ R.lengths x i:=(R.route.covered _ _).1; linarith only [not_lt.mp he, mul_le_mul_of_nonneg_left hD Z.pos.le] -- need mul
   have hu': y+y ≤ u*R.delta x b:=(div_le_iff₀ hk).mp h3 |>.trans (mul_le_mul_of_nonneg_left hK' (hY.trans hu)); apply (norm_sub_le ..).trans; refine (add_le_add (hF ht hr hy f hf hh) (hF ht (lt_of_lt_of_le hr hA) hy f hf hh)).trans ?_; exact le_trans (b:=(y+y)*S) (le_of_eq (by unfold S; ring)) ((mul_le_mul_of_nonneg_right hu' hD).trans_eq (by unfold S; ring)) -- syntax
end Court
end YM.Frontier6.Bouquet.Atelier
