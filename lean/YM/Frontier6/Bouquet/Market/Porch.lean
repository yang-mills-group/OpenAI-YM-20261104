import YM.Frontier6.Bouquet.Market.Event

/-! Integrating descendant incomes over the independent margin (orthogonal
 normal Haar volumes). Let the radius scale be that of the retained parent
 annulus. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Atelier.Court
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains Prescription Metric Audit Submodule Fareway
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {I L Y:Type}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}{K:Final C F S}{P:Ensemble}{i:P}(Z:Court i)
variable [NormedAddCommGroup Y][NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y][CompleteSpace Y]
variable (R: Air (S:=S) P I L Y)
set_option quotPrecheck false
section
variable (X:Place)[FiniteDimensional ℝ X]
def cash (B:ℝ):ℝ:= (volume:Measure X).real (closedBall (0:X) 1)*B^(dim X)
lemma bankable {t B D:ℝ}(f:X→Y)(he:0<t)(h:0<B)(hv:0 ≤ D)(hp:∀ x:X, B*t<‖x‖→f x=0)(hx:∀ x:X, ‖f x‖ * t^dim X ≤ D): ‖∫ x,f x‖≤ cash X B*D:=by
    let M:=(volume:Measure X); letI:= FiniteDimensional.proper ℝ X; let V:= closedBall (0:X) (B*t); rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ:=M) (s:=V) (fun i hi=> hp i (by simpa [V] using hi))]; let T:= t^dim X; have ht:0 < T:= pow_pos he _;
    refine (norm_setIntegral_le_of_norm_le_const (μ:=M) (show M V<⊤ from (isCompact_closedBall ..).measure_lt_top) (fun x _=> (le_div_iff₀ ht).mpr (hx x))).trans_eq ?_; unfold cash; rw [Measure.addHaar_real_closedBall' M 0 (mul_pos h he|>.le)]; unfold M dim at *; rw [mul_pow]; field_simp; rfl
end
variable {d:Slot→ℕ}{f:Full (fiber P)}{t A a b B ε D C':ℝ}{j n:ℕ}{M:Pod→ℝ}{x:I}
variable (v:(i:Slot)→ S.Field (d i))(ht: Length P M t)(hh:R.suitable x C' t)(hf:Fellow P (R.lengths x) (R.region x) B f j A)(hc: Z.Contains (R.lengths x i) f)
    (hx:R.Welkin M)(hQ:Endows K d v Z.split M (Z.newWorld R) n B C' ε D)
include hf hx hc
lemma worthy (a t:ℝ): launch K d v (R.region x) (R.sky x) t a f=∫ z, offspring Z R K d v t a x f z:=by exact GlueComplies K _ (common a) Z.legend.le (fun y hy=> Z.separates (R.length_pos x i) (hc y hy)) hf.fair (hx.smooth x)
omit hc
lemma supports (a t:ℝ)(z:Margin P Z.split)(hz:B*R.lengths x i< ‖z‖): offspring Z R K d v t a x f z=0:= Z.uninhabited R v _ _ _ (Z.support_moves R hf _ _ hz)
include hc ht hh hQ
local notation "X"=> R.lengths x i
lemma portrait (ha:0<a)(hb:0<B){A':ℝ}(he: Checks (fiber P) (paths P (R.lengths x)) ((common a).film P Z.split f) n A'):
   ‖launch K d v (R.region x) (R.sky x) t a f‖ ≤ cash (Margin P Z.split) B*(D*A'*R.freight d x ε):= by rw [worthy Z R v hf hc hx a]; exact bankable _ _ (R.length_pos x i) hb (mul_nonneg (mul_nonneg hQ.pos he.nonneg) (R.freight_pos d hx x ε).le) (Z.supports R v hf hx _ _ ) (fun z=> Z.prize R v ht hh hf hc hx hQ z ha he)
lemma pair_cost (ha:0<a)(hb:a≤b)(he:4*b<Z.clearance*R.lengths x i)(hJ:n≤j)(hB:0<B): ‖launch K d v (R.region x) (R.sky x) t a f-launch K d v (R.region x) (R.sky x) t b f‖≤ cash (Margin P Z.split) B*(D*A*R.freight d x ε*R.delta x b):=by
   let F(u):= offspring Z R K d v t u x f; have hf'(u): Integrable (F u):= glued_apt K _ _ _ hf.fair (hx.smooth x); simp_rw [worthy Z R v hf hc hx]; rw [← integral_sub (hf' a) (hf' b)];
   refine bankable _ (fun i=>F a i-F b i) (R.length_pos x i) hB (mul_nonneg (mul_nonneg (mul_nonneg hQ.pos hf.costs.nonneg) (R.freight_pos d hx x ε).le) (R.delta_pos _ (lt_of_lt_of_le ha hb)).le) (fun z hz=> ?_) (fun z=> Z.precision R v ht hh hf hc hx hQ z ha hb he hJ)
   unfold F; rw [Z.supports R v hf hx _ _ z hz,Z.supports R v hf hx _ _ z hz,sub_self]
end YM.Frontier6.Bouquet.Atelier.Court
