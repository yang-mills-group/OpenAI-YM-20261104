import YM.OPE.Compatible.Nock.Columns
/-!
# Normalized charge on coordinate law (centered)
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Cascade
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency
open PertExtension Series Asymptotics GaussianScore Radial Finset Flock
variable {E F I:Type}
variable [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]
variable [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F][MeasurableSpace F][BorelSpace F]
def draw (p:E→Token)(A:Law E)(μ:Measure E):Token:= ⟨A.average μ (fun x=>(p x).s),A.average μ (fun x=>(p x).l), A.average μ (fun x=>(p x).h)⟩
omit [FiniteDimensional ℝ E] [BorelSpace E] in lemma drawScale (p:E→Token)(k:ℝ) (A:Law E)(μ:Measure E): draw (fun i=> JetS.plainJ k*p i) A μ=JetS.plainJ k*draw p A μ:= by
     have he(f:E→Token): draw (k • f) A μ=k • draw f A μ:= by apply JetS.eta; exact scooted μ A k _; exact scooted μ A k _; exact scooted μ A k _
     simp_rw [JetS.plain_full]; exact he _
lemma ease (p:E→ Token)(hp:ScriptJ.B p)(M:E≃ₗ[ℝ] F)(A:Law E)(L:Law F)(hh:∀ x,A.P x x=L.P (M x) (M x))(μ:Measure E)[μ.IsAddHaarMeasure](ν:Measure F)[ν.IsAddHaarMeasure] : draw p A μ=draw (fun v=>p (M.symm v)) L ν:=by
      have he(f:E→ℝ)(h:Bond f):A.average μ f=L.average ν (f ∘ M.symm):= meanFit ν μ _ _ M.symm.toLinearMap (dual_wick _ _ _ (fun x=>(hh (M.symm x)).trans (by simp) |>.symm)) f h
      apply JetS.eta; exact he _ (hp 0); exact he _ (hp 1); exact he _ (hp 2)
variable {G:Gauge} {I J:Type} [Fintype I]
namespace Lid
open JetS ScriptJ
variable (X:Lid G I)
local notation "W" => Chart.tangent G I
local notation "TK" => Keys G I
def seedPrice (P:ChartRatio G) :=warmer (I:=I) P X.w 0 -- args
lemma seed_pos {P:ChartRatio G}(R:LocalRatio P): 0<X.seedPrice P:=mul_pos X.charm (by unfold Chart.jacobian; apply Finset.prod_pos; intro i _; rw [Chart.fee,Pi.zero_apply,R.anchored, mul_one]; exact lt_sup_of_lt_left R.scale)
def hat (P:ChartRatio G)(x: TK): Token:= (plainJ (X.seedPrice P)⁻¹)* (X.heat P x) -- parentheses
lemma hat_full {P:ChartRatio G}(R:LocalRatio P)(x:TK):(X.hat P x).s=1:=by unfold hat heat; rw [ml_s,plain_s,Pi.mul_apply,ml_s]; change _*(jet _ 0 x*1)=1; rw [jet_zero,mul_one]; exact inv_mul_cancel₀ (X.seed_pos R).ne'
lemma hat_toll {P:ChartRatio G}(R:LocalRatio P) : ScriptJ.B (X.hat P):= height (p:= fun _=> plainJ (X.seedPrice P)⁻¹) (Xbond (Bond.keep _) Bond.zero Bond.zero) (ScriptJ.height ((Pawn.calm (X.winds _ R)).toll) (heightens _ (Pawn.trio X.F).toll))
-- explicit virtual pay menu
lemma cutOut {P:ChartRatio G}(R:LocalRatio P)(Q:Law TK)(p:ScriptJ TK)(ht:∀ x,jet X.f 2 x=Q.P x x/2): X.pay P p= draw (p*X.hat P) Q W / draw (X.hat P) Q W:=by
     have hx:kernel X.f=Q.kern:=by ext v; unfold kernel Law.kern; rw [ht]; congr 1; ring
     unfold pay purse capstone; let a:= (∫ x,Q.kern x ∂W); let b:= X.seedPrice P
     have ha : 0<a:= integral_exp_pos (by
           have hz:= lumpZ W Q 1 Bond.one; rw [one_mul] at hz; exact (show Integrable Q.kern W from hz))
     have hb: 0<b:= X.seed_pos R
     let T:= Pawn.mold (warmer P X.w) 0; let K:= wheel (Pawn.mold X.f 2); change gemLift W _ (p*T*K)/_= _; rw [hx,mul_assoc]; change gemLift W _ (p*X.heat P)/_= _; symm
     have ht (V: TK→Token): draw V Q W= plainJ (a⁻¹) * gemLift W Q.kern V:= by
        have h(f:TK→ℝ): Q.average W f=a⁻¹*(∫ x,f x*Q.kern x ∂W):=by unfold Law.average; rw [mul_comm a⁻¹,← div_eq_mul_inv];rfl
        rw [plain_full]; apply eta; exact h _; exact h _; exact h _
     let F:= plainJ (a⁻¹)*plainJ (b⁻¹)
     have hh (V:TK→Token): draw (fun i=> plainJ (b⁻¹)*V i) Q W= F*gemLift W Q.kern V:=by rw [drawScale,ht,mul_left_comm,←mul_assoc]
     rw [show p*X.hat P=fun i=> plainJ (b⁻¹)*(p*X.heat P) i from funext fun i=>by unfold hat; simp only [Pi.mul_apply]; exact mul_left_comm ..,show draw (X.hat P) _ _=_ from hh (X.heat P), hh]
     apply JetS.transfer; · rw [show F.s=_ from ml_s ..]; exact mul_ne_zero (inv_pos.mpr ha).ne' (inv_pos.mpr hb).ne'
     rw [← hx]; exact (X.warmth P R).ne'
end Lid
end YM.OPE.Libra
