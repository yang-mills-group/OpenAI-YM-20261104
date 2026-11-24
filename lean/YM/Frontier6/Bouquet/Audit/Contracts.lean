import YM.Frontier6.Bouquet.Audit.Airspace

/-! Policies for the approximations and estimates. Use small positive ε at each
 fixed valuation comparison.Cumulative.Effects explicit. (Account W positive,
 contraction loss common denominator cap.) -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Audit
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains Prescription Metric Fareway
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {Y I L G':Type}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S)(d:Slot→ℕ)(v:(i:Slot)→S.Field (d i))(s a:ℝ)(P:Ensemble)
variable [NormedAddCommGroup Y][NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y][CompleteSpace Y]

def uKernel (x:Seats P)(H:Patron S P Y)(f:Full (fiber P)) : Y:= regulator K (prepared K (common a) d v s) (common a) x H f
-- IMPORTANT re-using t^{N-d}; normal metric & unnormalized
abbrev difference (p:Pod)(d:Slot→ℕ):ℝ:= (dim (normal p):ℝ) - (p.arityD d:ℝ)
def stars (x:P→ℝ) : ℝ:= ∏ i:P, Real.rpow (x i) (difference i.val d)
-- rpow no notation issues
lemma stars_pos (x:P→ℝ)(he:∀ i,0<x i):0<stars d P x:=prod_pos fun i _=>Real.rpow_pos_of_pos (he i) _
-- first desired absolute.Error.Asym: eventually common on compact µ.First powers.
structure Endows (K:Final C F S)(d:Slot→ℕ)(v:(i:Slot)→S.Field (d i))(P:Ensemble)(M:Pod→ℝ)(X:Air (S:=S) P I L Y) (n:ℕ)(B C ε R:ℝ) : Prop where
  pos : 0 ≤ R
  body : ∀ (i:I)(A s a:ℝ)(f:Full (fiber P)),0<a→ Length P M s→ X.suitable i C s→ Fellow P (X.lengths i) (X.region i) B f n A→
    ‖uKernel K d v s a P (X.region i).center (X.sky i) f‖≤ R*A* X.account i * stars d P (X.lengths i) * X.route.ruin i ε
  both : ∀ (i:I)(A s a b:ℝ)(f:Full (fiber P)),0<a→ a≤b→ Length P M s→ X.suitable i C s→ Fellow P (X.lengths i) (X.region i) B f n A→
    ‖uKernel K d v s a P (X.region i).center (X.sky i) f-uKernel K d v s b P (X.region i).center (X.sky i) f‖≤ R*A*X.account i * stars d P (X.lengths i) * X.route.ruin i ε * (b/X.route.floor i)^(1/4:ℝ)

def Sails (n:ℕ) :Prop:=∀ {Y I L : Type}[NormedAddCommGroup Y][NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y][CompleteSpace Y]{M:Pod→ℝ}{X:Air (S:=S) P I L Y}, Dais K d P M → X.Welkin M→ Air.Hosts K X → ∀ (B C ε:ℝ),1≤B→1≤C→ 0<ε →∃ R:ℝ, Endows K d v P M X n B C ε R

section
variable {K d v P}{X:Air (S:=S) P I L Y}{B C' ε R:ℝ}{M:Pod→ℝ}{n m:ℕ} (h:Endows K d v P M X n B C' ε R)(he:n ≤ m)
include h he
lemma Endows.more : Endows K d v P M X m B C' ε R:=⟨h.pos,fun i A s a f hp hP hv hk=> h.body i _ _ _ _ hp hP hv (hk.below he le_rfl), fun i A s a b f hp hZ hP hv hk=> h.both i _ _ _ _ _ hp hZ hP hv (hk.below he le_rfl)⟩
end

end YM.Frontier6.Bouquet.Audit
