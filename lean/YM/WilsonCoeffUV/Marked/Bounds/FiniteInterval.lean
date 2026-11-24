import YM.WilsonCoeffUV.Marked.Bounds.Penalty
/-!
# Transmission over finite close interval

Log costs cumulate *each* step, dominance includes this in geometric reserve.
Polynomial-log through Board at last. Revealed aperture at repeated width
(non-degrading).
 -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Mark
open Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Metric Shard Realm PathCost Real
open scoped Topology BigOperators
variable {c f:Side}{ι α U V t:Type}{J K I T:Finset ι}{D k K':ι→ℕ}{i j i' j' a e r h N n m b l:ℕ}{G:Gauge}{σ τ u g B C z ρ:ℝ}
variable [DecidableEq ι][Fintype ι]{E W U':Credit}{R:Realm G (e+1) E}{P:Outerm G D}{p:ι→Cover}
omit [DecidableEq ι] [Fintype ι] in
lemma shingled_sh (h:shingled p J P e σ B)(v:τ≤σ): shingled p J P e τ B:=fun _ i _=> (h _ i _).shave v
omit [DecidableEq ι] [Fintype ι] in
lemma shingled_pay (h:shingled p J P e σ B)(u:0≤ B)(v:B≤C): shingled p J P e σ C:=fun _ i _=> (h _ i _).more (pow_le_pow_left₀ u v _)
def Uniform (R:Realm G (e+1) E)(P:Outerm G D)(m:ℕ)(v:R.anchor ≤ m)(u:ℝ): Prop:=∀ p S, shingled p S P e (R.mint m v).σ u
lemma oneMarch (p:Cloze D k R U')(P:Outerm G D)(t:Wellness k P)(u:R.anchor≤ m)(h:m<N)(z:Uniform R P (m+1) (by omega) B)(q:0≤B): Uniform R (stout R.draws R.paid m N K' k P) m u (R.cash (tollStep G D k K' e U' E) m*B):=fun _ _=> shingled_sh (furnish p _ t u h _ _ q (fun _ S' _ a c r=> z _ S' a c r)) (pureEl (R.mint m u).gear).le

lemma nearFit (p:Cloze D k R U')(P:Outerm G D)(t:Wellness k P)(u:R.anchor≤ m)(h:m≤ b)(f:b≤ N)(q: Uniform R P b (by omega) B)(z':0≤B)(w:PadRank R m b z):
    let C:=tollStep G D k K' e U' E
    Uniform R (Gears R.draws R.paid K' k N b m P) m u (C.buy z ^(b-m)*B):=by
   let X:=tollStep G D k K' e U' E; revert q
   induction h using Nat.decreasingInduction with
   | self=> intro q X; rw [gearTop,Nat.sub_self,pow_zero,one_mul]; exact q
   | of_succ i g ih=>
       intro q; have ht:1≤z:=le_trans (R.depth _ u) (w.year _ le_rfl g.le); have hf:=zero_le_one.trans (X.purchase ht); have hK:= ih (by omega) (w.zone (by omega) le_rfl) q
       let K:= X.buy z ^(b-(i+1))*B; have hZ:0≤K:=by unfold K; positivity
       intro C p' S; rw [gearUp R.draws R.paid P g]; have hv:=X.elder (R.depth _ u) (w.year _ le_rfl g.le); apply shingled_pay (oneMarch p _ (Cog R.draws R.paid f P t R.hG R.green g) u (g.trans_le f) hK hZ _ S) (mul_nonneg (zero_le_one.trans (X.purchase (R.depth _ u))) hZ)
       unfold K at *; rw [show b-i=b-(i+1)+1 by omega, pow_succ',mul_assoc]; exact mul_le_mul_of_nonneg_right hv hZ

def wintry (G:Gauge)(D k K:ι→ℕ)(e:ℕ)(W B E F:Credit):= Credit.leanC.prodC (tollStep G D k K e B E) |>.plus W |>.prodC F
lemma nearExponential (p:Cloze D k R U')(P:Outerm G D)(t:Wellness k P)(u:R.anchor≤ m)(h:m≤ b)(f:b≤ N)(q:Uniform R P b (by omega) B)(g:PadRank R m b z)(v:B≤exp (W.buy z))(x:0≤ B):
   Uniform R (Gears R.draws R.paid K' k N b m P) m u (exp ((wintry G D k K' e W U' E Credit.unit).buy z)):=by
   let K:=tollStep G D k K' e U' E; have ht:1≤ z:= (R.depth _ u).trans (g.year _ le_rfl h); have hv:1≤ K.buy z:= K.purchase ht
   intro i S; refine shingled_pay (nearFit p P t u h f q x g i S) (mul_nonneg (pow_nonneg (zero_le_one.trans hv) _) x) ?_; let V:=K.buy z;
   have hh:V≤ exp V:=by linarith only [Real.add_one_le_exp V];
   change V^(b-m)*B≤_; refine le_trans (mul_le_mul (pow_le_pow_left₀ (zero_le_one.trans hv) hh _) v x (by positivity)) ?_ ; unfold wintry; rw [← Real.exp_nat_mul, ← Real.exp_add,Credit.products,Credit.unit_cost,mul_one]; apply Real.exp_le_exp.mpr; apply le_trans _ (Credit.fuel (Credit.leanC.prodC K) W ht); rw [Credit.products,Credit.lean_cost]; exact add_le_add_left (mul_le_mul_of_nonneg_right g.lengthS (zero_le_one.trans hv)) _
end YM.WilsonCoeffUV.Wheel.Mark
