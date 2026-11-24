import YM.MS.Alps.Easy
import YM.MS.Plum.Maggie
/-!
# Exponential-time translation algebra for self-scaling D amplitudes

Geometry `Forecast`: on actual kernel. expensive Φ scaling positive or negative; int exponent from
 engineering dimension exactly w as stated. Laurent α may complex. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Alps
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum
open Momentum Metric
open scoped Topology ContDiff
variable {G:Gauge}{I A B E P:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup P][NormedSpace ℝ P]
  {m n:ℕ}
def pulse (a:ℂ)(t:ℝ)(U:Rip G): Rip G := fun _ i j p=> amount (a - (wfield i:ℂ)-(wfield j:ℂ)) t * U _ i j (Real.exp t • p)
lemma amount_add (p q:ℂ)(t:ℝ): amount (p+q) t=amount p t*amount q t:= by unfold amount; rw [mul_add, Complex.exp_add]
lemma amount_time (t q:ℝ)(p:ℂ): amount p (t+q)= amount p t*amount p q:= by unfold amount; rw [Complex.ofReal_add,add_mul,Complex.exp_add]
lemma amount_mint (a:ℝ)(t:ℝ): amount (a:ℂ) t=Real.exp (a*t):= by unfold amount; simp [Complex.ofReal_exp,mul_comm a]
lemma amountD (x:ℂ)(t:ℝ): HasDerivAt (amount x) (x*amount x t) t:= by unfold amount; convert! (((hasDerivAt_id' t).ofReal_comp).mul_const x).cexp using 1; simp [mul_comm]
@[simp] lemma posing (a:ℂ)(F:Mob G): plow a 0 F=F:= by ext; simp [plow,amount,sr]
@[simp] lemma poking (a:ℂ)(U:Rip G): pulse a 0 U=U:= by ext; simp [pulse,amount]
variable {l: Legs (Mode (Cfield G m) P)}
omit [NormedAddCommGroup P][NormedSpace ℝ P] in lemma Price_append (i j: Legs (Mode (Cfield G m) P)): mass (i++j)=mass i + mass j:=by simp [mass, fieldDim] -- mass dependent on P but implementation `mass`? autoImplicit may insert section because fieldDim no instance
omit [NormedAddCommGroup P][NormedSpace ℝ P] in lemma Price_cons (i: Mode (Cfield G m) P)(l): mass (i::l)=wfield i.1+mass l:= field_cons _ i l
lemma price_sr (t:ℝ)(l: Legs (Mode (Cfield G m) P)): mass (sr t l)=mass l:=by induction l with| nil=> rfl| cons i l ih=> unfold sr at *; rw [List.map_cons,Price_cons, ih,Price_cons]
lemma lift_sr (t:ℝ)(h:m≤n)(l:Legs (Shore G m)): sr t (Arts.lift h l)=Arts.lift h (sr t l):= by induction l with| nil=> rfl| cons i l ih=> rw [Arts.lift,List.map_cons]; unfold sr at *; simp only [List.map_cons]; congr 1; exact Eq.symm (Prod.ext rfl (map_smul (Left h) _ _))
lemma mass_lift (h:m≤n)(l:Legs (Shore G m)): mass (Arts.lift h l)=mass l:= by induction l with| nil=>rfl| cons i l ih=> unfold Arts.lift at *; rw [List.map_cons,Price_cons,Price_cons,ih]; rfl
lemma inside (p q:ℝ)(l:Legs (Mode A P)): sr p (sr q l)=sr (p+q) l:= by simp only [sr,List.map_map]; congr! 1; funext i; exact Prod.ext rfl (show rexp p • rexp q • i.2 = rexp (p+q) • i.2 from by rw [smul_smul,Real.exp_add])
lemma snow (a:ℂ)(p q:ℝ)(F:Mob G): plow a p (plow a q F)= plow a (p+q) F:= by funext r l; unfold plow; rw [price_sr, inside, add_comm p q, amount_time]; ring
lemma fire (a:ℂ)(p q:ℝ)(U:Rip G): pulse a p (pulse a q U)=pulse a (p+q) U:= by funext n i j w; unfold pulse; rw [smul_smul,mul_comm (exp q),amount_time, Real.exp_add]; ring
end YM.MS.Alps
