import YM.OPE.Compatible.Arch.Poppy
/-!
# Position record at one space in one gauge slice.

Comparisons are only finite germ calculations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal Matrix.Norms.Frobenius
open PertExtension Series GaussianScore Asymptotics Precision
variable {I J:Type}{G:Gauge}[Fintype I][Fintype J]
open Radial Zone ScriptJ Metric
local notation "W" => Chart.tangent G I
local notation "Lf" => Tested.germ
variable {P:ChartRatio G} (R: LocalRatio P)
abbrev Cel (f:Keys G I→ℝ) :=∃ c>0,∀ x:Keys G I,c*‖x‖^2≤jet f 2 x
abbrev warmer (P: ChartRatio G)(f:Keys G I→ℝ):= f * fun y=>Chart.jacobian P y
structure Lid (G:Gauge)(I:Type)[Fintype I] where
   f : Keys G I→ℝ
   F : Stationary f
   fmeas : Measurable f
   bright:Cel f
   w : Keys G I→ℝ
   charm : 0< w 0
   coat: ContDiffAt ℝ ∞ w 0
   gleams : Measurable w
namespace Lid
variable (P:ChartRatio G)(L:Lid G I)
def heat := Pawn.mold (warmer P L.w) 0 * wheel (Pawn.mold L.f 2)
lemma winds (R:LocalRatio P): ContDiffAt ℝ ∞ (warmer P L.w) 0:= L.coat.mul ((Chart.Ratio.jacobian_smooth R).of_le le_top)
def purse :JetS ℝ:= gemLift W (kernel L.f) (L.heat P)
def capstone (p: ScriptJ (Keys G I)) : JetS ℝ:= gemLift W (kernel L.f) ((p*Pawn.mold (warmer P L.w) 0)*wheel (Pawn.mold L.f 2))
def pay (p:ScriptJ (Keys G I)): JetS ℝ:= L.capstone P p / L.purse P
def mode (t:ℝ)(x:Tile G I):=let y:=intake G I x; L.w y * Real.exp (-L.f y/t^2)
@[fun_prop] lemma meas (t:ℝ):Measurable (L.mode t):=by unfold mode; exact (L.gleams.comp introM).mul (Real.measurable_exp.comp ((L.fmeas.comp introM|>.neg).div_const _))
lemma foundation (R:LocalRatio P) : Snap L.mode (L.purse P):=by
     let A(x:ℝ)(y:Keys G I):= warmer P L.w (x • y); refine wind R L.F L.fmeas L.meas (Pawn.calm (L.winds P R)) (fun t=>?_) ?_ L.bright
     · exact ((L.gleams.mul (Chart.Ratio.jacobian_meas R)).comp (measurable_const_smul t)) -- find name
     filter_upwards [local_intro] with y hy x t ht e; unfold mode; rw [hy,e]; simp [warmer]; ring
lemma warmth (R:LocalRatio P) : 0<(L.purse P).s:=by
    obtain ⟨c,hc,H⟩:= L.bright
    have ht : 0< warmer P L.w (0:Keys G I) := mul_pos L.charm (by unfold Chart.jacobian; apply Finset.prod_pos; intro i _; rw [Chart.fee,Pi.zero_apply,R.anchored, mul_one]; exact lt_sup_of_lt_left R.scale)
    unfold purse gemLift heat; dsimp only [Pi.mul_apply]; change 0 < ∫ x,(jet (warmer P L.w) 0 x*1)*kernel L.f x ∂W
    have he: Integrable (kernel L.f) W:=by
       have hr:KernFit (kernel L.f) c:= fun x=>⟨Real.exp_nonneg _,Real.exp_le_exp.mpr (by nlinarith only [H x])⟩; have hV:Measurable (kernel L.f):= Real.measurable_exp.comp ((Radial.Smooth.continuousJet L.f 2).neg.measurable)
       simpa only [one_mul] using integ W hr hV hc Bond.one
    simp only [jet_zero,mul_one,integral_const_mul]; exact mul_pos ht (integral_exp_pos he)
-- generalized true partition probe with possible P captured via integrated tolerance. Here just one chamber
lemma reading (R:LocalRatio P){p:ScriptJ (Keys G I)}{A:ℝ→Keys G I→ℝ}{g:ℝ→Tile G I→ℝ}(h: Cape A p)(hp:∀ t,Measurable (A t))(hh:∀ t,Measurable (g t))
  (hx:∀ᶠ y:Keys G I in 𝓝 0,∀ x t,0<t→ t•x=y→ g t (put y)= A t x*(L.w y *Real.exp (-L.f y/t^2)) ): Snap g (L.capstone P p):=by
    let a(t:ℝ)(y:Keys G I):= warmer P L.w (t • y); let p':= Pawn.mold (warmer P L.w) 0
    refine wind R L.F L.fmeas hh (show Cape (A*a) (p*p') from by simpa only [one_mul] using! h.ascent (Pawn.calm (L.winds P R))) ?_ ?_ L.bright
    · intro t; exact (hp _).mul ((L.gleams.mul (Chart.Ratio.jacobian_meas R)).comp (measurable_const_smul t))
    filter_upwards [hx] with y hy x t ht he; rw [hy x t ht he]; simp only [Pi.mul_apply, a,he,warmer]; ring
lemma reaches1 (R:LocalRatio P){g:ℝ→Tile G I→ℝ}(h:∀ t,Measurable (g t))(hx:∀ᶠ y:Keys G I in 𝓝 0,∀ t,g t (put y)=L.w y*Real.exp (-L.f y/t^2)): Snap g (L.purse P):= by
      refine wind R L.F L.fmeas h (Pawn.calm (L.winds P R)) (fun t=>?_) ?_ L.bright
      · exact (L.gleams.mul (Chart.Ratio.jacobian_meas R)).comp (measurable_const_smul t)
      filter_upwards [hx] with y hx x t ht e; rw [hx,e]; unfold warmer; simp; ring
end Lid
end YM.OPE.Libra
