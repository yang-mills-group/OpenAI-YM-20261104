import YM.Qlocal.Committed
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Binding
open Function Filter Lattice RG Wilson Tree Precision Input Gauge Finset MeasureTheory
open Push Push.Uniform SectorMeasure PhysicalNext Repeat Lapis
open ConnectedActivityE6 Blaze Brush Next.SectorChange Laurent Exterior Org
open Work.F03 Work.F05
open Marker Multi Comparison.RG02.Order
open AllOrder AllOrder.Floe Laplace Response Ink
open PertExtension.Series Radial PositionX.Jet PositionX.Gauss Extra.Iteration
open Comparison.RG02.Assembly Comparison.RG02.Bulk
open scoped BigOperators Topology ENNReal Classical InnerProductSpace MatrixOrder ContDiff Matrix.Norms.Frobenius
variable {G: Gauge} {c f n: Side} {S:StepData c f} {k t j:ℕ}
    {V:Type} [DecidableEq V] {B:Census V}
section seals
variable {X:Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
lemma ray_pow (u : Book X) (a k:ℕ) (x:X): Zone.TaylorPow u k a x= Response.energy u k a x:= by
 change _=PowerSeries.coeff a ((PowerSeries.mk fun i=>u i x)^k); induction k generalizing a with
 | zero=> simp only [Zone.TaylorPow, pow_zero, PowerSeries.coeff_one]
 | succ k ih=> unfold Zone.TaylorPow Zone.mul; rw [pow_succ, PowerSeries.coeff_mul]; simp only [PowerSeries.coeff_mk]; exact Finset.sum_congr rfl fun i hi=> by rw [ih]
lemma ray_exp (u : Book X) (he:u 0=0)(x:X) (k:ℕ): EXP u k x=Radial.expsum u k k x:= by
 rw [Expo he (le_refl k),Response.arrow, Finset.sum_apply, Finset.sum_apply]; unfold Radial.expsum; refine Finset.sum_congr rfl fun i _=>?_; rw [ray_pow]; rfl
-- bork.Summ.B.Space
variable [Fintype V]
omit [FiniteDimensional ℝ X] in
lemma ideal (u: ℕ→ℝ): bottom B k (series B k (realCurve B u))= series B k (realCurve B u):= by
 apply Join.both_parts; intro i j; rw [bottom_value]; split
 next he=>rw [he]
 next he=> rw [polarization,realCoeff,beads,if_neg he,mul_zero]
variable (e: Hot B→ X→ℂ)(h: Hot B→ℕ)(w:X→ℝ)(x:X)
include h e w
lemma original : denominator (series B k (expansions h e w x))= series B k (realCurve B fun n=> Radial.expsum (Radial.layers w) n n x):= by
 unfold denominator expansions; rw [map_mul,map_mul,mark_exp (mark_curve_quiet h e x),Poly.pass,map_sum]; rw [ideal]; -- prove bottom(exp)=1
 let u:=series B k (curve h e x); have hv : bottom B k u=0:= by
   unfold u; apply Join.both_parts; intro i j; rw [Poly.part_nil, bottom_value]; split
   next he=> rw [polarization,mark_curve_quiet,mul_zero]
   next he=> rfl
 dsimp only [u] at hv; simp_rw [_root_.map_smul, map_pow,hv]; rw [Finset.sum_range_succ']; simp only [Nat.factorial_zero,Nat.cast_one,inv_one,pow_zero,one_smul]; simp
lemma born (k:ℕ): rows (expansions h e w) B.quiet k x= Complex.ofReal (EXP (Radial.layers w) k x):= by
 let A:= series B k (expansions h e w x); have ht := original (k:=k) e h w x
 rw [rows,← observation B k _ (le_refl _),← show (observe B k (denominator A) k).part B.quiet=(observe B k (series B k (expansions h e w x)) k).part B.quiet from (by rw [denominator, observe_bottom, pure_marks,if_pos rfl])]; unfold A; rw [ht, observation _ _ _ (le_refl _),realCoeff,beads,if_pos rfl]; congr; rw [ray_exp (Radial.layers w) _ x k]; exact funext fun x=>Radial.Stationary.layers_zero x
end seals
end YM.Qlocal.Binding
