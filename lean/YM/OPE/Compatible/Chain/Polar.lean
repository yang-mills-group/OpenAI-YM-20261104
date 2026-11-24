import YM.OPE.Compatible.Chain.Berg
/-!
# inverse and permeated mass shifts. Uniform
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Terp
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Matrix Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Flume.Script Finset Metric
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent Further.FreeCovariance.KP GaussianScore Work.F06
local notation "M" => TypeFace 1
variable {C:KernelChoices}{r:ℕ}
def bough (P:Row M M)(u:ℝ)(p: Momentum):= spline P p + (↑u:ℂ) • 1
lemma added_major (P:Row M M)(u:ℝ)(h:Whole P)(n: Side): approached (major P n + u • 1)= spectral (fun p=> bough P u (mon p)):=by
    have hh: spectral (fun _:Site n=> (u:ℂ) • (1:Matrix M M ℂ))=(u:ℂ) • 1:=by
       apply cancel_rotation n; rw [spectral_read _]; have hx : (fiber (fun _:Site n=> (u:ℂ) • (1:Matrix M M ℂ)))= (u:ℂ) • 1 := by
            ext ⟨x,i⟩ ⟨y,j⟩; by_cases e:x=y <;> by_cases h:i=j<;> simp [fiber, Matrix.one_apply,e,h]
       rw [hx,Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_one,Matrix.one_mul]
    have hz: approached (major P n + u • 1)=approached (major P n) + (u:ℂ) • 1:=by
       ext i j; by_cases h:i=j <;>simp [h,approached]
    rw [hz, medic _ h,← hh,spectral_add]; rfl
lemma knot (C:KernelChoices) (h:4≤ r) : ∀ v:Train r,spline (ShellRow C v) 0=0:=by
    intro v; rw [spline_char v h 0]; unfold outside Exterior.q Exterior.wedge; simp; simp [Next.Free.physical]
lemma bough_bill (C:KernelChoices)(h:4≤r):∃ d:ℝ,0<d ∧∀ v:Train r,∀ n:Side,∀ u≥0,∀ p:Site n, ∀ x,(d*(win p)^2+u)*sqLength x≤ pairingRe (bough (ShellRow C v) u (mon p)) x x:=by
    obtain ⟨d,hd,H⟩:= profile C h; refine ⟨d,hd,fun v n u hu p x=>?_⟩; rw [bough,pairingRe_add, pairingRe_scale,price_unit, add_mul]; gcongr ?_+_; by_cases ht:p=0
    · subst p; rw [mon_zero,knot C h]; unfold win lit lift pairingRe; simp [rcast]; change d * ‖_ • (0:E4)‖^2* _ ≤ _; simp
    exact H _ _ _ ht _
abbrev under (P:Row M M)(u:ℝ)(p:Site n):= (bough P u (mon p))⁻¹
lemma pole_mass (v:Train r)(h:4≤r){u:ℝ}(hu:0<u)(n:Side): realOf (spectral (fun p:Site n=> under (ShellRow C v) u p))= (major (ShellRow C v) n + u • 1)⁻¹:=by
    symm; apply inv_eq_left_inv; rw [← realOf_mul', added_major _ _ (Op_whole h v), spectral_mul]; let f(p:Site n):=bough (ShellRow C v) u (mon p)
    have he(p:Site n): under (ShellRow C v) u p * f p=1:=by
        obtain ⟨d,hd,H⟩:= bough_bill C h; exact Matrix.nonsing_inv_mul _ (Value.det_unit (by positivity) (H v n u hu.le p))
    simp_rw [show ∀ p:Site n,under (ShellRow C v) u p * bough (ShellRow C v) u (mon p)=_ from he, spectral_unit]; ext i j; by_cases h:i=j <;> simp [h,realOf,Matrix.one_apply]
lemma plain_bill {a:ℝ}{v:Train r}(h:0≤ a){p:Site n}{d:ℝ}(hd:0<d)(hp:p≠0)(H:∀ x,(d*(win p)^2 + a)*sqLength x≤ pairingRe (bough (ShellRow C v) a (mon p)) x x)(i j:TypeFace 1): ‖under (ShellRow C v) a p i j‖ ≤ d⁻¹/(win p)^2:= by
    let f:=win p; have hx:0<f:=win_p _ hp; refine (entryC H (show 0<d*f^2+a by positivity) _ _).trans ?_; rw [show d⁻¹/f^2=(d*f^2)⁻¹ by ring] -- rw f/win
    apply inv_anti₀ (show 0<d*f^2 by positivity) (le_add_of_nonneg_right h)
end YM.OPE.Cascade.Terp
